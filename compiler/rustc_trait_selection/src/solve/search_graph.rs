use std::collections::BTreeMap;
use std::iter;
use std::mem;
use std::ops::BitOrAssign;

use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::Idx;
use rustc_index::IndexVec;
use rustc_infer::infer::InferCtxt;
use rustc_middle::dep_graph::dep_kinds;
use rustc_middle::traits::solve::CacheData;
use rustc_middle::traits::solve::EvaluationCache;
use rustc_middle::ty::TyCtxt;
use rustc_next_trait_solver::solve::{CanonicalInput, Certainty, QueryResult};
use rustc_session::Limit;
use rustc_type_ir::inherent::*;
use rustc_type_ir::Interner;

use super::inspect;
use super::inspect::ProofTreeBuilder;
use super::SolverMode;
use crate::solve::FIXPOINT_STEP_LIMIT;

rustc_index::newtype_index! {
    #[orderable]
    pub struct StackDepth {}
}

/// How a goal has been used in a cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UsageKind {
    Coinductive,
    Inductive,
    Both,
}

impl UsageKind {
    fn contains(self, other: UsageKind) -> bool {
        match (self, other) {
            (UsageKind::Both, _)
            | (UsageKind::Coinductive, UsageKind::Coinductive)
            | (UsageKind::Inductive, UsageKind::Inductive) => true,
            (UsageKind::Inductive, UsageKind::Coinductive | UsageKind::Both)
            | (UsageKind::Coinductive, UsageKind::Inductive | UsageKind::Both) => false,
        }
    }
}

impl BitOrAssign for UsageKind {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = match (*self, rhs) {
            (UsageKind::Coinductive, UsageKind::Coinductive) => UsageKind::Coinductive,
            (UsageKind::Inductive, UsageKind::Inductive) => UsageKind::Inductive,
            (UsageKind::Both, _)
            | (_, UsageKind::Both)
            | (UsageKind::Inductive, UsageKind::Coinductive)
            | (UsageKind::Coinductive, UsageKind::Inductive) => UsageKind::Both,
        };
    }
}

#[derive(Debug, Default)]
struct CycleHeads {
    heads: BTreeMap<StackDepth, UsageKind>,
}

impl CycleHeads {
    fn new_head(depth: StackDepth, usage_kind: UsageKind) -> CycleHeads {
        CycleHeads { heads: iter::once((depth, usage_kind)).collect() }
    }

    fn add_dependency(&mut self, depth: StackDepth, usage_kind: UsageKind) {
        self.heads.entry(depth).and_modify(|usage| *usage |= usage_kind).or_insert(usage_kind);
    }

    fn iter(&self) -> impl Iterator<Item = (StackDepth, UsageKind)> + '_ {
        self.heads.iter().map(|(depth, usage_kind)| (*depth, *usage_kind))
    }

    fn highest_cycle_head(&self) -> Option<StackDepth> {
        self.heads.last_key_value().map(|(depth, _)| *depth)
    }

    fn lowest_cycle_head(&self) -> Option<StackDepth> {
        self.heads.first_key_value().map(|(depth, _)| *depth)
    }
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct StackEntry<I: Interner> {
    input: CanonicalInput<I>,

    available_depth: Limit,

    /// The maximum depth reached by this stack entry, only up-to date
    /// for the top of the stack and lazily updated for the rest.
    reached_depth: StackDepth,

    /// Whether this entry is a non-root cycle participant.
    ///
    /// We must not move the result of non-root cycle participants to the
    /// global cache. We store the highest stack depth of a head of a cycle
    /// this goal is involved in. This necessary to soundly cache its
    /// provisional result.
    heads: CycleHeads,

    encountered_overflow: bool,

    has_been_used: Option<UsageKind>,

    nested_goals: FxHashSet<CanonicalInput<I>>,
    /// Starts out as `None` and gets set when rerunning this
    /// goal in case we encounter a cycle.
    provisional_result: Option<QueryResult<I>>,
}

/// The provisional result for a goal which is not on the stack.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct DetachedEntry<I: Interner> {
    /// The head of the smallest non-trivial cycle involving this entry.
    ///
    /// Given the following rules, when proving `A` the head for
    /// the provisional entry of `C` would be `B`.
    /// ```plain
    /// A :- B
    /// B :- C
    /// C :- A + B + C
    /// ```
    heads: CycleHeads,
    nested_goals: FxHashSet<CanonicalInput<I>>,

    result: QueryResult<I>,
}

impl<I: Interner> DetachedEntry<I> {
    /// The highest cycle head this entry depends on.
    fn head(&self) -> StackDepth {
        self.heads.highest_cycle_head().unwrap()
    }
}

/// Stores the stack depth of a currently evaluated goal *and* already
/// computed results for goals which depend on other goals still on the stack.
///
/// The provisional result may depend on whether the stack above it is inductive
/// or coinductive. Because of this, we store separate provisional results for
/// each case. If an provisional entry is not applicable, it may be the case
/// that we already have provisional result while computing a goal. In this case
/// we prefer the provisional result to potentially avoid fixpoint iterations.
/// See tests/ui/traits/next-solver/cycles/mixed-cycles-2.rs for an example.
///
/// The provisional cache can theoretically result in changes to the observable behavior,
/// see tests/ui/traits/next-solver/cycles/provisional-cache-impacts-behavior.rs.
#[derive(derivative::Derivative)]
#[derivative(Default(bound = ""))]
struct ProvisionalCacheEntry<I: Interner> {
    stack_depth: Option<StackDepth>,
    with_inductive_stack: Option<DetachedEntry<I>>,
    with_coinductive_stack: Option<DetachedEntry<I>>,
}

impl<I: Interner> ProvisionalCacheEntry<I> {
    fn is_empty(&self) -> bool {
        self.stack_depth.is_none()
            && self.with_inductive_stack.is_none()
            && self.with_coinductive_stack.is_none()
    }
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
struct StashedDetachedEntry<I: Interner> {
    heads: Vec<(CanonicalInput<I>, UsageKind, QueryResult<I>)>,
    nested_goals: FxHashSet<CanonicalInput<I>>,

    is_coinductive: bool,
    input: CanonicalInput<I>,
    result: QueryResult<I>,
}

impl<'tcx> StashedDetachedEntry<TyCtxt<'tcx>> {
    fn is_applicable(
        &self,
        tcx: TyCtxt<'tcx>,
        stack: &IndexVec<StackDepth, StackEntry<TyCtxt<'tcx>>>,
        provisional_cache: &FxHashMap<
            CanonicalInput<TyCtxt<'tcx>>,
            ProvisionalCacheEntry<TyCtxt<'tcx>>,
        >,
    ) -> Option<CycleHeads> {
        // All stack entries used by this stashed entry still have the same
        // provisional result.
        let mut cycle_heads = CycleHeads::default();
        for &(input, usage_kind, expected) in self.heads.iter().rev() {
            let Some(depth) = provisional_cache.get(&input).and_then(|e| e.stack_depth) else {
                return None;
            };

            let actual = if let Some(result) = stack[depth].provisional_result {
                result
            } else {
                match usage_kind {
                    UsageKind::Coinductive => {
                        response_no_constraints(tcx, stack[depth].input, Certainty::Yes)
                    }
                    UsageKind::Inductive => {
                        response_no_constraints(tcx, stack[depth].input, Certainty::overflow(false))
                    }
                    UsageKind::Both => return None,
                }
            };

            if actual == expected {
                cycle_heads.add_dependency(depth, usage_kind)
            } else {
                return None;
            }
        }

        // This entry did not use any current stack entry as a nested goal.
        //
        // Given an original cycle of `A -> B -> C -> A, B`, the result for `B` in
        // `A -> C -> B` may be different and we must not use its provisional
        // result.
        #[allow(rustc::potential_query_instability)]
        if self
            .nested_goals
            .iter()
            .any(|input| provisional_cache.get(input).is_some_and(|e| e.stack_depth.is_some()))
        {
            return None;
        } else {
            Some(cycle_heads)
        }
    }
}

pub(super) struct SearchGraph<I: Interner> {
    mode: SolverMode,
    /// The stack of goals currently being computed.
    ///
    /// An element is *deeper* in the stack if its index is *lower*.
    stack: IndexVec<StackDepth, StackEntry<I>>,
    provisional_cache: FxHashMap<CanonicalInput<I>, ProvisionalCacheEntry<I>>,
    detached_entries_stash: FxHashMap<CanonicalInput<I>, Vec<StashedDetachedEntry<I>>>,
}

impl<I: Interner> SearchGraph<I> {
    pub(super) fn new(mode: SolverMode) -> SearchGraph<I> {
        Self {
            mode,
            stack: Default::default(),
            provisional_cache: Default::default(),
            detached_entries_stash: Default::default(),
        }
    }

    pub(super) fn solver_mode(&self) -> SolverMode {
        self.mode
    }

    /// Pops the highest goal from the stack, lazily updating the
    /// the next goal in the stack.
    ///
    /// Directly popping from the stack instead of using this method
    /// would cause us to not track overflow and recursion depth correctly.
    fn pop_stack(&mut self) -> StackEntry<I> {
        let elem = self.stack.pop().unwrap();
        if let Some(last) = self.stack.raw.last_mut() {
            last.reached_depth = last.reached_depth.max(elem.reached_depth);
            last.encountered_overflow |= elem.encountered_overflow;
        }
        elem
    }

    pub(super) fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    /// Returns the remaining depth allowed for nested goals.
    ///
    /// This is generally simply one less than the current depth.
    /// However, if we encountered overflow, we significantly reduce
    /// the remaining depth of all nested goals to prevent hangs
    /// in case there is exponential blowup.
    fn allowed_depth_for_nested(
        tcx: I,
        stack: &IndexVec<StackDepth, StackEntry<I>>,
    ) -> Option<Limit> {
        if let Some(last) = stack.raw.last() {
            if last.available_depth.0 == 0 {
                return None;
            }

            Some(if last.encountered_overflow {
                Limit(last.available_depth.0 / 4)
            } else {
                Limit(last.available_depth.0 - 1)
            })
        } else {
            Some(Limit(tcx.recursion_limit()))
        }
    }

    fn stack_coinductive_from(
        tcx: I,
        stack: &IndexVec<StackDepth, StackEntry<I>>,
        head: StackDepth,
    ) -> bool {
        stack.raw[head.index()..]
            .iter()
            .all(|entry| entry.input.value.goal.predicate.is_coinductive(tcx))
    }

    /// When encountering a solver cycle, the result of the current goal
    /// depends on goals lower on the stack.
    ///
    /// This is incredibly subtle, but for each stack entry, we have to track
    /// all goals lower on the stack on which this entry depends on. This impacts
    /// both whether this goal is moved to the global cache once we've finished
    /// computing it and to track when its applicable as a detached entry in the
    /// provisional cache.
    fn tag_cycle_participants(stack: &mut IndexVec<StackDepth, StackEntry<I>>, heads: &CycleHeads) {
        for (head, usage_kind) in heads.iter() {
            if let Some(prev) = &mut stack[head].has_been_used {
                *prev |= usage_kind;
            } else {
                stack[head].has_been_used = Some(usage_kind);
            };
        }

        // The current root of these cycles. Note that this may not be the final
        // root in case a later goal depends on a goal higher up the stack.
        let lowest_head = heads.lowest_cycle_head().unwrap();
        let mut current_root = lowest_head;
        while let Some(parent) = stack[current_root].heads.lowest_cycle_head() {
            current_root = parent;
        }

        for depth in current_root.index()..stack.len() {
            // Update all nested goals this goal depends on.
            let (stack, nested) = stack.raw.split_at_mut(depth + 1);
            let current = &mut stack[depth];
            for entry in nested {
                current.nested_goals.insert(entry.input);
                current.nested_goals.extend(&entry.nested_goals);
            }

            // Update all the cycle heads this goal depends on.
            for (head, usage_kind) in heads.iter().filter(|(h, _)| h.index() < depth) {
                current.heads.add_dependency(head, usage_kind);
            }
        }
    }
}

impl<'tcx> SearchGraph<TyCtxt<'tcx>> {
    /// The trait solver behavior is different for coherence
    /// so we use a separate cache. Alternatively we could use
    /// a single cache and share it between coherence and ordinary
    /// trait solving.
    pub(super) fn global_cache(&self, tcx: TyCtxt<'tcx>) -> &'tcx EvaluationCache<'tcx> {
        match self.mode {
            SolverMode::Normal => &tcx.new_solver_evaluation_cache,
            SolverMode::Coherence => &tcx.new_solver_coherence_evaluation_cache,
        }
    }

    fn insert_relevant_stashed_detached_entries(
        &mut self,
        tcx: TyCtxt<'tcx>,
        input: CanonicalInput<TyCtxt<'tcx>>,
    ) {
        let Some(stashed_entries) = self.detached_entries_stash.get_mut(&input) else { return };
        stashed_entries.retain_mut(|stashed_entry| {
            if let Some(heads) =
                stashed_entry.is_applicable(tcx, &self.stack, &self.provisional_cache)
            {
                debug_assert_eq!(heads.highest_cycle_head(), self.stack.last_index());
                let detached_entry = DetachedEntry {
                    heads,
                    nested_goals: mem::take(&mut stashed_entry.nested_goals),
                    result: stashed_entry.result,
                };

                if let Some(entry) = self.provisional_cache.get(&stashed_entry.input) {
                    if stashed_entry.is_coinductive {
                        if let Some(e) = &entry.with_coinductive_stack {
                            assert_eq!(e.head(), detached_entry.head());
                            assert_eq!(e.result, detached_entry.result);
                        }
                    } else {
                        if let Some(e) = &entry.with_inductive_stack {
                            assert_eq!(e.head(), detached_entry.head());
                            assert_eq!(e.result, detached_entry.result);
                        }
                    }
                };
                false
            } else {
                true
            }
        })
    }

    fn stash_dependent_provisional_results(
        &mut self,
        tcx: TyCtxt<'tcx>,
        stack_entry: &StackEntry<TyCtxt<'tcx>>,
    ) {
        let mut stash_provisional_entry = |input, entry: DetachedEntry<_>, is_coinductive| {
            let mut heads = Vec::new();
            for (head, usage_kind) in entry.heads.iter() {
                let elem = &self.stack.get(head).unwrap_or(stack_entry);
                let used_result = if let Some(result) = elem.provisional_result {
                    result
                } else {
                    match usage_kind {
                        UsageKind::Coinductive => {
                            response_no_constraints(tcx, elem.input, Certainty::Yes)
                        }
                        UsageKind::Inductive => {
                            response_no_constraints(tcx, elem.input, Certainty::overflow(false))
                        }
                        // just bail and ignore that result for now here, this should be unlikely
                        UsageKind::Both => return,
                    }
                };

                heads.push((elem.input, usage_kind, used_result));
            }

            self.detached_entries_stash.entry(stack_entry.input).or_default().push(
                StashedDetachedEntry {
                    heads,
                    nested_goals: entry.nested_goals,
                    is_coinductive,
                    input,
                    result: entry.result,
                },
            );
        };

        let head = self.stack.next_index();
        #[allow(rustc::potential_query_instability)]
        self.provisional_cache.retain(|input, entry| {
            if let Some(e) = entry.with_coinductive_stack.take_if(|p| p.head() == head) {
                stash_provisional_entry(*input, e, true);
            }
            if let Some(e) = entry.with_inductive_stack.take_if(|p| p.head() == head) {
                stash_provisional_entry(*input, e, false);
            }

            !entry.is_empty()
        });
    }

    pub(super) fn with_new_goal(
        &mut self,
        tcx: TyCtxt<'tcx>,
        input: CanonicalInput<TyCtxt<'tcx>>,
        inspect: &mut ProofTreeBuilder<InferCtxt<'tcx>>,
        prove_goal: impl FnMut(
            &mut Self,
            &mut ProofTreeBuilder<InferCtxt<'tcx>>,
        ) -> QueryResult<TyCtxt<'tcx>>,
    ) -> QueryResult<TyCtxt<'tcx>> {
        self.check_invariants();
        let result = self.with_new_goal_inner(tcx, input, inspect, prove_goal);
        self.check_invariants();
        result
    }

    /// Probably the most involved method of the whole solver.
    ///
    /// Given some goal which is proven via the `prove_goal` closure, this
    /// handles caching, overflow, and coinductive cycles.
    fn with_new_goal_inner(
        &mut self,
        tcx: TyCtxt<'tcx>,
        input: CanonicalInput<TyCtxt<'tcx>>,
        inspect: &mut ProofTreeBuilder<InferCtxt<'tcx>>,
        mut prove_goal: impl FnMut(
            &mut Self,
            &mut ProofTreeBuilder<InferCtxt<'tcx>>,
        ) -> QueryResult<TyCtxt<'tcx>>,
    ) -> QueryResult<TyCtxt<'tcx>> {
        // Check for overflow.
        let Some(available_depth) = Self::allowed_depth_for_nested(tcx, &self.stack) else {
            if let Some(last) = self.stack.raw.last_mut() {
                last.encountered_overflow = true;
            }

            inspect
                .canonical_goal_evaluation_kind(inspect::WipCanonicalGoalEvaluationKind::Overflow);
            return response_no_constraints(tcx, input, Certainty::overflow(true));
        };

        if let Some(result) = self.lookup_global_cache(tcx, input, available_depth, inspect) {
            debug!("global cache hit");
            return result;
        }

        // Check whether the goal is in the provisional cache.
        // The provisional result may rely on the path to its cycle roots,
        // so we have to check the path of the current goal matches that of
        // the cache entry.
        let cache_entry = self.provisional_cache.entry(input).or_default();
        if let Some(entry) = cache_entry
            .with_coinductive_stack
            .as_ref()
            .filter(|p| Self::stack_coinductive_from(tcx, &self.stack, p.head()))
            .or_else(|| {
                cache_entry
                    .with_inductive_stack
                    .as_ref()
                    .filter(|p| !Self::stack_coinductive_from(tcx, &self.stack, p.head()))
            })
        {
            debug!("provisional cache hit");
            // We have a nested goal which is already in the provisional cache, use
            // its result. We do not provide any usage kind as that should have been
            // already set correctly while computing the cache entry.
            inspect.canonical_goal_evaluation_kind(
                inspect::WipCanonicalGoalEvaluationKind::ProvisionalCacheHit,
            );
            Self::tag_cycle_participants(&mut self.stack, &entry.heads);
            return entry.result;
        } else if let Some(stack_depth) = cache_entry.stack_depth {
            debug!("encountered cycle with depth {stack_depth:?}");
            // We have a nested goal which directly relies on a goal deeper in the stack.
            //
            // We start by tagging all cycle participants, as that's necessary for caching.
            //
            // Finally we can return either the provisional response or the initial response
            // in case we're in the first fixpoint iteration for this goal.
            inspect.canonical_goal_evaluation_kind(
                inspect::WipCanonicalGoalEvaluationKind::CycleInStack,
            );
            let is_coinductive_cycle = Self::stack_coinductive_from(tcx, &self.stack, stack_depth);
            let usage_kind =
                if is_coinductive_cycle { UsageKind::Coinductive } else { UsageKind::Inductive };
            let heads = CycleHeads::new_head(stack_depth, usage_kind);
            Self::tag_cycle_participants(&mut self.stack, &heads);

            // Return the provisional result or, if we're in the first iteration,
            // start with no constraints.
            return if let Some(result) = self.stack[stack_depth].provisional_result {
                result
            } else if is_coinductive_cycle {
                response_no_constraints(tcx, input, Certainty::Yes)
            } else {
                response_no_constraints(tcx, input, Certainty::overflow(false))
            };
        } else {
            // No entry, we push this goal on the stack and try to prove it.
            let depth = self.stack.next_index();
            let entry = StackEntry {
                input,
                available_depth,
                reached_depth: depth,
                heads: Default::default(),
                encountered_overflow: false,
                has_been_used: None,
                nested_goals: Default::default(),
                provisional_result: None,
            };
            assert_eq!(self.stack.push(entry), depth);
            cache_entry.stack_depth = Some(depth);
        }

        // This is for global caching, so we properly track query dependencies.
        // Everything that affects the `result` should be performed within this
        // `with_anon_task` closure. If computing this goal depends on something
        // not tracked by the cache key and from outside of this anon task, it
        // must not be added to the global cache. Notably, this is the case for
        // trait solver cycles participants.
        let ((final_entry, result), dep_node) =
            tcx.dep_graph.with_anon_task(tcx, dep_kinds::TraitSelect, || {
                for _ in 0..FIXPOINT_STEP_LIMIT {
                    match self.fixpoint_step_in_task(tcx, input, inspect, &mut prove_goal) {
                        StepResult::Done(final_entry, result) => return (final_entry, result),
                        StepResult::HasChanged => debug!("fixpoint changed provisional results"),
                    }
                }

                debug!("canonical cycle overflow");
                let current_entry = self.pop_stack();
                debug_assert!(current_entry.has_been_used.is_none());
                let result = response_no_constraints(tcx, input, Certainty::overflow(false));
                (current_entry, result)
            });

        let proof_tree = inspect.finalize_canonical_goal_evaluation(tcx);

        let depth = self.stack.next_index();
        if let Some(head) = final_entry.heads.highest_cycle_head() {
            debug_assert!(head < depth);
            debug_assert!(self.stack[head].has_been_used.is_some());
            let heads = final_entry.heads;
            let nested_goals = final_entry.nested_goals;
            let coinductive_stack = Self::stack_coinductive_from(tcx, &self.stack, head);
            let entry = self.provisional_cache.get_mut(&input).unwrap();
            assert_eq!(entry.stack_depth.take(), Some(depth));
            if coinductive_stack {
                entry.with_coinductive_stack = Some(DetachedEntry { heads, nested_goals, result });
            } else {
                entry.with_inductive_stack = Some(DetachedEntry { heads, nested_goals, result });
            }
        } else {
            // When encountering a cycle, both inductive and coinductive, we only
            // move the root into the global cache. We also store all other cycle
            // participants involved.
            //
            // We must not use the global cache entry of a root goal if a cycle
            // participant is on the stack. This is necessary to prevent unstable
            // results. See the comment of `StackEntry::nested_goals` for
            // more details.
            let provisional_cache_entry = self.provisional_cache.remove(&input);
            debug_assert_eq!(provisional_cache_entry.unwrap().stack_depth, Some(depth));
            // TODO clear fixpoint instantiation cache.
            let reached_depth = final_entry.reached_depth.as_usize() - self.stack.len();
            self.global_cache(tcx).insert(
                tcx,
                input,
                proof_tree,
                reached_depth,
                final_entry.encountered_overflow,
                final_entry.nested_goals,
                dep_node,
                result,
            )
        }

        result
    }

    /// Try to fetch a previously computed result from the global cache,
    /// making sure to only do so if it would match the result of reevaluating
    /// this goal.
    fn lookup_global_cache(
        &mut self,
        tcx: TyCtxt<'tcx>,
        input: CanonicalInput<TyCtxt<'tcx>>,
        available_depth: Limit,
        inspect: &mut ProofTreeBuilder<InferCtxt<'tcx>>,
    ) -> Option<QueryResult<TyCtxt<'tcx>>> {
        let CacheData { result, proof_tree, additional_depth, encountered_overflow } = self
            .global_cache(tcx)
            .get(tcx, input, self.stack.iter().map(|e| e.input), available_depth)?;

        // If we're building a proof tree and the current cache entry does not
        // contain a proof tree, we do not use the entry but instead recompute
        // the goal. We simply overwrite the existing entry once we're done,
        // caching the proof tree.
        if !inspect.is_noop() {
            if let Some(final_revision) = proof_tree {
                let kind = inspect::WipCanonicalGoalEvaluationKind::Interned { final_revision };
                inspect.canonical_goal_evaluation_kind(kind);
            } else {
                return None;
            }
        }

        // Update the reached depth of the current goal to make sure
        // its state is the same regardless of whether we've used the
        // global cache or not.
        let reached_depth = self.stack.next_index().plus(additional_depth);
        if let Some(last) = self.stack.raw.last_mut() {
            last.reached_depth = last.reached_depth.max(reached_depth);
            last.encountered_overflow |= encountered_overflow;
        }

        Some(result)
    }
}

enum StepResult<I: Interner> {
    Done(StackEntry<I>, QueryResult<I>),
    HasChanged,
}

impl<'tcx> SearchGraph<TyCtxt<'tcx>> {
    /// When we encounter a coinductive cycle, we have to fetch the
    /// result of that cycle while we are still computing it. Because
    /// of this we continuously recompute the cycle until the result
    /// of the previous iteration is equal to the final result, at which
    /// point we are done.
    fn fixpoint_step_in_task<F>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        input: CanonicalInput<TyCtxt<'tcx>>,
        inspect: &mut ProofTreeBuilder<InferCtxt<'tcx>>,
        prove_goal: &mut F,
    ) -> StepResult<TyCtxt<'tcx>>
    where
        F: FnMut(&mut Self, &mut ProofTreeBuilder<InferCtxt<'tcx>>) -> QueryResult<TyCtxt<'tcx>>,
    {
        self.check_invariants();
        // Insert all relevant stashed detached entries for the given
        // provisional result.
        self.insert_relevant_stashed_detached_entries(tcx, input);

        let result = prove_goal(self, inspect);
        let stack_entry = self.pop_stack();
        debug_assert_eq!(stack_entry.input, input);

        // Start by clearing all provisional cache entries which depend on this
        // the current goal.
        //
        // Note that such entries can exist even if the current goal is unused in
        // this iteration. E.g. given the following setup.
        //
        // A :- B
        // B :- A, C
        // C :- B
        //
        // If `A` ends up returning `NoSolution` in the second fixpoint iteration, we
        // can reuse the provisional cache entry for `C` in `B`, as it does not depend
        // on `A`, but we never try using it as we eagerly stop proving `B` once `A`
        // does not hold.
        self.stash_dependent_provisional_results(tcx, &stack_entry);

        // If the current goal is not the root of a cycle, we are done.
        let Some(usage_kind) = stack_entry.has_been_used else {
            return StepResult::Done(stack_entry, result);
        };

        // If it is a cycle head, we have to keep trying to prove it until
        // we reach a fixpoint. We need to do so for all cycle heads,
        // not only for the root.
        //
        // See tests/ui/traits/next-solver/cycles/fixpoint-rerun-all-cycle-heads.rs
        // for an example.

        // Check whether we reached a fixpoint, either because the final result
        // is equal to the provisional result of the previous iteration, or because
        // this was only the root of either coinductive or inductive cycles, and the
        // final result is equal to the initial response for that case.
        let reached_fixpoint = if let Some(r) = stack_entry.provisional_result {
            eprintln!("existing {}: {r:?} == {result:?}", r == result);
            r == result
        } else {
            match usage_kind {
                UsageKind::Coinductive => {
                    let r = response_no_constraints(tcx, input, Certainty::Yes);
                    eprintln!("coinductive {}: {r:?} == {result:?}", r == result);
                    r == result
                }
                UsageKind::Inductive => {
                    let r = response_no_constraints(tcx, input, Certainty::overflow(false));
                    eprintln!("inductive {}: {r:?} == {result:?}", r == result);
                    r == result
                }
                UsageKind::Both => {
                    eprintln!("both fail");
                    false
                }
            }
        };

        // If we did not reach a fixpoint, update the provisional result and reevaluate.
        if reached_fixpoint {
            StepResult::Done(stack_entry, result)
        } else {
            let depth = self.stack.push(StackEntry {
                has_been_used: None,
                provisional_result: Some(result),
                ..stack_entry
            });
            debug_assert_eq!(self.provisional_cache[&input].stack_depth, Some(depth));
            StepResult::HasChanged
        }
    }
}

fn response_no_constraints<'tcx>(
    tcx: TyCtxt<'tcx>,
    goal: CanonicalInput<TyCtxt<'tcx>>,
    certainty: Certainty,
) -> QueryResult<TyCtxt<'tcx>> {
    Ok(super::response_no_constraints_raw(tcx, goal.max_universe, goal.variables, certainty))
}

impl<I: Interner> SearchGraph<I> {
    #[allow(rustc::potential_query_instability)]
    fn check_invariants(&self) {
        if !cfg!(debug_assertions) {
            return;
        }

        let SearchGraph { mode: _, stack, provisional_cache, detached_entries_stash } = self;
        if stack.is_empty() {
            assert!(provisional_cache.is_empty());
        }

        for (depth, entry) in stack.iter_enumerated() {
            let StackEntry {
                input,
                available_depth: _,
                reached_depth: _,
                ref heads,
                encountered_overflow: _,
                has_been_used: _,
                ref nested_goals,
                provisional_result: _,
            } = *entry;
            let cache_entry = provisional_cache.get(&entry.input).unwrap();
            assert_eq!(cache_entry.stack_depth, Some(depth));

            for (head, usage_kind) in heads.iter() {
                assert!(head < depth);
                assert!(stack[head].has_been_used.unwrap().contains(usage_kind));
            }

            if let Some(lowest_head) = heads.lowest_cycle_head() {
                let mut current_root = lowest_head;
                while let Some(parent) = stack[current_root].heads.lowest_cycle_head() {
                    current_root = parent;
                }

                for entry in &stack.raw[current_root.index()..depth.index()] {
                    assert!(entry.nested_goals.contains(&input));
                }
            }

            if !nested_goals.is_empty() {
                for entry in stack.iter().take(depth.as_usize()) {
                    assert_eq!(nested_goals.get(&entry.input), None);
                }
            }
        }

        for (&input, entry) in &self.provisional_cache {
            let ProvisionalCacheEntry { stack_depth, with_coinductive_stack, with_inductive_stack } =
                entry;
            assert!(
                stack_depth.is_some()
                    || with_coinductive_stack.is_some()
                    || with_inductive_stack.is_some()
            );

            if let &Some(stack_depth) = stack_depth {
                assert_eq!(stack[stack_depth].input, input);
            }
        }

        for (&input, entries) in detached_entries_stash {
            for comb in entries.iter().combinations(2) {
                assert_ne!(comb[0], comb[1]);
            }

            for entry in entries {
                let StashedDetachedEntry {
                    heads,
                    nested_goals: _,
                    is_coinductive: _,
                    input: _,
                    result: _,
                } = entry;
                assert_eq!(input, heads.last().unwrap().0);
            }
        }
    }
}
