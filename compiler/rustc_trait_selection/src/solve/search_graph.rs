use std::mem;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::Idx;
use rustc_index::IndexVec;
use rustc_middle::bug;
use rustc_middle::dep_graph::dep_kinds;
use rustc_middle::traits::solve::CacheData;
use rustc_middle::traits::solve::EvaluationCache;
use rustc_middle::ty::TyCtxt;
use rustc_next_trait_solver::solve::{CanonicalInput, Certainty, QueryResult};
use rustc_session::Limit;
use rustc_type_ir::inherent::*;
use rustc_type_ir::Interner;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::iter;

use super::inspect;
use super::inspect::ProofTreeBuilder;
use super::SolverMode;
use crate::solve::FIXPOINT_STEP_LIMIT;

rustc_index::newtype_index! {
    #[orderable]
    pub struct StackDepth {}
}

bitflags::bitflags! {
    /// Whether and how this goal has been used as the root of a
    /// cycle. We track the kind of cycle as we're otherwise forced
    /// to always rerun at least once.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct HasBeenUsed: u8 {
        const INDUCTIVE_CYCLE = 1 << 0;
        const COINDUCTIVE_CYCLE = 1 << 1;
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

    /// If this entry is a non-root cycle participant, we store the depth of
    /// all cycle participants and how that participant has been used. We only
    /// need to track the `root` for t
    ///
    /// We must not move the result of non-root cycle participants to the
    /// global cache. The goal itself only really needs the highest stack depth
    /// of a head of a cycle this goal is involved in. However, the
    /// `fixpoint_instantiation_cache` needs to know about all used heads
    /// to reuse detached entries.
    heads: BTreeMap<StackDepth, HasBeenUsed>,

    encountered_overflow: bool,

    has_been_used: HasBeenUsed,

    /// We put only the root goal of a coinductive cycle into the global cache.
    ///
    /// If we were to use that result when later trying to prove another cycle
    /// participant, we can end up with unstable query results.
    ///
    /// See tests/ui/next-solver/coinduction/incompleteness-unstable-result.rs for
    /// an example of where this is needed.
    ///
    /// There can  be multiple roots on the same stack, so we need to track
    /// cycle participants per root:
    /// ```plain
    /// A :- B
    /// B :- A, C
    /// C :- D
    /// D :- C
    /// ```
    cycle_participants: FxHashSet<CanonicalInput<I>>,
    /// Starts out as `None` and gets set when rerunning this
    /// goal in case we encounter a cycle.
    provisional_result: Option<QueryResult<I>>,
}

/// The provisional result for a goal which is not on the stack.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct DetachedEntry<I: Interner> {
    /// The heads of all cycles used by this entry itself or
    /// any other detached entries this entry depends on.
    ///
    /// Given the following rules, when proving `A` the heads for
    /// the provisional entry of `C` would be `[A, B]`.
    /// ```plain
    /// A :- B
    /// B :- C
    /// C :- A + B + C
    /// ```
    /// After computing `C`, we put it into the cache as a detached
    /// entry. Once we pop `B` from the stack we move the entry for
    /// `C` into the `FixpointInstantationCacheEntry` of `B` to
    /// potentially reuse it in the next fixpoint iteration as long
    /// as the provisional results of *all* heads are still equal. The
    /// entry is outdated if the provisional result of any of the heads
    /// has changed.
    ///
    /// The usage kind is used by the `fixpoint_instantiation_cache` to
    /// make sure the used provisional results haven't changed.
    heads: BTreeMap<StackDepth, HasBeenUsed>,
    result: QueryResult<I>,
}

impl<I: Interner> DetachedEntry<I> {
    /// The highest cycle head this entry depends on.
    fn head(&self) -> StackDepth {
        *self.heads.last_key_value().unwrap().0
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

/// A `DetachedEntry` stored for a future fixpoint iteration if the
/// provisional results in case the provisional result of all its
/// cycle heads has not changed.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct StashedDetachedEntry<I: Interner> {
    /// The cycle heads this detached entries depends on and how
    /// they have been used.
    heads: BTreeMap<StackDepth, HasBeenUsed>,
    /// The provisional results of all cycle heads used when
    /// computing this goal. This entry can only be reused if
    /// they haven't changed.
    provisional_results: Vec<QueryResult<I>>,
    /// Whether the path from the highested cycle head to this
    /// goal was coinductive. Used to actual populate the
    /// provisional cache.
    is_coinductive: bool,

    result: QueryResult<I>,
}

impl<'tcx> StashedDetachedEntry<TyCtxt<'tcx>> {
    /// Whether this entry can be reused as its dependencies haven't
    /// changed.
    fn is_applicable(
        &self,
        tcx: TyCtxt<'tcx>,
        stack: &IndexVec<StackDepth, StackEntry<TyCtxt<'tcx>>>,
    ) -> bool {
        itertools::zip_eq(&self.heads, &self.provisional_results).all(|x| {
            let ((&stack_depth, &usage_kind), &result) = x;
            let actual = if let Some(result) = stack[stack_depth].provisional_result {
                result
            } else if usage_kind == HasBeenUsed::COINDUCTIVE_CYCLE {
                response_no_constraints(tcx, stack[stack_depth].input, Certainty::Yes)
            } else if usage_kind == HasBeenUsed::INDUCTIVE_CYCLE {
                response_no_constraints(tcx, stack[stack_depth].input, Certainty::overflow(false))
            } else {
                unreachable!(); // for now
            };

            actual == result
        })
    }
}

/// When rerunning a goal as we haven't yet reached a fixpoint,
/// try to reuse as much from the previous iteration as possible to
/// avoid exponential blowup.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct FixpointInstantiationCacheEntry<I: Interner> {
    /// The stack when computing this goal. We need to make sure
    /// the provisional result is actually a subset of the final result.
    /// As computing this goal depends on its stack, we therefore only
    /// reuse its provisional result if the stack is the same.
    expected_stack: IndexVec<StackDepth, CanonicalInput<I>>,
    /// All cycle heads this provisional result depends on. While the
    /// provisional can be reused if the provisional result of them changed,
    /// the final value of this goal still depends on these stack entries.
    heads: BTreeMap<StackDepth, HasBeenUsed>,
    /// The final provisional result when we previously evaluated this
    /// goal to a fixpoint. By using this as the initial provisional result
    /// in any following iteration we can avoid rerunning this goal in
    /// future iterations.
    provisional_result: QueryResult<I>,
    /// All detached entries for which this goal is the highest cycle head
    /// they depend on. They can be reused if the provisional result of all
    /// their dependencies haven't changed since then.
    detached_entries: FxHashMap<CanonicalInput<I>, StashedDetachedEntry<I>>,
}

impl<'tcx> FixpointInstantiationCacheEntry<TyCtxt<'tcx>> {
    /// When reusing a provisional result we have to make sure the
    /// result is actually applicable for the given goal. We check this
    /// by only adding a provisional result if the stack matches the
    /// previous iteration.
    fn is_applicable(&self, stack: &IndexVec<StackDepth, StackEntry<TyCtxt<'tcx>>>) -> bool {
        self.expected_stack.len() == stack.len()
            && itertools::zip_eq(&self.expected_stack, stack.iter().map(|e| &e.input))
                .all(|(l, r)| l == r)
    }
}

pub(super) struct SearchGraph<I: Interner> {
    mode: SolverMode,
    /// The stack of goals currently being computed.
    ///
    /// An element is *deeper* in the stack if its index is *lower*.
    stack: IndexVec<StackDepth, StackEntry<I>>,

    /// A lookup table for both goals currently on the stack and the
    /// result of finished goals whose result depends on goals on
    /// the stack.
    provisional_cache: FxHashMap<CanonicalInput<I>, ProvisionalCacheEntry<I>>,

    /// The provisional results for all nested cycle participants we've already computed.
    /// The next time we evaluate these nested goals we use that result in the first
    /// iteration. This also contains the detached cache entries we may reuse.
    fixpoint_instantiation_cache:
        FxHashMap<CanonicalInput<I>, Vec<FixpointInstantiationCacheEntry<I>>>,
}

impl<I: Interner> SearchGraph<I> {
    pub(super) fn new(mode: SolverMode) -> SearchGraph<I> {
        SearchGraph {
            mode,
            stack: Default::default(),
            provisional_cache: Default::default(),
            fixpoint_instantiation_cache: Default::default(),
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
    fn tag_cycle_participants(
        stack: &mut IndexVec<StackDepth, StackEntry<I>>,
        heads: &BTreeMap<StackDepth, HasBeenUsed>,
    ) {
        for (&head, &usage_kind) in heads {
            stack[head].has_been_used |= usage_kind;
            debug_assert!(!stack[head].has_been_used.is_empty());
        }

        // The current root of these cycles. Note that this may not be the final
        // root in case a later goal depends on a goal higher up the stack.
        let lowest_head = *heads.first_key_value().unwrap().0;
        let mut current_root = lowest_head;
        while let Some((&parent, _)) = stack[current_root].heads.first_key_value() {
            current_root = parent;
        }

        // Make sure to track all cycle participants for the current root and
        // track the dependencies of every goal involved in this cycle.
        let participants_start = lowest_head.index() + 1;
        let (stack, cycle_participants) = stack.raw.split_at_mut(participants_start);
        let current_cycle_root = &mut stack[current_root.as_usize()];
        for (entry_depth, entry) in iter::zip(participants_start.., cycle_participants) {
            let entry_depth = StackDepth::from(entry_depth);
            current_cycle_root.cycle_participants.insert(entry.input);
            current_cycle_root.cycle_participants.extend(mem::take(&mut entry.cycle_participants));

            for (&head, &usage_kind) in heads.iter().filter(|(&h, _)| h < entry_depth) {
                entry
                    .heads
                    .entry(head)
                    .and_modify(|usage| *usage |= usage_kind)
                    .or_insert(usage_kind);
            }
        }
    }

    fn clear_dependent_provisional_results(
        provisional_cache: &mut FxHashMap<CanonicalInput<I>, ProvisionalCacheEntry<I>>,
        head: StackDepth,
        mut f: impl FnMut(CanonicalInput<I>, Option<DetachedEntry<I>>, Option<DetachedEntry<I>>),
    ) {
        let condition = |p: &mut DetachedEntry<I>| match p.head().cmp(&head) {
            Ordering::Less => false,
            Ordering::Equal => true,
            Ordering::Greater => bug!("provisional entry for popped value"),
        };

        #[allow(rustc::potential_query_instability)]
        provisional_cache.retain(|input, entry| {
            let coinductive = entry.with_coinductive_stack.take_if(condition);
            let inductive = entry.with_inductive_stack.take_if(condition);
            f(*input, coinductive, inductive);
            !entry.is_empty()
        });
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

    /// Probably the most involved method of the whole solver.
    ///
    /// Given some goal which is proven via the `prove_goal` closure, this
    /// handles caching, overflow, and coinductive cycles.
    pub(super) fn with_new_goal(
        &mut self,
        tcx: TyCtxt<'tcx>,
        input: CanonicalInput<TyCtxt<'tcx>>,
        inspect: &mut ProofTreeBuilder<TyCtxt<'tcx>>,
        mut prove_goal: impl FnMut(
            &mut Self,
            &mut ProofTreeBuilder<TyCtxt<'tcx>>,
        ) -> QueryResult<TyCtxt<'tcx>>,
    ) -> QueryResult<TyCtxt<'tcx>> {
        self.check_invariants();
        // Check for overflow.
        let Some(available_depth) = Self::allowed_depth_for_nested(tcx, &self.stack) else {
            if let Some(last) = self.stack.raw.last_mut() {
                last.encountered_overflow = true;
            }

            inspect.goal_evaluation_kind(inspect::WipCanonicalGoalEvaluationKind::Overflow);
            return response_no_constraints(tcx, input, Certainty::overflow(true));
        };

        if let Some(result) = self.lookup_global_cache(tcx, input, available_depth, inspect) {
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
            inspect
                .goal_evaluation_kind(inspect::WipCanonicalGoalEvaluationKind::ProvisionalCacheHit);
            Self::tag_cycle_participants(&mut self.stack, &entry.heads);
            return entry.result;
        } else if let Some(stack_depth) = cache_entry.stack_depth {
            // We have a nested goal which directly relies on a goal deeper in the stack.
            //
            // We start by tagging all cycle participants, as that's necessary for caching.
            //
            // Finally we can return either the provisional response or the initial response
            // in case we're in the first fixpoint iteration for this goal.
            inspect.goal_evaluation_kind(inspect::WipCanonicalGoalEvaluationKind::CycleInStack);
            let is_coinductive_cycle = Self::stack_coinductive_from(tcx, &self.stack, stack_depth);
            let usage_kind = if is_coinductive_cycle {
                HasBeenUsed::COINDUCTIVE_CYCLE
            } else {
                HasBeenUsed::INDUCTIVE_CYCLE
            };
            let heads = [(stack_depth, usage_kind)].into_iter().collect();
            Self::tag_cycle_participants(&mut self.stack, &heads);

            // Return the provisional result or, if we're in the first iteration,
            // start with no constraints.
            let result = if let Some(result) = self.stack[stack_depth].provisional_result {
                result
            } else if is_coinductive_cycle {
                response_no_constraints(tcx, input, Certainty::Yes)
            } else {
                response_no_constraints(tcx, input, Certainty::overflow(false))
            };

            debug!(?is_coinductive_cycle, ?result, "encountered cycle with depth {stack_depth:?}");
            return result;
        } else {
            // No entry, we push this goal on the stack and try to prove it.
            let depth = self.stack.next_index();
            cache_entry.stack_depth = Some(depth);
            if !self.try_apply_fixpoint_instantiation_cache_entry(
                tcx,
                available_depth,
                depth,
                input,
            ) {
                let entry = StackEntry {
                    input,
                    available_depth,
                    reached_depth: depth,
                    heads: Default::default(),
                    encountered_overflow: false,
                    has_been_used: HasBeenUsed::empty(),
                    cycle_participants: Default::default(),
                    provisional_result: None,
                };
                assert_eq!(self.stack.push(entry), depth);
            }
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
                        StepResult::HasChanged => debug!("canonical cycle fixpoint step"),
                    }
                }

                debug!("canonical cycle overflow");
                let current_entry = self.pop_stack();
                debug_assert!(current_entry.has_been_used.is_empty());
                let result = response_no_constraints(tcx, input, Certainty::overflow(false));
                (current_entry, result)
            });

        let proof_tree = inspect.finalize_evaluation(tcx);

        // We're now done with this goal. In case this goal is involved in a larger cycle
        // do not remove it from the provisional cache and update its provisional result.
        // We only add the root of cycles to the global cache.
        let depth = self.stack.next_index();
        if final_entry.heads.is_empty() {
            // When encountering a cycle, both inductive and coinductive, we only
            // move the root into the global cache. We also store all other cycle
            // participants involved.
            //
            // We must not use the global cache entry of a root goal if a cycle
            // participant is on the stack. This is necessary to prevent unstable
            // results. See the comment of `StackEntry::cycle_participants` for
            // more details.
            let provisional_cache_entry = self.provisional_cache.remove(&input);
            debug_assert_eq!(provisional_cache_entry.unwrap().stack_depth, Some(depth));
            self.clear_nested_fixpoint_instantion_cache_entries(&final_entry.cycle_participants);
            let reached_depth = final_entry.reached_depth.as_usize() - self.stack.len();
            self.global_cache(tcx).insert(
                tcx,
                input,
                proof_tree,
                reached_depth,
                final_entry.encountered_overflow,
                final_entry.cycle_participants,
                dep_node,
                result,
            )
        } else {
            let heads = final_entry.heads;
            let head = *heads.last_key_value().unwrap().0;
            debug_assert!(head < depth);
            debug_assert_ne!(self.stack[head].has_been_used, HasBeenUsed::empty());
            debug_assert!(final_entry.cycle_participants.is_empty());
            let coinductive_stack = Self::stack_coinductive_from(tcx, &self.stack, head);
            let entry = self.provisional_cache.get_mut(&input).unwrap();
            assert_eq!(entry.stack_depth.take(), Some(depth));
            if coinductive_stack {
                entry.with_coinductive_stack = Some(DetachedEntry { heads, result });
            } else {
                entry.with_inductive_stack = Some(DetachedEntry { heads, result });
            }
        }

        self.check_invariants();

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
        inspect: &mut ProofTreeBuilder<TyCtxt<'tcx>>,
    ) -> Option<QueryResult<TyCtxt<'tcx>>> {
        let CacheData { result, proof_tree, additional_depth, encountered_overflow } = self
            .global_cache(tcx)
            .get(tcx, input, self.stack.iter().map(|e| e.input), available_depth)?;

        // If we're building a proof tree and the current cache entry does not
        // contain a proof tree, we do not use the entry but instead recompute
        // the goal. We simply overwrite the existing entry once we're done,
        // caching the proof tree.
        if !inspect.is_noop() {
            if let Some(revisions) = proof_tree {
                let kind = inspect::WipCanonicalGoalEvaluationKind::Interned { revisions };
                inspect.goal_evaluation_kind(kind);
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

    /// After reaching a fixpoint for a given stack entry, add an entry into
    /// the fixpoint instantiation cache to reuse it in future fixpoint iterations.
    ///
    /// We also stash all detached entries whose highest cycle head is the current goal.
    /// These entries can only be reused once we're recomputing the current goal and all
    /// the provisional results they depend on haven't changed.
    fn add_fixpoint_instantiation_cache_entry(
        &mut self,
        entry: &StackEntry<TyCtxt<'tcx>>,
        provisional_result: QueryResult<TyCtxt<'tcx>>,
        detached_entries: FxHashMap<
            CanonicalInput<TyCtxt<'tcx>>,
            StashedDetachedEntry<TyCtxt<'tcx>>,
        >,
    ) {
        // No need to cache cycle roots in the fixpoint instantiation cache.
        // Their final value gets moved to the global cache instead.
        if entry.heads.is_empty() {
            return;
        }

        let cache_entries = self.fixpoint_instantiation_cache.entry(entry.input).or_default();
        if cfg!(debug_assertions) {
            // We should only use this function after computing a goal, at
            // the start of which we remove its previous fixpoint instantiation
            // cache entry.
            if let Some(r) = cache_entries.iter().find(|r| r.is_applicable(&self.stack)) {
                bug!("existing fixpoint instantiation cache entry: {r:?}");
            }

            #[allow(rustc::potential_query_instability)]
            for (_, detached_entry) in &detached_entries {
                let usage_kind = *detached_entry.heads.get(&self.stack.next_index()).unwrap();
                assert!(entry.has_been_used.contains(usage_kind));
            }
        }

        cache_entries.push(FixpointInstantiationCacheEntry {
            expected_stack: self.stack.iter().map(|e| e.input).collect(),
            heads: entry.heads.clone(),
            provisional_result,
            detached_entries,
        });

        debug_assert!(cache_entries.iter().find(|r| r.is_applicable(&self.stack)).is_some());
    }

    /// Tries to reuse results from the previous fixpoint iteration if they
    /// are still applicable.
    ///
    /// We are able to use this to both initialize the provisional result
    /// and add the results of nested goals to the provisional cache if they
    /// only depend on stack entries whose provisional result has not changed.
    fn try_apply_fixpoint_instantiation_cache_entry(
        &mut self,
        tcx: TyCtxt<'tcx>,
        available_depth: Limit,
        depth: StackDepth,
        input: CanonicalInput<TyCtxt<'tcx>>,
    ) -> bool {
        let Some(entries) = self.fixpoint_instantiation_cache.get_mut(&input) else {
            return false;
        };
        let Some(idx) = entries.iter().position(|r| r.is_applicable(&self.stack)) else {
            return false;
        };

        let FixpointInstantiationCacheEntry {
            expected_stack: _,
            heads,
            provisional_result,
            detached_entries,
        } = entries.remove(idx);

        let stack_entry = StackEntry {
            input,
            available_depth,
            reached_depth: depth,
            heads: heads.clone(),
            encountered_overflow: false,
            has_been_used: HasBeenUsed::empty(),
            cycle_participants: Default::default(),
            provisional_result: Some(provisional_result),
        };
        assert_eq!(self.stack.push(stack_entry), depth);
        
        Self::tag_cycle_participants(&mut self.stack, &heads);
        assert!(!self.stack.raw.last().unwrap().heads.is_empty());

        #[allow(rustc::potential_query_instability)]
        for (input, detached_entry) in detached_entries {
            if detached_entry.is_applicable(tcx, &self.stack) {
                let StashedDetachedEntry { heads, provisional_results: _, is_coinductive, result } =
                    detached_entry;
                let cache_entry = self.provisional_cache.entry(input).or_default();
                if is_coinductive {
                    cache_entry.with_coinductive_stack = Some(DetachedEntry { heads, result });
                } else {
                    cache_entry.with_inductive_stack = Some(DetachedEntry { heads, result });
                }
            }
        }

        true
    }

    /// When popping a cycle root from the stack, we remove all its cycle participants
    /// from the fixpoint instantiation cache as they shouldn't be used anymore.
    fn clear_nested_fixpoint_instantion_cache_entries(
        &mut self,
        cycle_participants: &FxHashSet<CanonicalInput<TyCtxt<'tcx>>>,
    ) {
        #[allow(rustc::potential_query_instability)]
        for participant in cycle_participants {
            // We do not move non-head cycle participants into the fixpoint instantiation
            // cache, so not all participants are present.
            let Some(cache_entries) = self.fixpoint_instantiation_cache.remove(participant) else {
                continue;
            };
            if cfg!(debug_assertions) {
                // `cache_entries` may be empty if reevaluating a goal from the fixpoint
                // instantiation cache ends not causing a cycle. This is the case in
                // ui/traits/inductive-overflow/issue-90662-minimization.rs. See that
                // test for an explanation.
                for entry in cache_entries {
                    assert!(self.stack.len() <= entry.expected_stack.len());
                    assert!(
                        iter::zip(&self.stack, entry.expected_stack).all(|(l, r)| l.input == r)
                    );
                }
            }
        }
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
        inspect: &mut ProofTreeBuilder<TyCtxt<'tcx>>,
        prove_goal: &mut F,
    ) -> StepResult<TyCtxt<'tcx>>
    where
        F: FnMut(&mut Self, &mut ProofTreeBuilder<TyCtxt<'tcx>>) -> QueryResult<TyCtxt<'tcx>>,
    {
        self.check_invariants();
        let result = prove_goal(self, inspect);
        let stack_entry = self.pop_stack();
        debug_assert_eq!(stack_entry.input, input);

        // If the current goal is not the root of a cycle, we are done.
        if stack_entry.has_been_used.is_empty() {
            // We have to clear the provisional results here as they may
            // have been needed by the fixpoint instantiation cache, but
            // due to different provisional results aren't required as
            // nested goals anymore.
            Self::clear_dependent_provisional_results(
                &mut self.provisional_cache,
                self.stack.next_index(),
                |_, _, _| {},
            );
            return StepResult::Done(stack_entry, result);
        }

        // If it is a cycle head, we have to keep trying to prove it until
        // we reach a fixpoint. We've reached a fixpoint either because the final result
        // is equal to the provisional result of the previous iteration, or because
        // this was only the root of either coinductive or inductive cycles, and the
        // final result is equal to the initial response for that case.
        //
        // We need to rerun all cycle heads, not only cycle roots. See
        // tests/ui/traits/next-solver/cycles/fixpoint-rerun-all-cycle-heads.rs
        // for an example.
        let reached_fixpoint = if let Some(r) = stack_entry.provisional_result {
            r == result
        } else if stack_entry.has_been_used == HasBeenUsed::COINDUCTIVE_CYCLE {
            response_no_constraints(tcx, input, Certainty::Yes) == result
        } else if stack_entry.has_been_used == HasBeenUsed::INDUCTIVE_CYCLE {
            response_no_constraints(tcx, input, Certainty::overflow(false)) == result
        } else {
            false
        };

        // If we did not reach a fixpoint, update the provisional result and reevaluate.
        if reached_fixpoint {
            let mut detached_cache_entries = FxHashMap::default();
            Self::clear_dependent_provisional_results(
                &mut self.provisional_cache,
                self.stack.next_index(),
                |input, coinductive, inductive| {
                    let (entry, is_coinductive) = match (coinductive, inductive) {
                        (Some(entry), None) => (entry, true),
                        (None, Some(entry)) => (entry, false),
                        _ => return,
                    };

                    let mut provisional_results = Vec::new();
                    for (&head, &usage_kind) in &entry.heads {
                        // We compute this after already popping the current goal from the stack.
                        let elem = &self.stack.get(head).unwrap_or(&stack_entry);
                        provisional_results.push(if let Some(result) = elem.provisional_result {
                            result
                        } else if usage_kind == HasBeenUsed::COINDUCTIVE_CYCLE {
                            response_no_constraints(tcx, elem.input, Certainty::Yes)
                        } else if usage_kind == HasBeenUsed::COINDUCTIVE_CYCLE {
                            response_no_constraints(tcx, elem.input, Certainty::overflow(false))
                        } else {
                            return; // just bail and ignore that result in this case for now
                        });
                    }
                    let entry = StashedDetachedEntry {
                        heads: entry.heads,
                        provisional_results,
                        is_coinductive,
                        result: entry.result,
                    };
                    assert!(detached_cache_entries.insert(input, entry).is_none());
                },
            );
            self.add_fixpoint_instantiation_cache_entry(
                &stack_entry,
                result,
                detached_cache_entries,
            );
            StepResult::Done(stack_entry, result)
        } else {
            // If not, recompute after throwing out all provisional cache
            // entries which depend on the current goal. We then update
            // the provisional result and recompute.
            Self::clear_dependent_provisional_results(
                &mut self.provisional_cache,
                self.stack.next_index(),
                |_, _, _| {},
            );
            let depth = self.stack.push(StackEntry {
                has_been_used: HasBeenUsed::empty(),
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

        let SearchGraph { mode: _, stack, provisional_cache, fixpoint_instantiation_cache } = self;
        if stack.is_empty() {
            assert!(provisional_cache.is_empty());
            assert!(fixpoint_instantiation_cache.is_empty());
        }

        for (depth, entry) in stack.iter_enumerated() {
            let StackEntry {
                input,
                available_depth: _,
                reached_depth: _,
                ref heads,
                encountered_overflow: _,
                has_been_used,
                ref cycle_participants,
                provisional_result,
            } = *entry;
            let cache_entry = provisional_cache.get(&entry.input).unwrap();
            assert_eq!(cache_entry.stack_depth, Some(depth));
            if let Some((&lowest_head, _)) = heads.first_key_value() {
                assert!(cycle_participants.is_empty());
                let mut current_root = lowest_head;
                while let Some((&parent, _)) = stack[current_root].heads.first_key_value() {
                    current_root = parent;
                }
                assert!(stack[current_root].cycle_participants.contains(&input));
            }

            for (&head, &usage_kind) in heads {
                assert!(head < depth);
                assert_ne!(usage_kind, HasBeenUsed::empty());
                assert!(stack[head].has_been_used.contains(usage_kind));
            }

            if !cycle_participants.is_empty() {
                assert!(provisional_result.is_some() || !has_been_used.is_empty());
                for entry in stack.iter().take(depth.as_usize()) {
                    assert_eq!(cycle_participants.get(&entry.input), None);
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

            // If a detached entry is from the fixpoint instantiation cache
            // its heads may still be unused in this fixpoint iteration and
            // that only changes once we use this provisional cache entry.
            //
            // This means we can't assert anything for detached entries here.
        }

        for (input, entries) in &self.fixpoint_instantiation_cache {
            for entry in entries {
                let FixpointInstantiationCacheEntry {
                    ref expected_stack,
                    heads: _,
                    provisional_result: _,
                    detached_entries: _,
                } = *entry;

                assert!(
                    iter::zip(stack.iter(), expected_stack)
                        .take_while(|(l, &r)| l.input == r)
                        .any(|(e, _)| e.cycle_participants.contains(input))
                );
            }
        }
    }
}
