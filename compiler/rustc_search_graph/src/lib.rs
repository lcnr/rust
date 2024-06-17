use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::{Idx, IndexVec};
use std::{collections::BTreeMap, fmt::Debug, hash::Hash, iter, marker::PhantomData, mem};
use tracing::debug;

mod global_cache;
use global_cache::CacheData;
pub use global_cache::GlobalCache;
mod validate;

pub trait Cx: Copy {
    /// Used by rustc to target a separate global cache during coherence.
    type ProofTree: Debug + Copy;
    type Input: Debug + Eq + Hash + Copy;
    type Result: Debug + Eq + Hash + Copy;

    type DepNode;
    type Tracked<T: Clone>;
    fn mk_tracked<T: Clone>(self, data: T, dep_node: Self::DepNode) -> Self::Tracked<T>;
    fn get_tracked<T: Clone>(self, tracked: &Self::Tracked<T>) -> T;
    fn with_anon_task<R>(self, task: impl FnOnce() -> R) -> (R, Self::DepNode);
    fn with_global_cache<R>(
        self,
        mode: SolverMode,
        f: impl FnOnce(&mut GlobalCache<Self>) -> R,
    ) -> R;
}

pub trait Delegate<D>: Cx {
    const FIXPOINT_STEP_LIMIT: usize;
    type ProofTreeBuilder: ProofTreeBuilder<Self>;

    fn recursion_limit(self) -> usize;

    fn is_initial_provisional_result(self, usage_kind: UsageKind, result: Self::Result) -> bool;
    fn opt_initial_provisional_result(
        self,
        usage_kind: UsageKind,
        input: Self::Input,
    ) -> Option<Self::Result>;
    fn reached_fixpoint(
        self,
        usage_kind: UsageKind,
        provisional_result: Option<Self::Result>,
        result: Self::Result,
    ) -> bool;
    fn on_stack_overflow(
        self,
        inspect: &mut Self::ProofTreeBuilder,
        input: Self::Input,
    ) -> Self::Result;
    fn on_fixpoint_overflow(self, input: Self::Input) -> Self::Result;

    fn step_is_coinductive(self, input: Self::Input) -> bool;
}

#[derive(Debug, Clone, Copy)]
pub enum SolverMode {
    /// Ordinary trait solving, using everywhere except for coherence.
    Normal,
    /// Trait solving during coherence. There are a few notable differences
    /// between coherence and ordinary trait solving.
    ///
    /// Most importantly, trait solving during coherence must not be incomplete,
    /// i.e. return `Err(NoSolution)` for goals for which a solution exists.
    /// This means that we must not make any guesses or arbitrary choices.
    Coherence,
}

rustc_index::newtype_index! {
    #[orderable]
    struct StackDepth {}
}

#[derive(Debug, Clone, Copy)]
struct AvailableDepth(usize);
impl AvailableDepth {
    fn value_within_limit(self, value: usize) -> bool {
        self.0 >= value
    }
}

/// In the initial iteration of a cycle, we do not yet have a provisional
/// result. In the case we return an initial provisional result depending
/// on the kind of cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UsageKind {
    Coinductive,
    Inductive,
    Both,
}

impl UsageKind {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (UsageKind::Coinductive, UsageKind::Coinductive) => UsageKind::Coinductive,
            (UsageKind::Inductive, UsageKind::Inductive) => UsageKind::Inductive,
            (UsageKind::Both, _)
            | (_, UsageKind::Both)
            | (UsageKind::Inductive, UsageKind::Coinductive)
            | (UsageKind::Coinductive, UsageKind::Inductive) => UsageKind::Both,
        }
    }

    fn contains(self, other: Self) -> bool {
        match (self, other) {
            (UsageKind::Both, _)
            | (UsageKind::Coinductive, UsageKind::Coinductive)
            | (UsageKind::Inductive, UsageKind::Inductive) => true,
            (UsageKind::Inductive, UsageKind::Coinductive | UsageKind::Both)
            | (UsageKind::Coinductive, UsageKind::Inductive | UsageKind::Both) => false,
        }
    }
}

pub trait ProofTreeBuilder<X: Cx> {
    fn try_apply_proof_tree(&mut self, proof_tree: X::ProofTree) -> bool;
    fn on_provisional_cache_hit(&mut self);
    fn on_cycle_in_stack(&mut self);
    fn finalize_canonical_goal_evaluation(&mut self, cx: X) -> X::ProofTree;
}

#[derive(Debug, Default, PartialEq, Eq)]
struct CycleHeads {
    heads: BTreeMap<StackDepth, UsageKind>,
}

impl CycleHeads {
    fn new_head(depth: StackDepth, usage_kind: UsageKind) -> CycleHeads {
        CycleHeads { heads: iter::once((depth, usage_kind)).collect() }
    }

    fn extend(&mut self, other: &CycleHeads) {
        for (&head, &usage_kind) in other.heads.iter() {
            self.add_dependency(head, usage_kind);
        }
    }

    fn add_dependency(&mut self, depth: StackDepth, usage_kind: UsageKind) {
        self.heads
            .entry(depth)
            .and_modify(|prev| *prev = prev.merge(usage_kind))
            .or_insert(usage_kind);
    }

    fn len(&self) -> usize {
        self.heads.len()
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
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""), Default(bound = ""))]
struct NestedGoals<X: Cx> {
    nested_goals: FxHashSet<X::Input>,
}

impl<X: Cx> NestedGoals<X> {
    fn insert(&mut self, goal: X::Input) {
        self.nested_goals.insert(goal);
    }

    fn extend(&mut self, goals: &NestedGoals<X>) {
        self.nested_goals.extend(&goals.nested_goals);
    }

    fn contains(&self, input: X::Input) -> bool {
        self.nested_goals.contains(&input)
    }

    fn referenced_by_stack(&self, stack: &IndexVec<StackDepth, StackEntry<X>>) -> bool {
        stack.iter().any(|e| self.nested_goals.contains(&e.input))
    }
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct StackEntry<X: Cx> {
    input: X::Input,
    available_depth: AvailableDepth,

    /// The maximum depth reached by this stack entry, only up-to date
    /// for the top of the stack and lazily updated for the rest.
    reached_depth: StackDepth,

    /// The cycle heads this goal depends on. This does not include this
    /// goal itself, even if there's a self-cycle.
    heads: CycleHeads,

    encountered_overflow: bool,

    /// Whether this goal has been used as the head of a cycle, including
    /// any self-cycle.
    has_been_used: Option<UsageKind>,

    nested_goals: NestedGoals<X>,

    /// In case this goal has been used as the head of a cycle, we set this to
    /// the result of the previous iteration until reaching a fixpoint.
    provisional_result: Option<X::Result>,
}

#[derive(derivative::Derivative)]
#[derivative(
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = ""),
    Clone(bound = ""),
    Copy(bound = "")
)]
struct CycleHeadData<X: Cx> {
    input: X::Input,
    usage_kind: UsageKind,
    expected_result: X::Result,
}

/// A currently not applicable detached entry of the provisional result.
///
/// Will be moved back into the `provisional_cache` once it's applicable again.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
struct StashedDetachedEntry<X: Cx> {
    heads: Vec<CycleHeadData<X>>,
    coinductive_until: usize,
    nested_goals: NestedGoals<X>,

    input: X::Input,
    result: X::Result,
}

impl<X: Cx> StashedDetachedEntry<X> {
    fn is_applicable<D>(
        &self,
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        provisional_cache: &FxHashMap<X::Input, ProvisionalCacheEntry<X>>,
    ) -> Option<CycleHeads>
    where
        X: Delegate<D>,
    {
        // All stack entries used by this stashed entry still have the same
        // provisional result.
        let mut cycle_heads = CycleHeads::default();
        let mut stack_iter = stack.iter_enumerated().rev();
        let mut coinductive_stack = true;
        'cycle_heads: for (i, &CycleHeadData { input, usage_kind, expected_result }) in
            self.heads.iter().enumerate().rev()
        {
            'stack_entries: while let Some((depth, entry)) = stack_iter.next() {
                coinductive_stack = coinductive_stack && cx.step_is_coinductive(entry.input);

                if input != entry.input {
                    continue 'stack_entries;
                }

                if (i >= self.coinductive_until) != coinductive_stack {
                    return None;
                }

                let result_matches = if let Some(actual) = entry.provisional_result {
                    actual == expected_result
                } else {
                    cx.is_initial_provisional_result(usage_kind, expected_result)
                };

                if !result_matches {
                    return None;
                }

                cycle_heads.add_dependency(depth, usage_kind);
                continue 'cycle_heads;
            }

            return None;
        }

        // This entry did not use any current stack entry as a nested goal.
        //
        // Given an original cycle of `A -> B -> C -> A, B`, the result for `B` in
        // `A -> C -> B` may be different and we must not use its provisional
        // result.
        if self.nested_goals.referenced_by_stack(stack) {
            return None;
        } else {
            Some(cycle_heads)
        }
    }
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
struct DetachedEntry<X: Cx> {
    heads: CycleHeads,
    nested_goals: NestedGoals<X>,

    result: X::Result,
}

impl<X: Cx> DetachedEntry<X> {
    fn highest_cycle_head(&self) -> StackDepth {
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
#[derivative(Default(bound = ""), Debug(bound = ""))]
struct ProvisionalCacheEntry<X: Cx> {
    stack_depth: Option<StackDepth>,
    with_inductive_stack: Option<DetachedEntry<X>>,
    with_coinductive_stack: Option<DetachedEntry<X>>,
}

impl<X: Cx> ProvisionalCacheEntry<X> {
    fn is_empty(&self) -> bool {
        self.stack_depth.is_none()
            && self.with_inductive_stack.is_none()
            && self.with_coinductive_stack.is_none()
    }
}

enum StepResult<X: Cx> {
    Done(StackEntry<X>, X::Result),
    HasChanged,
}

pub struct SearchGraph<X: Cx, D> {
    mode: SolverMode,

    stack: IndexVec<StackDepth, StackEntry<X>>,

    provisional_cache: FxHashMap<X::Input, ProvisionalCacheEntry<X>>,
    detached_entries_stash: FxHashMap<X::Input, Vec<StashedDetachedEntry<X>>>,

    _marker: PhantomData<D>,
}

impl<X: Delegate<D>, D> SearchGraph<X, D> {
    pub fn new(mode: SolverMode) -> SearchGraph<X, D> {
        Self {
            mode,
            stack: Default::default(),
            provisional_cache: Default::default(),
            detached_entries_stash: Default::default(),
            _marker: PhantomData,
        }
    }

    pub fn solver_mode(&self) -> SolverMode {
        self.mode
    }

    /// Pops the highest goal from the stack, lazily updating the
    /// the next goal in the stack.
    ///
    /// Directly popping from the stack instead of using this method
    /// would cause us to not track overflow and recursion depth correctly.
    fn pop_stack(&mut self) -> StackEntry<X> {
        let elem = self.stack.pop().unwrap();
        if let Some(last) = self.stack.raw.last_mut() {
            last.reached_depth = last.reached_depth.max(elem.reached_depth);
            last.encountered_overflow |= elem.encountered_overflow;
        }
        elem
    }

    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    /// Returns the remaining depth allowed for nested goals.
    ///
    /// This is generally simply one less than the current depth.
    /// However, if we encountered overflow, we significantly reduce
    /// the remaining depth of all nested goals to prevent hangs
    /// in case there is exponential blowup.
    fn allowed_depth_for_nested(
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
    ) -> Option<AvailableDepth> {
        if let Some(last) = stack.raw.last() {
            if last.available_depth.0 == 0 {
                return None;
            }

            Some(if last.encountered_overflow {
                AvailableDepth(last.available_depth.0 / 4)
            } else {
                AvailableDepth(last.available_depth.0 - 1)
            })
        } else {
            Some(AvailableDepth(cx.recursion_limit()))
        }
    }

    fn stack_coinductive_from(
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        head: StackDepth,
    ) -> bool {
        stack.raw[head.index()..].iter().all(|entry| cx.step_is_coinductive(entry.input))
    }

    /// When encountering a solver cycle, the result of the current goal
    /// depends on the result of any cycle heads lower on the stack.
    fn tag_cycle_participants(
        stack: &mut IndexVec<StackDepth, StackEntry<X>>,
        heads: &CycleHeads,
        detached_entry: Option<(X::Input, &NestedGoals<X>)>,
    ) {
        for (head, usage_kind) in heads.iter() {
            stack[head].has_been_used =
                Some(stack[head].has_been_used.map_or(usage_kind, |prev| prev.merge(usage_kind)));
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
            let (current, prev) = stack.split_last_mut().unwrap();
            for entry in nested {
                current.nested_goals.insert(entry.input);
                current.nested_goals.extend(&entry.nested_goals);
            }
            if let Some((input, nested_goals)) = detached_entry {
                current.nested_goals.insert(input);
                current.nested_goals.extend(nested_goals);
            }

            // Update all the cycle heads this goal depends on.
            for (head, usage_kind) in heads.iter().filter(|(h, _)| h.index() < depth) {
                current.heads.add_dependency(head, usage_kind);
                // Subtle: this goal also depends on all cycle heads its cycle heads
                // depend on as these previous cycles while computing its heads change
                // the behavior.
                current.heads.extend(&prev[head.as_usize()].heads);
            }
        }
    }

    fn insert_relevant_stashed_detached_entries(&mut self, cx: X, input: X::Input) {
        let Some(stashed_entries) = self.detached_entries_stash.get_mut(&input) else { return };
        stashed_entries.retain_mut(|stashed_entry| {
            let Some(heads) = stashed_entry.is_applicable(cx, &self.stack, &self.provisional_cache)
            else {
                return true;
            };

            debug_assert_eq!(heads.highest_cycle_head(), self.stack.last_index());
            let detached_entry = DetachedEntry {
                heads,
                nested_goals: mem::take(&mut stashed_entry.nested_goals),
                result: stashed_entry.result,
            };

            if let Some(entry) = self.provisional_cache.get(&stashed_entry.input) {
                // The path from the highest cycle head to the stashed goal is coinductive.
                if stashed_entry.coinductive_until < stashed_entry.heads.len() {
                    if let Some(e) = &entry.with_coinductive_stack {
                        if e.highest_cycle_head() != detached_entry.highest_cycle_head() || e.result != detached_entry.result {
                            let e_heads = e.heads.iter().map(|(h, _)| self.stack[h].input).collect::<Vec<_>>();
                            let detached_entry_heads = detached_entry.heads.iter().map(|(h, _)| self.stack[h].input).collect::<Vec<_>>();
                            tracing::warn!(?stashed_entry.input, ?entry, ?e_heads, ?detached_entry, ?detached_entry_heads, ?stashed_entry, ?self.stack, ?self.provisional_cache);
                            panic!()
                        }
                    }
                } else {
                    if let Some(e) = &entry.with_inductive_stack {
                        if e.highest_cycle_head() != detached_entry.highest_cycle_head() || e.result != detached_entry.result {
                            let e_heads = e.heads.iter().map(|(h, _)| self.stack[h].input).collect::<Vec<_>>();
                            let detached_entry_heads = detached_entry.heads.iter().map(|(h, _)| self.stack[h].input).collect::<Vec<_>>();
                            tracing::warn!(?stashed_entry.input, ?entry, ?e_heads, ?detached_entry, ?detached_entry_heads, ?stashed_entry, ?self.stack, ?self.provisional_cache);
                            panic!()
                        }
                    }
                }
            };

            false
        })
    }

    fn stash_invalidated_detached_entries(&mut self, cx: X, added_goal: X::Input) {
        let mut stash_detached_entry = |input, entry: DetachedEntry<X>, is_coinductive| {
            let coinductive_until = if is_coinductive {
                let highest_cycle_head = entry.heads.highest_cycle_head().unwrap().as_usize();
                let enumerated_heads = entry.heads.iter().enumerate();
                let coinductive_heads = enumerated_heads.filter(|(_, (head, _))| {
                    self.stack.raw[head.as_usize()..highest_cycle_head]
                        .iter()
                        .all(|e| cx.step_is_coinductive(e.input))
                });
                coinductive_heads.last().unwrap().0
            } else {
                entry.heads.len()
            };

            let mut heads = Vec::new();
            for (head, usage_kind) in entry.heads.iter() {
                let elem = &self.stack[head];
                let Some(expected_result) = elem
                    .provisional_result
                    .or_else(|| cx.opt_initial_provisional_result(usage_kind, elem.input))
                else {
                    debug!(?input, "discard invalidated entry");
                    return;
                };
                heads.push(CycleHeadData { input: elem.input, usage_kind, expected_result });
            }

            let highest_cycle_head = heads.last().unwrap().input;
            let stashed_entry = StashedDetachedEntry {
                heads,
                nested_goals: entry.nested_goals,
                coinductive_until,
                input,
                result: entry.result,
            };
            debug!(?stashed_entry, "stash invalidated entry");

            self.detached_entries_stash.entry(highest_cycle_head).or_default().push(stashed_entry);
        };

        #[allow(rustc::potential_query_instability)]
        self.provisional_cache.retain(|input, entry| {
            if let Some(e) = entry.with_coinductive_stack.take_if(|p| {
                p.nested_goals.contains(added_goal) || !cx.step_is_coinductive(added_goal)
            }) {
                stash_detached_entry(*input, e, true);
            }
            if let Some(e) =
                entry.with_inductive_stack.take_if(|p| p.nested_goals.contains(added_goal))
            {
                stash_detached_entry(*input, e, false);
            }

            !entry.is_empty()
        });
    }

    fn stash_dependent_detached_entries(&mut self, cx: X, stack_entry: &StackEntry<X>) {
        let mut stash_detached_entry = |input, entry: DetachedEntry<X>, is_coinductive| {
            let coinductive_until = if is_coinductive {
                let highest_cycle_head = entry.heads.highest_cycle_head().unwrap().as_usize();
                let enumerated_heads = entry
                    .heads
                    .iter()
                    .enumerate()
                    .filter(|(_, (h, _))| h.as_usize() != highest_cycle_head);
                let coinductive_heads = enumerated_heads.filter(|(_, (head, _))| {
                    self.stack.raw[head.as_usize()..]
                        .iter()
                        .all(|e| cx.step_is_coinductive(e.input))
                });
                coinductive_heads.last().map_or(entry.heads.len() - 1, |(i, _)| i)
            } else {
                entry.heads.len()
            };

            let mut heads = Vec::new();
            for (head, usage_kind) in entry.heads.iter() {
                let elem = self.stack.get(head).unwrap_or_else(|| {
                    assert_eq!(head, self.stack.next_index());
                    stack_entry
                });

                let Some(expected_result) = elem
                    .provisional_result
                    .or_else(|| cx.opt_initial_provisional_result(usage_kind, elem.input))
                else {
                    debug!(?input, "discard dependent entry");
                    return;
                };
                heads.push(CycleHeadData { input: elem.input, usage_kind, expected_result });
            }

            let stashed_entry = StashedDetachedEntry {
                heads,
                nested_goals: entry.nested_goals,
                coinductive_until,
                input,
                result: entry.result,
            };
            debug!(?stashed_entry, "stash dependent entry");

            self.detached_entries_stash.entry(stack_entry.input).or_default().push(stashed_entry);
        };

        let head = self.stack.next_index();
        #[allow(rustc::potential_query_instability)]
        self.provisional_cache.retain(|input, entry| {
            if let Some(e) =
                entry.with_coinductive_stack.take_if(|p| p.highest_cycle_head() == head)
            {
                stash_detached_entry(*input, e, true);
            }
            if let Some(e) = entry.with_inductive_stack.take_if(|p| p.highest_cycle_head() == head)
            {
                stash_detached_entry(*input, e, false);
            }

            !entry.is_empty()
        });
    }

    /// Try to fetch a previously computed result from the global cache,
    /// making sure to only do so if it would match the result of reevaluating
    /// this goal.
    fn lookup_global_cache(
        &mut self,
        cx: X,
        input: X::Input,
        available_depth: AvailableDepth,
        inspect: &mut X::ProofTreeBuilder,
    ) -> Option<X::Result> {
        let CacheData { result, proof_tree, additional_depth, encountered_overflow } = cx
            .with_global_cache(self.mode, |cache| {
                cache.get(cx, input, &self.stack, available_depth)
            })?;

        // If we're building a proof tree and the current cache entry does not
        // contain a proof tree, we do not use the entry but instead recompute
        // the goal. We simply overwrite the existing entry once we're done,
        // caching the proof tree.
        if !inspect.try_apply_proof_tree(proof_tree) {
            return None;
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

    /// When we encounter a coinductive cycle, we have to fetch the
    /// result of that cycle while we are still computing it. Because
    /// of this we continuously recompute the cycle until the result
    /// of the previous iteration is equal to the final result, at which
    /// point we are done.
    fn fixpoint_step_in_task<F>(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut X::ProofTreeBuilder,
        prove_goal: &mut F,
    ) -> StepResult<X>
    where
        F: FnMut(&mut Self, &mut X::ProofTreeBuilder) -> X::Result,
    {
        self.check_invariants();
        // Insert all relevant stashed detached entries for the given
        // provisional result.
        self.insert_relevant_stashed_detached_entries(cx, input);

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
        self.stash_dependent_detached_entries(cx, &stack_entry);

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
        // If we did not reach a fixpoint, update the provisional result and reevaluate.
        if cx.reached_fixpoint(usage_kind, stack_entry.provisional_result, result) {
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

    pub fn with_new_goal(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut X::ProofTreeBuilder,
        prove_goal: impl FnMut(&mut Self, &mut X::ProofTreeBuilder) -> X::Result,
    ) -> X::Result {
        self.check_invariants();
        let result = self.with_new_goal_inner(cx, input, inspect, prove_goal);
        self.check_invariants();
        result
    }

    /// Probably the most involved method of the whole solver.
    ///
    /// Given some goal which is proven via the `prove_goal` closure, this
    /// handles caching, overflow, and coinductive cycles.
    fn with_new_goal_inner(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut X::ProofTreeBuilder,
        mut prove_goal: impl FnMut(&mut Self, &mut X::ProofTreeBuilder) -> X::Result,
    ) -> X::Result {
        // Check for overflow.
        let Some(available_depth) = Self::allowed_depth_for_nested(cx, &self.stack) else {
            if let Some(last) = self.stack.raw.last_mut() {
                last.encountered_overflow = true;
            }

            return cx.on_stack_overflow(inspect, input);
        };

        if let Some(result) = self.lookup_global_cache(cx, input, available_depth, inspect) {
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
            .filter(|p| Self::stack_coinductive_from(cx, &self.stack, p.highest_cycle_head()))
            .or_else(|| {
                cache_entry.with_inductive_stack.as_ref().filter(|p| {
                    !Self::stack_coinductive_from(cx, &self.stack, p.highest_cycle_head())
                })
            })
            .filter(|p| !p.nested_goals.referenced_by_stack(&self.stack))
        {
            // We have a nested goal which is already in the provisional cache, use
            // its result. We do not provide any usage kind as that should have been
            // already set correctly while computing the cache entry.
            debug!("provisional cache hit");
            inspect.on_provisional_cache_hit();
            Self::tag_cycle_participants(
                &mut self.stack,
                &entry.heads,
                Some((input, &entry.nested_goals)),
            );
            return entry.result;
        } else if let Some(stack_depth) = cache_entry.stack_depth {
            // We have a nested goal which directly relies on a goal deeper in the stack.
            //
            // We start by tagging all cycle participants, as that's necessary for caching.
            //
            // Finally we can return either the provisional response or the initial response
            // in case we're in the first fixpoint iteration for this goal.
            inspect.on_cycle_in_stack();
            let is_coinductive_cycle = Self::stack_coinductive_from(cx, &self.stack, stack_depth);
            let usage_kind =
                if is_coinductive_cycle { UsageKind::Coinductive } else { UsageKind::Inductive };
            debug!(?usage_kind, "encountered cycle with depth {stack_depth:?}");
            let heads = CycleHeads::new_head(stack_depth, usage_kind);
            Self::tag_cycle_participants(&mut self.stack, &heads, None);

            // Return the provisional result or, if we're in the first iteration,
            // start with no constraints.
            return self.stack[stack_depth]
                .provisional_result
                .unwrap_or_else(|| cx.opt_initial_provisional_result(usage_kind, input).unwrap());
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

        // In case the currently added goal is a nested goal of a detached entry,
        // it has to get removed from the provisional cache.
        self.stash_invalidated_detached_entries(cx, input);

        // This is for global caching, so we properly track query dependencies.
        // Everything that affects the `result` should be performed within this
        // `with_anon_task` closure. If computing this goal depends on something
        // not tracked by the cache key and from outside of this anon task, it
        // must not be added to the global cache. Notably, this is the case for
        // trait solver cycles participants.
        let ((final_entry, result), dep_node) = cx.with_anon_task(|| {
            for _ in 0..X::FIXPOINT_STEP_LIMIT {
                match self.fixpoint_step_in_task(cx, input, inspect, &mut prove_goal) {
                    StepResult::Done(final_entry, result) => return (final_entry, result),
                    StepResult::HasChanged => debug!("fixpoint changed provisional results"),
                }
            }

            debug!("canonical cycle overflow");
            let current_entry = self.pop_stack();
            debug_assert!(current_entry.has_been_used.is_none());
            let result = cx.on_fixpoint_overflow(input);
            (current_entry, result)
        });

        let proof_tree = inspect.finalize_canonical_goal_evaluation(cx);

        let depth = self.stack.next_index();
        if let Some(head) = final_entry.heads.highest_cycle_head() {
            debug_assert!(head < depth);
            debug_assert!(self.stack[head].has_been_used.is_some());
            let heads = final_entry.heads;
            let nested_goals = final_entry.nested_goals;
            let coinductive_stack = Self::stack_coinductive_from(cx, &self.stack, head);
            let entry = self.provisional_cache.get_mut(&input).unwrap();
            assert_eq!(entry.stack_depth.take(), Some(depth));
            if coinductive_stack {
                entry.with_coinductive_stack = Some(DetachedEntry { heads, nested_goals, result });
            } else {
                entry.with_inductive_stack = Some(DetachedEntry { heads, nested_goals, result });
            }
        } else {
            debug!(?input, ?final_entry.nested_goals, "to global cache");
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
            let additional_depth = final_entry.reached_depth.as_usize() - self.stack.len();
            cx.with_global_cache(self.mode, |cache| {
                cache.insert(
                    cx,
                    input,
                    result,
                    proof_tree,
                    dep_node,
                    additional_depth,
                    final_entry.encountered_overflow,
                    &final_entry.nested_goals,
                )
            })
        }

        result
    }
}
