use std::collections::BTreeMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use rustc_index::{Idx, IndexVec};
use tracing::debug;

use crate::data_structures::{HashMap, HashSet};
use crate::solve::SolverMode;

mod global_cache;
use global_cache::CacheData;
pub use global_cache::GlobalCache;
mod validate;

/// The search graph does not simply use `Interner` directly
/// to enable its fuzzing without having to stub the rest of
/// the interner. We don't make this a super trait of `Interner`
/// as users of the shared type library shouldn't have to care
/// about `Input` and `Result` as they are implementation details
/// of the search graph.
pub trait Cx: Copy {
    type ProofTree: Debug + Copy;
    type Input: Debug + Eq + Hash + Copy;
    type Result: Debug + Eq + Hash + Copy;

    type DepNodeIndex;
    type Tracked<T: Debug + Clone>: Debug;
    fn mk_tracked<T: Debug + Clone>(
        self,
        data: T,
        dep_node_index: Self::DepNodeIndex,
    ) -> Self::Tracked<T>;
    fn get_tracked<T: Debug + Clone>(self, tracked: &Self::Tracked<T>) -> T;
    fn with_cached_task<T>(self, task: impl FnOnce() -> T) -> (T, Self::DepNodeIndex);

    fn with_global_cache<R>(
        self,
        mode: SolverMode,
        f: impl FnOnce(&mut GlobalCache<Self>) -> R,
    ) -> R;
}

pub trait ProofTreeBuilder<X: Cx> {
    fn try_apply_proof_tree(&mut self, proof_tree: X::ProofTree) -> bool;
    fn on_provisional_cache_hit(&mut self);
    fn on_cycle_in_stack(&mut self);
    fn finalize_canonical_goal_evaluation(&mut self, cx: X) -> X::ProofTree;
}

pub trait Delegate {
    /// If this returns `true` we do not use the global cache entry
    /// in case it exists and instead check that recomputing the goal
    /// matches the cache entry.
    ///
    /// Note that the fuzzer must track which cache entries we didn't try
    /// to use and then consistently not use that cache entry
    #[inline]
    fn validate_global_cache(_cx: Self::Cx, _input: <Self::Cx as Cx>::Input) -> bool {
        false
    }
    #[inline]
    fn finalize_validate(_cx: Self::Cx, _input: <Self::Cx as Cx>::Input) {}

    type Cx: Cx;
    const FIXPOINT_STEP_LIMIT: usize;
    type ProofTreeBuilder: ProofTreeBuilder<Self::Cx>;

    fn recursion_limit(cx: Self::Cx) -> usize;

    fn initial_provisional_result(
        cx: Self::Cx,
        kind: CycleKind,
        input: <Self::Cx as Cx>::Input,
    ) -> <Self::Cx as Cx>::Result;
    fn reached_fixpoint(
        cx: Self::Cx,
        kind: UsageKind,
        input: <Self::Cx as Cx>::Input,
        provisional_result: Option<<Self::Cx as Cx>::Result>,
        result: <Self::Cx as Cx>::Result,
    ) -> bool;
    fn on_stack_overflow(
        cx: Self::Cx,
        inspect: &mut Self::ProofTreeBuilder,
        input: <Self::Cx as Cx>::Input,
    ) -> <Self::Cx as Cx>::Result;
    fn on_fixpoint_overflow(
        cx: Self::Cx,
        input: <Self::Cx as Cx>::Input,
    ) -> <Self::Cx as Cx>::Result;

    fn step_is_coinductive(cx: Self::Cx, input: <Self::Cx as Cx>::Input) -> bool;
}

/// In the initial iteration of a cycle, we do not yet have a provisional
/// result. In the case we return an initial provisional result depending
/// on the kind of cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CycleKind {
    Coinductive,
    Inductive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UsageKind {
    Single(CycleKind),
    Mixed,
}
impl UsageKind {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (UsageKind::Mixed, _) | (_, UsageKind::Mixed) => UsageKind::Mixed,
            (UsageKind::Single(lhs), UsageKind::Single(rhs)) => {
                if lhs == rhs {
                    UsageKind::Single(lhs)
                } else {
                    UsageKind::Mixed
                }
            }
        }
    }
    fn and_merge(&mut self, other: Self) {
        *self = self.merge(other);
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
struct CycleHeads {
    heads: BTreeSet<StackDepth>,
}

impl<X: Cx> CycleHeads<X> {
    fn is_empty(&self) -> bool {
        self.heads.is_empty()
    }

    fn contains(&sef, input: StackDepth) -> bool {
        self.heads.contains_key(&input)
    }

    fn iter(&self) -> impl Iterator<Item = StackDepth> + '_ {
        self.heads.iter().copied()
    }

    fn insert(&mut self, head: X::Input) {
        self.heads
            .entry(head)
            .and_modify(|paths| paths.and_merge(usage_kind))
            .or_insert(usage_kind);
    }

    fn extend_from_child(
        &mut self,
        this: X::Input,
        step_kind: CycleKind,
        child_heads: impl Iterator<Item = (X::Input, UsageKind)>,
    ) {
        for (head, usage_kind) in child_heads {
            if head == this {
                continue;
            }

            let updated_usage_kind = match step_kind {
                // If this step is inductive, then all cycles using this step are inductive.
                CycleKind::Inductive => UsageKind::Single(CycleKind::Inductive),
                // If this step is coinductive, then it doesn't impact the cycle kind.
                CycleKind::Coinductive => usage_kind,
            };
            self.insert(head, updated_usage_kind);
        }
    }l
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""), Default(bound = ""))]
struct NestedGoals<X: Cx> {
    nested_goals: HashSet<X::Input>,
}

impl<X: Cx> NestedGoals<X> {
    fn insert(&mut self, input: X::Input) {
        self.nested_goals.insert(input);
    }

    fn extend(&mut self, nested_goals: &NestedGoals<X>) {
        self.nested_goals.extend(nested_goals.nested_goals.iter());
    }

    fn contains(&self, input: X::Input) -> bool {
        self.nested_goals.contains(&input)
    }
}

#[derive(Debug, Clone, Copy)]
struct AvailableDepth(usize);
impl AvailableDepth {
    /// Returns the remaining depth allowed for nested goals.
    ///
    /// This is generally simply one less than the current depth.
    /// However, if we encountered overflow, we significantly reduce
    /// the remaining depth of all nested goals to prevent hangs
    /// in case there is exponential blowup.
    fn allowed_depth_for_nested<D: Delegate>(
        cx: D::Cx,
        stack: &IndexVec<StackDepth, StackEntry<D::Cx>>,
    ) -> Option<AvailableDepth> {
        if let Some(last) = stack.raw.last() {
            if last.available_depth.0 == 0 {
                return None;
            }

            Some(if last.encountered_overflow {
                AvailableDepth(last.available_depth.0 / 2)
            } else {
                AvailableDepth(last.available_depth.0 - 1)
            })
        } else {
            Some(AvailableDepth(D::recursion_limit(cx)))
        }
    }

    /// Whether we're allowed to use a global cache entry which required
    /// the given depth.
    fn cache_entry_is_applicable(self, additional_depth: usize) -> bool {
        self.0 >= additional_depth
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[gate_rustc_only]
    pub struct StackDepth {}
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct StackEntry<X: Cx> {
    input: X::Input,

    available_depth: AvailableDepth,

    /// The maximum depth reached by this stack entry, only up-to date
    /// for the top of the stack and lazily updated for the rest.
    reached_depth: StackDepth,

    cycle_heads: CycleHeads<X>,

    encountered_overflow: bool,

    has_been_used: Option<UsageKind>,

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
    nested_goals: NestedGoals<X>,
    /// Starts out as `None` and gets set when rerunning this
    /// goal in case we encounter a cycle.
    provisional_result: Option<X::Result>,
}

/// The provisional result for a goal which is not on the stack.
#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct DetachedEntry<X: Cx> {
    cycle_heads: CycleHeads<X>,
    result: X::Result,
}

struct CycleCache<X: Cx> {
    root: StackDepth,
    entries: HashMap<X::Input, Vec<DetachedEntry<X>>>,
}

pub struct SearchGraph<D: Delegate<Cx = X>, X: Cx = <D as Delegate>::Cx> {
    mode: SolverMode,
    /// The stack of goals currently being computed.
    ///
    /// An element is *deeper* in the stack if its index is *lower*.
    stack: IndexVec<StackDepth, StackEntry<X>>,
    cycle_caches: Vec<CycleCache<X>>,

    _marker: PhantomData<D>,
}

impl<D: Delegate<Cx = X>, X: Cx> SearchGraph<D> {
    pub fn new(mode: SolverMode) -> SearchGraph<D> {
        Self {
            mode,
            stack: Default::default(),
            provisional_cache: Default::default(),
            _marker: PhantomData,
        }
    }

    pub fn solver_mode(&self) -> SolverMode {
        self.mode
    }

    fn step_kind(cx: X, input: X::Input) -> CycleKind {
        if D::step_is_coinductive(cx, input) {
            CycleKind::Coinductive
        } else {
            CycleKind::Inductive
        }
    }

    fn update_parent_goal_on_provisional(
        cx: X,
        provisional_cache: &HashMap<X::Input, ProvisionalCacheEntry<X>>,
        stack: &mut IndexVec<StackDepth, StackEntry<X>>,
        cycle_heads: &CycleHeads<X>,
    ) {
        assert!(!cycle_heads.is_empty());
        let last_index = stack.last_index().unwrap();
        let parent = &mut stack[last_index];
        let step_kind = Self::step_kind(cx, parent.input);
        let child_heads = cycle_heads
            .iter()
            .filter(|(key, _)| provisional_cache.get(key).is_some_and(|e| e.stack_depth.is_some()));
        parent.cycle_heads.extend_from_child(parent.input, step_kind, child_heads);
    }

    fn update_parent_goal(
        &mut self,
        cx: X,
        input: X::Input,
        reached_depth: StackDepth,
        cycle_heads: &CycleHeads<X>,
        encountered_overflow: bool,
        nested_goals: &NestedGoals<X>,
    ) {
        if let Some(last_index) = self.stack.last_index() {
            let parent = &mut self.stack[last_index];
            parent.reached_depth = parent.reached_depth.max(reached_depth);
            parent.encountered_overflow |= encountered_overflow;
            parent.nested_goals.extend(nested_goals);
            if !cycle_heads.is_empty() {
                let step_kind = Self::step_kind(cx, parent.input);
                parent.cycle_heads.extend_from_child(parent.input, step_kind, cycle_heads.iter());
                parent.nested_goals.insert(input);
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    fn stack_path_kind(
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        head: StackDepth,
    ) -> CycleKind {
        let is_coinductive =
            stack.raw[head.index()..].iter().all(|entry| D::step_is_coinductive(cx, entry.input));
        if is_coinductive { CycleKind::Coinductive } else { CycleKind::Inductive }
    }

    fn clear_dependent_cache(
        cycle_cache: &mut CycleCache<X>,
        input: X::Input,
    ) {
        #[allow(rustc::potential_query_instability)]
        cycle_cache.retain(|_, entry| {
            entry.detached_entries.retain(|e| e.cycle_heads.contains(input));
            !entry.is_empty()
        });
    }

    fn clear_provisional_cache_after_computing_goal(&mut self, input: X::Input) {
        #[allow(rustc::potential_query_instability)]
        self.provisional_cache.retain(|&key, entry| {
            if key == input {
                entry.stack_depth = None;
            }
            entry.detached_entries.retain(|detached| {
                self.stack.iter().any(|e| detached.cycle_heads.contains(e.input))
            });
            !entry.is_empty()
        });
    }

    /// Probably the most involved method of the whole solver.
    ///
    /// Given some goal which is proven via the `prove_goal` closure, this
    /// handles caching, overflow, and coinductive cycles.
    pub fn with_new_goal(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut D::ProofTreeBuilder,
        mut prove_goal: impl FnMut(&mut Self, &mut D::ProofTreeBuilder) -> X::Result,
    ) -> X::Result {
        self.check_invariants();
        // Check for overflow.
        let Some(available_depth) = AvailableDepth::allowed_depth_for_nested::<D>(cx, &self.stack)
        else {
            if let Some((last, start)) = self.stack.raw.split_last_mut() {
                last.encountered_overflow = true;
                if let Some(prev) = start.last_mut() {
                    prev.nested_goals.insert(last.input);
                }
            }

            debug!("encountered stack overflow");
            return D::on_stack_overflow(cx, inspect, input);
        };

        let verify_result = if D::validate_global_cache(cx, input) {
            self.lookup_global_cache_untracked(cx, input, available_depth)
        } else if let Some(result) = self.lookup_global_cache(cx, input, available_depth, inspect) {
            return result;
        } else {
            None
        };

        // Check whether the goal is in the provisional cache.
        // The provisional result may rely on the path to its cycle roots,
        // so we have to check the path of the current goal matches that of
        // the cache entry.
        if let Some(result) = self.lookup_provisional_cache(cx, input, inspect) {
            return result;
        }

        let cache_entry = self.provisional_cache.entry(input).or_default();
        if let Some(stack_depth) = cache_entry.stack_depth {
            debug!("encountered cycle with depth {stack_depth:?}");
            // We have a nested goal which directly relies on a goal deeper in the stack.
            //
            // We start by tagging all cycle participants, as that's necessary for caching.
            //
            // Finally we can return either the provisional response or the initial response
            // in case we're in the first fixpoint iteration for this goal.
            inspect.on_cycle_in_stack();

            // Subtle: when encountering a cyclic goal, we still first checked for overflow,
            // so we have to update the reached depth.
            let next_index = self.stack.next_index();
            let last = &mut self.stack.raw.last_mut().unwrap();
            last.reached_depth = last.reached_depth.max(next_index);

            if last.input != input {
                let path_from_entry = Self::step_kind(cx, last.input);
                last.cycle_heads.insert(input, UsageKind::Single(path_from_entry));
            }

            let cycle_kind = Self::stack_path_kind(cx, &self.stack, stack_depth);
            let usage_kind = UsageKind::Single(cycle_kind);
            self.stack[stack_depth].has_been_used.get_or_insert(usage_kind).and_merge(usage_kind);
            // Return the provisional result or, if we're in the first iteration,
            // start with no constraints.
            return if let Some(result) = self.stack[stack_depth].provisional_result {
                result
            } else {
                D::initial_provisional_result(cx, cycle_kind, input)
            };
        } else {
            // No entry, we push this goal on the stack and try to prove it.
            let depth = self.stack.next_index();
            let entry = StackEntry {
                input,
                available_depth,
                reached_depth: depth,
                cycle_heads: Default::default(),
                encountered_overflow: false,
                has_been_used: None,
                nested_goals: Default::default(),
                provisional_result: None,
            };
            assert_eq!(self.stack.push(entry), depth);
            cache_entry.stack_depth = Some(depth);
        };

        // This is for global caching, so we properly track query dependencies.
        // Everything that affects the `result` should be performed within this
        // `with_anon_task` closure. If computing this goal depends on something
        // not tracked by the cache key and from outside of this anon task, it
        // must not be added to the global cache. Notably, this is the case for
        // trait solver cycles participants.
        let ((final_entry, result), dep_node) = cx.with_cached_task(|| {
            for _ in 0..D::FIXPOINT_STEP_LIMIT {
                match self.fixpoint_step_in_task(cx, input, inspect, &mut prove_goal) {
                    StepResult::Done(final_entry, result) => return (final_entry, result),
                    StepResult::HasChanged => {}
                }
            }

            debug!("canonical cycle overflow");
            let current_entry = self.stack.pop().unwrap();
            debug_assert!(current_entry.has_been_used.is_none());
            let result = D::on_fixpoint_overflow(cx, input);
            (current_entry, result)
        });

        let proof_tree = inspect.finalize_canonical_goal_evaluation(cx);

        self.update_parent_goal(
            cx,
            input,
            final_entry.reached_depth,
            &final_entry.cycle_heads,
            final_entry.encountered_overflow,
            &final_entry.nested_goals,
        );

        // We're now done with this goal. In case this goal is involved in a larger cycle
        // do not remove it from the provisional cache and update its provisional result.
        // We only add the root of cycles to the global cache.
        if !final_entry.cycle_heads.is_empty() {
            debug_assert!(verify_result.is_none());
            let entry = self.provisional_cache.get_mut(&input).unwrap();
            entry.stack_depth = None;
            entry
                .detached_entries
                .push(DetachedEntry { cycle_heads: final_entry.cycle_heads, result });
        } else {
            // When encountering a cycle, both inductive and coinductive, we only
            // move the root into the global cache. We also store all other cycle
            // participants involved.
            //
            // We must not use the global cache entry of a root goal if a cycle
            // participant is on the stack. This is necessary to prevent unstable
            // results. See the comment of `StackEntry::nested_goals` for
            // more details.
            self.clear_provisional_cache_after_computing_goal(input);
            self.provisional_cache.remove(&input);
            if let Some(expected) = verify_result {
                // Do not try to move a goal into the cache again if we're testing the
                // global cache. We also need to notify the validator that we've
                // popped a goal from the stack as it must always disable the global
                // cache for a given goal while we're computing it as it would
                // otherwise hide cycles.
                assert_eq!(result, expected, "input={input:?}");
            } else {
                debug!(?input, ?result, ?final_entry, "to global cache");
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
                        final_entry.nested_goals,
                    )
                });

                if cfg!(debug_assertions) {
                    let actual = self.lookup_global_cache_untracked(cx, input, available_depth);
                    if actual.is_some_and(|actual| actual != result) {
                        debug!(?input, ?actual, ?result);
                        panic!();
                    }
                }
            }
        }

        self.check_invariants();

        result
    }

    fn lookup_global_cache_untracked(
        &self,
        cx: X,
        input: X::Input,
        available_depth: AvailableDepth,
    ) -> Option<X::Result> {
        cx.with_global_cache(self.mode, |cache| {
            let references_nested = |nested_goals: &NestedGoals<X>| {
                self.provisional_cache.keys().any(|&g| nested_goals.contains(g))
            };
            cache.get(cx, input, available_depth, references_nested).map(|c| c.result)
        })
    }

    /// Try to fetch a previously computed result from the global cache,
    /// making sure to only do so if it would match the result of reevaluating
    /// this goal.
    fn lookup_global_cache(
        &mut self,
        cx: X,
        input: X::Input,
        available_depth: AvailableDepth,
        inspect: &mut D::ProofTreeBuilder,
    ) -> Option<X::Result> {
        cx.with_global_cache(self.mode, |cache| {
            // TODO: explain
            let references_nested = |nested_goals: &NestedGoals<X>| {
                self.provisional_cache.keys().any(|&g| nested_goals.contains(g))
            };
            let CacheData {
                result,
                proof_tree,
                additional_depth,
                encountered_overflow,
                nested_goals,
            } = cache.get(cx, input, available_depth, references_nested)?;

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
            self.update_parent_goal(
                cx,
                input,
                reached_depth,
                &Default::default(),
                encountered_overflow,
                nested_goals,
            );

            debug!("global cache hit");
            Some(result)
        })
    }

    fn lookup_provisional_cache(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut D::ProofTreeBuilder,
    ) -> Option<X::Result> {
        for detached_entry in &self.provisional_cache.get(&input)?.detached_entries {
            if self.detached_entry_is_applicable(cx, detached_entry) {
                // We have a nested goal which is already in the provisional cache, use
                // its result. We do not provide any usage kind as that should have been
                // already set correctly while computing the cache entry.
                debug!(?detached_entry, "provisional cache hit");
                inspect.on_provisional_cache_hit();
                Self::update_parent_goal_on_provisional(
                    cx,
                    &self.provisional_cache,
                    &mut self.stack,
                    &detached_entry.cycle_heads,
                );
                return Some(detached_entry.result);
            }
        }

        None
    }

    fn detached_entry_is_applicable(&self, cx: X, detached_entry: &DetachedEntry<X>) -> bool {
        detached_entry.cycle_heads.iter().all(|(head, path_segment)| {
            let Some(head) = self.provisional_cache.get(&head).and_then(|e| e.stack_depth) else {
                return true;
            };

            if self.stack[head].provisional_result.is_some() {
                return true;
            }

            match path_segment {
                UsageKind::Mixed => false,
                UsageKind::Single(path_segment) => {
                    SearchGraph::<D, X>::stack_path_kind(cx, &self.stack, head) == path_segment
                }
            }
        })
    }
}

enum StepResult<X: Cx> {
    Done(StackEntry<X>, X::Result),
    HasChanged,
}

impl<D: Delegate<Cx = X>, X: Cx> SearchGraph<D> {
    /// When we encounter a coinductive cycle, we have to fetch the
    /// result of that cycle while we are still computing it. Because
    /// of this we continuously recompute the cycle until the result
    /// of the previous iteration is equal to the final result, at which
    /// point we are done.
    fn fixpoint_step_in_task<F>(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut D::ProofTreeBuilder,
        prove_goal: &mut F,
    ) -> StepResult<X>
    where
        F: FnMut(&mut Self, &mut D::ProofTreeBuilder) -> X::Result,
    {
        let result = prove_goal(self, inspect);
        let stack_entry = self.stack.pop().unwrap();
        debug_assert_eq!(stack_entry.input, input);

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

        // Start by clearing all provisional cache entries which depend on this
        // the current goal.
        Self::clear_dependent_cache(&mut self.cycle_caches.last_mut().unwrap(), input);

        // Check whether we reached a fixpoint, either because the final result
        // is equal to the provisional result of the previous iteration, or because
        // this was only the root of either coinductive or inductive cycles, and the
        // final result is equal to the initial response for that case.
        //
        // If we did not reach a fixpoint, update the provisional result and reevaluate.
        if D::reached_fixpoint(cx, usage_kind, input, stack_entry.provisional_result, result) {
            StepResult::Done(stack_entry, result)
        } else {
            debug!(?result, "fixpoint changed provisional results");
            let depth = self.stack.push(StackEntry {
                has_been_used: None,
                provisional_result: Some(result),
                ..stack_entry
            });
            StepResult::HasChanged
        }
    }
}
