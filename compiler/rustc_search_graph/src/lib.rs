use rustc_data_structures::fx::FxHashSet;
use rustc_index::{Idx, IndexVec};
use std::{fmt::Debug, hash::Hash, marker::PhantomData};
use tracing::debug;

mod global_cache;
use global_cache::CacheData;
pub use global_cache::GlobalCache;
mod validate;

pub trait ProofTreeBuilder<X: Cx> {
    fn try_apply_proof_tree(&mut self, proof_tree: X::ProofTree) -> bool;
    fn on_cycle_in_stack(&mut self);
    fn finalize_canonical_goal_evaluation(&mut self, cx: X) -> X::ProofTree;
}

pub trait Cx: Copy {
    const VERIFY_CACHE: bool = false;

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

    fn initial_provisional_result(self, kind: CycleKind, input: Self::Input) -> Self::Result;
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
    /// Returns the remaining depth allowed for nested goals.
    ///
    /// This is generally simply one less than the current depth.
    /// However, if we encountered overflow, we significantly reduce
    /// the remaining depth of all nested goals to prevent hangs
    /// in case there is exponential blowup.
    fn allowed_depth_for_nested<X: Delegate<D>, D>(
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
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
            Some(AvailableDepth(cx.recursion_limit()))
        }
    }

    /// Whether we're allowed to use a global cache entry which required
    /// the given depth.
    fn cache_entry_is_applicable(self, additional_depth: usize) -> bool {
        self.0 >= additional_depth
    }
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
            (UsageKind::Single(lhs), UsageKind::Single(rhs)) => {
                if lhs == rhs {
                    UsageKind::Single(lhs)
                } else {
                    UsageKind::Mixed
                }
            }
            (UsageKind::Mixed, UsageKind::Mixed)
            | (UsageKind::Mixed, UsageKind::Single(_))
            | (UsageKind::Single(_), UsageKind::Mixed) => UsageKind::Mixed,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
struct CycleHeads {
    lowest_cycle_head: Option<StackDepth>,
}

impl CycleHeads {
    fn is_empty(&self) -> bool {
        self.lowest_cycle_head.is_none()
    }

    fn lowest_cycle_head(&self) -> Option<StackDepth> {
        self.lowest_cycle_head
    }

    fn insert(&mut self, head: StackDepth) {
        if let Some(curr) = &mut self.lowest_cycle_head {
            *curr = head.min(*curr);
        } else {
            self.lowest_cycle_head = Some(head);
        }
    }

    fn extend_from_child(&mut self, this: StackDepth, other: &CycleHeads) {
        if let Some(head) = other.lowest_cycle_head.filter(|h| *h != this) {
            self.insert(head);
        }
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

enum StepResult<X: Cx> {
    Done(StackEntry<X>, X::Result),
    HasChanged,
}

pub struct SearchGraph<X: Cx, D> {
    mode: SolverMode,

    stack: IndexVec<StackDepth, StackEntry<X>>,

    _marker: PhantomData<D>,
}

impl<X: Delegate<D>, D> SearchGraph<X, D> {
    pub fn new(mode: SolverMode) -> SearchGraph<X, D> {
        Self { mode, stack: Default::default(), _marker: PhantomData }
    }

    pub fn solver_mode(&self) -> SolverMode {
        self.mode
    }

    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    fn stack_coinductive_from(
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        head: StackDepth,
    ) -> bool {
        stack.raw[head.index()..].iter().all(|entry| cx.step_is_coinductive(entry.input))
    }

    fn update_parent_goal(
        &mut self,
        input: X::Input,
        nested_goals: &NestedGoals<X>,
        heads: &CycleHeads,
        reached_depth: StackDepth,
        encountered_overflow: bool,
    ) {
        if let Some(parent_index) = self.stack.last_index() {
            let parent = &mut self.stack[parent_index];
            parent.reached_depth = parent.reached_depth.max(reached_depth);
            parent.encountered_overflow |= encountered_overflow;

            parent.nested_goals.extend(nested_goals);
            if !heads.is_empty() || encountered_overflow {
                parent.nested_goals.insert(input);
            }

            parent.heads.extend_from_child(parent_index, &heads);
        }
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
        if X::VERIFY_CACHE {
            return None;
        }

        cx.with_global_cache(self.mode, |cache| {
            let CacheData {
                result,
                proof_tree,
                additional_depth,
                encountered_overflow,
                nested_goals,
            } = cache.get(cx, input, &self.stack, available_depth)?;

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
                input,
                nested_goals,
                &CycleHeads::default(),
                reached_depth,
                encountered_overflow,
            );

            debug!("global cache hit");
            Some(result)
        })
    }

    fn handle_cyclic_goal(
        &mut self,
        cx: X,
        input: X::Input,
        inspect: &mut X::ProofTreeBuilder,
    ) -> Option<X::Result> {
        let Some(depth) = self
            .stack
            .iter_enumerated()
            .find_map(|(depth, entry)| if entry.input == input { Some(depth) } else { None })
        else {
            return None;
        };

        inspect.on_cycle_in_stack();

        // Subtle: when encountering a cyclic goal, we still first checked for overflow,
        // so we have to update the reached depth.
        let next_index = self.stack.next_index();
        let last_index = self.stack.last_index().unwrap();
        let last = &mut self.stack[last_index];
        last.reached_depth = last.reached_depth.max(next_index);
        last.heads.insert(depth);
        if last_index != depth {
            last.heads.insert(depth);
        }

        let cycle_kind = if Self::stack_coinductive_from(cx, &self.stack, depth) {
            CycleKind::Coinductive
        } else {
            CycleKind::Inductive
        };

        let usage_kind = UsageKind::Single(cycle_kind);
        let head = &mut self.stack[depth];
        head.has_been_used =
            Some(head.has_been_used.map_or(usage_kind, |prev| prev.merge(usage_kind)));

        debug!(?cycle_kind, "encountered cycle with depth {depth:?}");
        if let Some(result) = self.stack[depth].provisional_result {
            Some(result)
        } else {
            Some(cx.initial_provisional_result(cycle_kind, input))
        }
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
        // If we did not reach a fixpoint, update the provisional result and reevaluate.
        if cx.reached_fixpoint(usage_kind, stack_entry.provisional_result, result) {
            StepResult::Done(stack_entry, result)
        } else {
            self.stack.push(StackEntry {
                has_been_used: None,
                provisional_result: Some(result),
                ..stack_entry
            });
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

        let verify = if X::VERIFY_CACHE && self.stack.iter().all(|e| e.input != input) {
            AvailableDepth::allowed_depth_for_nested(cx, &self.stack).and_then(|available_depth| {
                cx.with_global_cache(self.mode, |cache| {
                    cache.get(cx, input, &self.stack, available_depth).map(|data| data.result)
                })
            })
        } else {
            None
        };

        let result = self.with_new_goal_inner(cx, input, inspect, prove_goal);

        if let Some(expected) = verify {
            if expected != result {
                panic!("input: {input:?}, expected: {expected:?}, result: {result:?}");
            }
        }

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
        let Some(available_depth) = AvailableDepth::allowed_depth_for_nested(cx, &self.stack)
        else {
            if let Some(last) = self.stack.raw.last_mut() {
                last.encountered_overflow = true;
            }

            debug!("encountered stack overflow");
            return cx.on_stack_overflow(inspect, input);
        };

        if let Some(result) = self.lookup_global_cache(cx, input, available_depth, inspect) {
            return result;
        }

        if let Some(result) = self.handle_cyclic_goal(cx, input, inspect) {
            return result;
        }
        // No entry, we push this goal on the stack and try to prove it.
        let depth = self.stack.next_index();
        let actual_depth = self.stack.push(StackEntry {
            input,
            available_depth,
            reached_depth: depth,
            heads: Default::default(),
            encountered_overflow: false,
            has_been_used: None,
            nested_goals: Default::default(),
            provisional_result: None,
        });
        debug_assert_eq!(actual_depth, depth);

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
            let current_entry = self.stack.pop().unwrap();
            debug_assert!(current_entry.has_been_used.is_none());
            let result = cx.on_fixpoint_overflow(input);
            (current_entry, result)
        });

        let proof_tree = inspect.finalize_canonical_goal_evaluation(cx);

        if final_entry.heads.is_empty() {
            // When encountering a cycle, both inductive and coinductive, we only
            // move the root into the global cache. We also store all other cycle
            // participants involved.
            //
            // We must not use the global cache entry of a root goal if a cycle
            // participant is on the stack. This is necessary to prevent unstable
            // results. See the comment of `StackEntry::nested_goals` for
            // more details.
            let additional_depth = final_entry.reached_depth.as_usize() - self.stack.len();
            debug!(?input, ?final_entry.nested_goals, ?final_entry.encountered_overflow, ?additional_depth,  "to global cache");
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

        // Lazily update the stack entry of the caller unless this is the root goal.
        self.update_parent_goal(
            input,
            &final_entry.nested_goals,
            &final_entry.heads,
            final_entry.reached_depth,
            final_entry.encountered_overflow,
        );

        result
    }
}
