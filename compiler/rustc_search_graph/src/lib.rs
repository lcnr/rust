use rustc_data_structures::fx::FxHashMap;
use rustc_index::IndexVec;
use std::{cmp::Ordering, collections::BTreeMap, fmt::Debug, hash::Hash, marker::PhantomData};
use tracing::debug;

mod global_cache;
pub use global_cache::GlobalCache;
mod validate;

pub trait ProofTreeBuilder<X: Cx> {
    fn is_noop(&self) -> bool;
    fn on_cycle_in_stack(&mut self);
    fn finalize_canonical_goal_evaluation(&mut self, cx: X);
}

pub trait Cx: Copy {
    const VERIFY_CACHE: bool = false;

    type Input: Debug + Eq + Hash + Copy;
    type Result: Debug + Eq + Hash + Copy;

    type DepNode;
    type Tracked<T: Debug + Clone>: Debug;
    fn mk_tracked<T: Debug + Clone>(self, data: T, dep_node: Self::DepNode) -> Self::Tracked<T>;
    fn get_tracked<T: Debug + Clone>(self, tracked: &Self::Tracked<T>) -> T;
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

    fn initial_provisional_result(self, kind: PathKind, input: Self::Input) -> Self::Result;
    fn is_initial_provisional_result(
        self,
        input: Self::Input,
        result: Self::Result,
    ) -> Option<PathKind>;
    fn reached_fixpoint(
        self,
        input: Self::Input,
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

    fn step_kind(self, input: Self::Input) -> PathKind;
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
pub enum PathKind {
    Coinductive,
    Inductive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UsageKind {
    Single(PathKind),
    Mixed,
}

impl UsageKind {
    fn merge(self, other: impl Into<Self>) -> Self {
        match (self, other.into()) {
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

    fn and_merge(&mut self, other: impl Into<Self>) {
        *self = self.merge(other);
    }
}

impl From<PathKind> for UsageKind {
    fn from(value: PathKind) -> Self {
        UsageKind::Single(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct CycleHeads {
    heads: BTreeMap<StackDepth, UsageKind>,
}

impl CycleHeads {
    fn is_empty(&self) -> bool {
        self.heads.is_empty()
    }

    fn contains<X: Cx>(
        &self,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        input: X::Input,
    ) -> bool {
        self.heads.iter().any(|(h, _)| stack[*h].input == input)
    }

    fn iter(&self) -> impl Iterator<Item = (StackDepth, UsageKind)> + '_ {
        self.heads.iter().map(|(h, u)| (*h, *u))
    }

    fn insert(&mut self, head: StackDepth, usage_kind: UsageKind) {
        self.heads
            .entry(head)
            .and_modify(|paths| paths.and_merge(usage_kind))
            .or_insert(usage_kind);
    }

    fn extend_from_child(&mut self, this: StackDepth, step_kind: PathKind, child: &CycleHeads) {
        for (head, usage_kind) in child.iter() {
            match head.cmp(&this) {
                Ordering::Less => {}
                Ordering::Equal => continue,
                Ordering::Greater => unreachable!(),
            }

            let updated_usage_kind = match step_kind {
                // If this step is inductive, then all cycles using this step are inductive.
                PathKind::Inductive => UsageKind::Single(PathKind::Inductive),
                // If this step is coinductive, then it doesn't impact the cycle kind.
                PathKind::Coinductive => usage_kind,
            };
            self.insert(head, updated_usage_kind);
        }
    }
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
enum ExpectedResult<X: Cx> {
    Value(X::Result),
    Initial(UsageKind),
}

impl<X: Cx> ExpectedResult<X> {
    fn from_known<D>(cx: X, input: X::Input, result: X::Result) -> ExpectedResult<X>
    where
        X: Delegate<D>,
    {
        match cx.is_initial_provisional_result(input, result) {
            Some(path_kind) => ExpectedResult::Initial(UsageKind::Single(path_kind)),
            None => ExpectedResult::Value(result),
        }
    }
}

#[derive(derivative::Derivative)]
#[derivative(
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = ""),
    Clone(bound = ""),
    Copy(bound = "")
)]
struct NestedGoal<X: Cx> {
    path_from_entry: UsageKind,
    expected_result: Option<ExpectedResult<X>>,
}

impl<X: Cx> NestedGoal<X> {
    fn after_step(self, step_kind: PathKind) -> Self {
        match step_kind {
            PathKind::Coinductive => self,
            PathKind::Inductive => {
                let path_from_entry = UsageKind::Single(PathKind::Inductive);
                match self.expected_result {
                    None
                    | Some(ExpectedResult::Value(_))
                    | Some(ExpectedResult::Initial(UsageKind::Single(PathKind::Inductive))) => {
                        NestedGoal { path_from_entry, expected_result: self.expected_result }
                    }
                    Some(ExpectedResult::Initial(
                        UsageKind::Single(PathKind::Coinductive) | UsageKind::Mixed,
                    )) => NestedGoal { path_from_entry, expected_result: None },
                }
            }
        }
    }

    fn merge_expected_results(self, other: NestedGoal<X>) -> Option<ExpectedResult<X>> {
        match (self.expected_result?, other.expected_result?) {
            (ExpectedResult::Value(lhs), ExpectedResult::Value(rhs)) => {
                if lhs == rhs {
                    Some(ExpectedResult::Value(lhs))
                } else {
                    None
                }
            }

            (ExpectedResult::Value(_), ExpectedResult::Initial(_))
            | (ExpectedResult::Initial(_), ExpectedResult::Value(_)) => None,

            (
                ExpectedResult::Initial(UsageKind::Single(PathKind::Coinductive)),
                ExpectedResult::Initial(UsageKind::Single(PathKind::Coinductive)),
            ) => Some(ExpectedResult::Initial(UsageKind::Single(PathKind::Coinductive))),
            (
                ExpectedResult::Initial(UsageKind::Single(PathKind::Inductive)),
                ExpectedResult::Initial(UsageKind::Single(PathKind::Inductive)),
            ) => Some(ExpectedResult::Initial(UsageKind::Single(PathKind::Inductive))),
            (ExpectedResult::Initial(lhs), ExpectedResult::Initial(rhs)) => {
                // TODO: fuzz after enabling this and show that it errors + test
                if lhs == self.path_from_entry && rhs == other.path_from_entry {
                    Some(ExpectedResult::Initial(UsageKind::Mixed))
                } else {
                    None
                }
            }
        }
    }

    fn merge(self, other: NestedGoal<X>) -> NestedGoal<X> {
        let path_from_entry = self.path_from_entry.merge(other.path_from_entry);
        let expected_result = self.merge_expected_results(other);
        NestedGoal { path_from_entry, expected_result }
    }

    fn and_merge(&mut self, other: NestedGoal<X>) {
        *self = self.merge(other);
    }
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""), Default(bound = ""))]
struct NestedGoals<X: Cx> {
    nested_goals: FxHashMap<X::Input, NestedGoal<X>>,
}

impl<X: Cx> NestedGoals<X> {
    fn insert<D>(
        &mut self,
        input: X::Input,
        path_from_entry: UsageKind,
        expected_result: Option<ExpectedResult<X>>,
    ) where
        X: Delegate<D>,
    {
        let nested_goal = NestedGoal { path_from_entry, expected_result };
        self.nested_goals.entry(input).or_insert(nested_goal).and_merge(nested_goal);
    }

    fn extend_from_child(&mut self, step_kind: PathKind, nested_goals: &NestedGoals<X>) {
        #[allow(rustc::potential_query_instability)]
        for (&input, nested_goal) in nested_goals.nested_goals.iter() {
            let updated_nested_goal = nested_goal.after_step(step_kind);
            self.nested_goals
                .entry(input)
                .or_insert(updated_nested_goal)
                .and_merge(updated_nested_goal)
        }
    }

    fn contains(&self, input: X::Input) -> bool {
        self.nested_goals.contains_key(&input)
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

    fn stack_path_kind(
        cx: X,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        head: StackDepth,
    ) -> PathKind {
        let apply_step = |path, entry: &StackEntry<X>| match (path, cx.step_kind(entry.input)) {
            (PathKind::Coinductive, PathKind::Coinductive) => PathKind::Coinductive,
            (PathKind::Inductive, _) | (_, PathKind::Inductive) => PathKind::Inductive,
        };
        stack.raw[head.index()..].iter().fold(PathKind::Coinductive, apply_step)
    }

    fn update_parent_goal(
        &mut self,
        cx: X,
        input: X::Input,
        nested_goals: &NestedGoals<X>,
        heads: &CycleHeads,
        reached_depth: StackDepth,
        encountered_overflow: bool,
        result: X::Result,
    ) {
        if let Some(parent_index) = self.stack.last_index() {
            let parent = &mut self.stack[parent_index];
            parent.reached_depth = parent.reached_depth.max(reached_depth);
            parent.encountered_overflow |= encountered_overflow;

            let step_kind = cx.step_kind(parent.input);
            parent.heads.extend_from_child(parent_index, step_kind, &heads);

            parent.nested_goals.extend_from_child(step_kind, nested_goals);
            if !heads.is_empty() || encountered_overflow {
                let usage_kind = UsageKind::Single(cx.step_kind(parent.input));
                let expected_result = ExpectedResult::from_known(cx, input, result);
                parent.nested_goals.insert(input, usage_kind, Some(expected_result));
            }
        }
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
        if last_index != depth {
            let path_from_entry = cx.step_kind(last.input);
            last.heads.insert(depth, UsageKind::Single(path_from_entry));
        }

        let path_kind = Self::stack_path_kind(cx, &self.stack, depth);
        let usage_kind = UsageKind::Single(Self::stack_path_kind(cx, &self.stack, depth));
        self.stack[depth].has_been_used.get_or_insert(usage_kind).and_merge(usage_kind);

        debug!(?path_kind, "encountered cycle with depth {depth:?}");
        if let Some(result) = self.stack[depth].provisional_result {
            Some(result)
        } else {
            Some(cx.initial_provisional_result(path_kind, input))
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
        if cx.reached_fixpoint(input, usage_kind, stack_entry.provisional_result, result) {
            StepResult::Done(stack_entry, result)
        } else {
            self.stack.push(StackEntry {
                has_been_used: None,
                provisional_result: Some(result),
                ..stack_entry
            });
            debug!(?result, "fixpoint changed provisional result");
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
        let Some(available_depth) = AvailableDepth::allowed_depth_for_nested(cx, &self.stack)
        else {
            if let Some(last) = self.stack.raw.last_mut() {
                last.encountered_overflow = true;
            }

            debug!("encountered stack overflow");
            return cx.on_stack_overflow(inspect, input);
        };

        if let Some(result) = self.handle_cyclic_goal(cx, input, inspect) {
            return result;
        }

        let verify_result = if X::VERIFY_CACHE {
            AvailableDepth::allowed_depth_for_nested(cx, &self.stack).and_then(|available_depth| {
                self.lookup_global_cache_untracked(cx, input, available_depth)
            })
        } else if inspect.is_noop() {
            if let Some(result) = self.lookup_global_cache(cx, input, available_depth) {
                return result;
            } else {
                None
            }
        } else {
            None
        };

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
        let ((final_entry, meh, result), dep_node) = cx.with_anon_task(|| {
            for _ in 0..X::FIXPOINT_STEP_LIMIT {
                match self.fixpoint_step_in_task(cx, input, inspect, &mut prove_goal) {
                    StepResult::Done(final_entry, result) => return (final_entry, false, result),
                    StepResult::HasChanged => {}
                }
            }

            debug!("canonical cycle overflow");
            let current_entry = self.stack.pop().unwrap();
            debug_assert!(current_entry.has_been_used.is_none());
            let result = cx.on_fixpoint_overflow(input);
            (current_entry, true, result)
        });

        inspect.finalize_canonical_goal_evaluation(cx);

        // Lazily update the stack entry of the caller unless this is the root goal.
        self.update_parent_goal(
            cx,
            input,
            &final_entry.nested_goals,
            &final_entry.heads,
            final_entry.reached_depth,
            final_entry.encountered_overflow ||meh,
            result,
        );

        // WARNING: We move a goal into the global cache after updating its parents.
        // We have to make sure that updating the parent doesn't impact the cache
        // entry. This is necessary as `update_parent_goal` relies on `final_entry`.
        if let Some(expected) = verify_result {
            assert_eq!(result, expected, "input={input:?}, result={result:?}, expected={expected:?}");
        } else if inspect.is_noop() {
            self.insert_global_cache(cx, input, final_entry, result, dep_node)
        }

        result
    }
}
