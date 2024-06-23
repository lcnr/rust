use crate::{
    AvailableDepth, Cx, CycleHeads, Delegate, ExpectedResult, NestedGoal, NestedGoals, PathKind,
    SearchGraph, StackDepth, StackEntry, UsageKind,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_index::{Idx, IndexVec};
use std::fmt::Debug;
use tracing::debug;

#[derive(derivative::Derivative)]
#[derivative(
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = ""),
    Clone(bound = ""),
    Copy(bound = "")
)]
struct Dependency<X: Cx> {
    on_stack: bool,
    path_from_entry: UsageKind,
    expected_result: Option<ExpectedResult<X>>,
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = "DEPTH: Debug"))]
struct Candidate<X: Cx, DEPTH> {
    additional_depth: DEPTH,
    dependencies: FxHashMap<X::Input, Dependency<X>>,

    result: X::Tracked<X::Result>,
}

/// The cache entry for a given input.
///
/// This contains results whose computation never hit the
/// recursion limit in `success`, and all results which hit
/// the recursion limit in `with_overflow`.
#[derive(derivative::Derivative)]
#[derivative(Default(bound = ""))]
struct CacheEntry<X: Cx> {
    success: Vec<Candidate<X, usize>>,
    with_overflow: FxHashMap<usize, Vec<Candidate<X, ()>>>,
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
struct CacheData<X: Cx> {
    result: X::Result,
    additional_depth: usize,
    encountered_overflow: bool,
    heads: CycleHeads,
    nested_goals: NestedGoals<X>,
}

#[derive(derivative::Derivative)]
#[derivative(Default(bound = ""))]
pub struct GlobalCache<X: Cx> {
    map: FxHashMap<X::Input, CacheEntry<X>>,
}

fn insert<X: Delegate<D>, D>(
    cache: &mut GlobalCache<X>,
    cx: X,
    input: X::Input,
    dependencies: FxHashMap<X::Input, Dependency<X>>,

    result: X::Result,
    dep_node: X::DepNode,

    additional_depth: usize,
    encountered_overflow: bool,
) {
    let result = cx.mk_tracked(result, dep_node);
    let entry = cache.map.entry(input).or_default();
    if encountered_overflow {
        let candidate = Candidate { additional_depth: (), dependencies, result };
        let entry = entry.with_overflow.entry(additional_depth).or_default();
        entry.push(candidate);
    } else {
        let candidate = Candidate { additional_depth, dependencies, result };
        entry.success.push(candidate);
    }
}

fn result_matches_expected<X: Delegate<D>, D>(
    cx: X,
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    path_from_entry: UsageKind,
    expected_result: ExpectedResult<X>,
    head: StackDepth,
    head_entry: &StackEntry<X>,
) -> bool {
    if let Some(result) = head_entry.provisional_result {
        return match expected_result {
            ExpectedResult::Value(expected) => result == expected,
            ExpectedResult::Initial(UsageKind::Single(path_kind)) => cx
                .is_initial_provisional_result(head_entry.input, result)
                .is_some_and(|p| p == path_kind),
            ExpectedResult::Initial(UsageKind::Mixed) => false,
        };
    }

    match expected_result {
        ExpectedResult::Value(_) => false,
        ExpectedResult::Initial(UsageKind::Single(PathKind::Coinductive)) => {
            if let UsageKind::Single(PathKind::Coinductive) = path_from_entry {
                match SearchGraph::stack_path_kind(cx, stack, head) {
                    PathKind::Coinductive => true,
                    PathKind::Inductive => false,
                }
            } else {
                // This branch may seem unreachable, however, we may have used another
                // candidate in a previous iteration resulting in trivial provisional
                // result even though this cycle is not coinductive.
                false
            }
        }
        ExpectedResult::Initial(UsageKind::Single(PathKind::Inductive)) => {
            if let UsageKind::Single(PathKind::Inductive) = path_from_entry {
                true
            } else {
                match SearchGraph::stack_path_kind(cx, stack, head) {
                    PathKind::Coinductive => false,
                    PathKind::Inductive => true,
                }
            }
        }
        ExpectedResult::Initial(UsageKind::Mixed) => {
            debug_assert_eq!(path_from_entry, UsageKind::Mixed);
            match SearchGraph::stack_path_kind(cx, stack, head) {
                PathKind::Coinductive => true,
                PathKind::Inductive => false,
            }
        }
    }
}

fn consider_candidate<X: Delegate<D>, D, DEPTH: Debug + Copy>(
    cx: X,
    candidate: &Candidate<X, DEPTH>,
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    check_depth: impl Fn(DEPTH) -> bool,
    overflow_data: impl Fn(DEPTH) -> (usize, bool),
) -> Option<CacheData<X>> {
    if !check_depth(candidate.additional_depth) {
        return None;
    }

    let mut heads = CycleHeads::default();
    for (head, entry) in stack.iter_enumerated() {
        let Some(&Dependency { path_from_entry, expected_result, .. }) =
            candidate.dependencies.get(&entry.input)
        else {
            continue;
        };

        if !expected_result.is_some_and(|expected_result| {
            result_matches_expected(cx, stack, path_from_entry, expected_result, head, entry)
        }) {
            return None;
        }

        heads.insert(head, path_from_entry);
    }

    let mut nested_goals = NestedGoals::default();
    #[allow(rustc::potential_query_instability)]
    for (&input, &dependency) in &candidate.dependencies {
        if heads.contains(stack, input) {
            continue;
        }

        // If a dependency was on the stack when computing the cache entry
        // then we can only use that cache entry if it is also on the stack
        // during lookup.
        if dependency.on_stack {
            return None;
        }

        nested_goals.insert(input, dependency.path_from_entry, dependency.expected_result);
    }

    let (additional_depth, encountered_overflow) = overflow_data(candidate.additional_depth);
    debug!(?candidate, "success");
    Some(CacheData {
        result: cx.get_tracked(&candidate.result),
        additional_depth,
        encountered_overflow,
        heads,
        nested_goals,
    })
}

fn consider_candidates<X: Delegate<D>, D, DEPTH: Debug + Copy>(
    cx: X,
    candidates: &[Candidate<X, DEPTH>],
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    check_depth: impl Fn(DEPTH) -> bool,
    overflow_data: impl Fn(DEPTH) -> (usize, bool),
) -> Option<CacheData<X>> {
    let mut results = candidates.iter().rev().filter_map(|candidate| {
        consider_candidate(cx, candidate, stack, &check_depth, &overflow_data)
    });

    let result = results.next();
    if cfg!(debug_assertions) {
        for other in results {
            if other.result != result.as_ref().unwrap().result {
                panic!("inconsistent results: first={result:?}, second={other:?}");
            }
        }
    }
    result
}

/// Try to fetch a cached result, checking the recursion limit
/// and handling root goals of coinductive cycles.
///
/// If this returns `Some` the cache result can be used.
fn get<X: Delegate<D>, D>(
    cache: &GlobalCache<X>,
    cx: X,
    input: X::Input,
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    available_depth: AvailableDepth,
) -> Option<CacheData<X>> {
    let entry = cache.map.get(&input)?;
    if let Some(data) = consider_candidates(
        cx,
        &entry.success,
        stack,
        |additional_depth| available_depth.cache_entry_is_applicable(additional_depth),
        |additional_depth| (additional_depth, false),
    ) {
        return Some(data);
    }

    entry.with_overflow.get(&available_depth.0).and_then(|candidates| {
        consider_candidates(cx, candidates, stack, |()| true, |()| (available_depth.0, true))
    })
}

impl<X: Delegate<D>, D> SearchGraph<X, D> {
    /// Lookup a previously computed result from the global cache without
    /// modifying the search graph. This must only be used for debugging
    /// and is otherwise unsound.
    pub(super) fn lookup_global_cache_untracked(
        &self,
        cx: X,
        input: X::Input,
        available_depth: AvailableDepth,
    ) -> Option<X::Result> {
        cx.with_global_cache(self.mode, |cache| {
            get(cache, cx, input, &self.stack, available_depth).map(|data| data.result)
        })
    }

    /// Try to fetch a previously computed result from the global cache,
    /// making sure to only do so if it would match the result of reevaluating
    /// this goal.
    pub(super) fn lookup_global_cache(
        &mut self,
        cx: X,
        input: X::Input,
        available_depth: AvailableDepth,
    ) -> Option<X::Result> {
        if X::VERIFY_CACHE {
            return None;
        }

        cx.with_global_cache(self.mode, |cache| {
            let CacheData { result, additional_depth, encountered_overflow, heads, nested_goals } =
                get(cache, cx, input, &self.stack, available_depth)?;

            for (head, path_from_entry) in heads.iter() {
                let usage_kind = match Self::stack_path_kind(cx, &self.stack, head) {
                    PathKind::Coinductive => path_from_entry,
                    PathKind::Inductive => UsageKind::Single(PathKind::Inductive),
                };
                self.stack[head].has_been_used.get_or_insert(usage_kind).and_merge(usage_kind);
            }

            // Update the reached depth of the current goal to make sure
            // its state is the same regardless of whether we've used the
            // global cache or not.
            let reached_depth = self.stack.next_index().plus(additional_depth);
            self.update_parent_goal(
                cx,
                input,
                &nested_goals,
                &heads,
                reached_depth,
                encountered_overflow,
                result,
            );

            debug!("global cache hit");
            Some(result)
        })
    }

    pub(super) fn insert_global_cache(
        &self,
        cx: X,
        input: X::Input,
        final_entry: StackEntry<X>,
        result: X::Result,
        dep_node: X::DepNode,
    ) {
        let mut dependencies = FxHashMap::default();
        for (head, path_from_entry) in final_entry.heads.iter() {
            let input = self.stack[head].input;
            let expected_result = if let Some(result) = self.stack[head].provisional_result {
                ExpectedResult::from_known(cx, input, result)
            } else {
                let expected = match path_from_entry {
                    UsageKind::Single(PathKind::Inductive) => path_from_entry,
                    UsageKind::Single(PathKind::Coinductive) | UsageKind::Mixed => {
                        match Self::stack_path_kind(cx, &self.stack, head) {
                            PathKind::Coinductive => path_from_entry,
                            PathKind::Inductive => UsageKind::Single(PathKind::Inductive),
                        }
                    }
                };

                debug!(?head, ?path_from_entry, ?expected);

                ExpectedResult::Initial(expected)
            };
            let prev = dependencies.insert(
                input,
                Dependency {
                    on_stack: true,
                    path_from_entry,
                    expected_result: Some(expected_result),
                },
            );
            debug_assert_eq!(prev, None);
        }

        #[allow(rustc::potential_query_instability)]
        for (input, nested_goal) in final_entry.nested_goals.nested_goals {
            let NestedGoal { path_from_entry, expected_result } = nested_goal;
            let prev = dependencies
                .insert(input, Dependency { on_stack: false, path_from_entry, expected_result });
            debug_assert_eq!(prev, None);
        }

        let additional_depth = final_entry.reached_depth.as_usize() - self.stack.len();
        debug!(?input, ?dependencies, "to global cache");
        cx.with_global_cache(self.mode, |cache| {
            insert(
                cache,
                cx,
                input,
                dependencies,
                result,
                dep_node,
                additional_depth,
                final_entry.encountered_overflow,
            )
        });

        if cfg!(debug_assertions) {
            let cached =
                self.lookup_global_cache_untracked(cx, input, AvailableDepth(additional_depth));
            assert_eq!(cached, Some(result));
        }
    }
}
