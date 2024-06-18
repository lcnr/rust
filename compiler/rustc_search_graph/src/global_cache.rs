use crate::{
    AvailableDepth, Cx, CycleHeads, Delegate, NestedGoals, PathKind, SearchGraph, StackDepth,
    StackEntry, UsageKind,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_index::{Idx, IndexVec};
use std::fmt::Debug;
use tracing::debug;

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
enum ExpectedResult<X: Cx> {
    Value(X::Result),
    Initial(UsageKind),
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
struct Head<X: Cx> {
    input: X::Input,
    /// How this entries uses a given head. Note
    /// that this only tracks paths from the entry
    /// to the head.
    path_from_entry: UsageKind,
    expected_result: ExpectedResult<X>,
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = "DEPTH: Debug"))]
struct Candidate<X: Cx, DEPTH> {
    additional_depth: DEPTH,
    heads: Vec<Head<X>>,
    nested_goals: NestedGoals<X>,
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
struct CacheData<'a, X: Cx> {
    result: X::Result,
    additional_depth: usize,
    encountered_overflow: bool,
    heads: CycleHeads,
    nested_goals: &'a NestedGoals<X>,
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

    result: X::Result,
    dep_node: X::DepNode,

    additional_depth: usize,
    encountered_overflow: bool,

    heads: Vec<Head<X>>,
    nested_goals: NestedGoals<X>,
) {
    let result = cx.mk_tracked(result, dep_node);
    let entry = cache.map.entry(input).or_default();
    if encountered_overflow {
        let candidate = Candidate { additional_depth: (), heads, nested_goals, result };
        let entry = entry.with_overflow.entry(additional_depth).or_default();
        entry.push(candidate);
    } else {
        let candidate = Candidate { additional_depth, heads, nested_goals, result };
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

fn consider_candidate<'a, X: Delegate<D>, D, DEPTH: Debug + Copy>(
    cx: X,
    candidate: &'a Candidate<X, DEPTH>,
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    check_depth: impl Fn(DEPTH) -> bool,
    overflow_data: impl Fn(DEPTH) -> (usize, bool),
) -> Option<CacheData<'a, X>> {
    if !check_depth(candidate.additional_depth) {
        return None;
    }

    let mut heads = CycleHeads::default();
    for head in &candidate.heads {
        let &Head { input, path_from_entry, expected_result } = head;
        let Some((head, entry)) = stack.iter_enumerated().find(|(_, e)| e.input == input) else {
            return None;
        };

        if !result_matches_expected(cx, stack, path_from_entry, expected_result, head, entry) {
            return None;
        }

        heads.insert(head, path_from_entry);
    }

    if candidate.nested_goals.referenced_by_stack(stack) {
        return None;
    }

    let (additional_depth, encountered_overflow) = overflow_data(candidate.additional_depth);
    debug!(?candidate, "success");
    Some(CacheData {
        result: cx.get_tracked(&candidate.result),
        additional_depth,
        encountered_overflow,
        heads,
        nested_goals: &candidate.nested_goals,
    })
}

fn consider_candidates<'a, X: Delegate<D>, D, DEPTH: Debug + Copy>(
    cx: X,
    candidates: &'a [Candidate<X, DEPTH>],
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    check_depth: impl Fn(DEPTH) -> bool,
    overflow_data: impl Fn(DEPTH) -> (usize, bool),
) -> Option<CacheData<'a, X>> {
    let mut results = candidates.iter().filter_map(|candidate| {
        consider_candidate(cx, candidate, stack, &check_depth, &overflow_data)
    });

    let result = results.next();
    if cfg!(debug_assertions) {
        if let Some(second) = results.next() {
            panic!("multiple applicable candidates: first={result:?}, second={second:?}");
        }
    }
    result
}

/// Try to fetch a cached result, checking the recursion limit
/// and handling root goals of coinductive cycles.
///
/// If this returns `Some` the cache result can be used.
fn get<'a, X: Delegate<D>, D>(
    cache: &'a GlobalCache<X>,
    cx: X,
    input: X::Input,
    stack: &IndexVec<StackDepth, StackEntry<X>>,
    available_depth: AvailableDepth,
) -> Option<CacheData<'a, X>> {
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
                nested_goals,
                &heads,
                reached_depth,
                encountered_overflow,
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
        let mut heads = vec![];
        for (head, path_from_entry) in final_entry.heads.iter() {
            let input = self.stack[head].input;
            let expected_result = if let Some(result) = self.stack[head].provisional_result {
                match cx.is_initial_provisional_result(input, result) {
                    Some(path_kind) => ExpectedResult::Initial(UsageKind::Single(path_kind)),
                    None => ExpectedResult::Value(result),
                }
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
            heads.push(Head { input, path_from_entry, expected_result })
        }

        let additional_depth = final_entry.reached_depth.as_usize() - self.stack.len();
        debug!(?input, ?heads, ?final_entry.nested_goals,  "to global cache");
        cx.with_global_cache(self.mode, |cache| {
            insert(
                cache,
                cx,
                input,
                result,
                dep_node,
                additional_depth,
                final_entry.encountered_overflow,
                heads,
                final_entry.nested_goals,
            )
        });

        if cfg!(debug_assertions) {
            let cached =
                self.lookup_global_cache_untracked(cx, input, AvailableDepth(additional_depth));
            assert_eq!(cached, Some(result));
        }
    }
}
