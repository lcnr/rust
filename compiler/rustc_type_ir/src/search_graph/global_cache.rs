use rustc_index::IndexVec;

use super::{AvailableDepth, Cx, StackDepth, StackEntry};
use crate::data_structures::{HashMap, HashSet};

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""), Copy(bound = ""))]
struct QueryData<X: Cx> {
    result: X::Result,
    proof_tree: X::ProofTree,
}

struct Success<X: Cx> {
    additional_depth: usize,
    nested_goals: HashSet<X::Input>,
    data: X::Tracked<QueryData<X>>,
}

struct WithOverflow<X: Cx> {
    nested_goals: HashSet<X::Input>,
    data: X::Tracked<QueryData<X>>,
}

/// The cache entry for a given input.
///
/// This contains results whose computation never hit the
/// recursion limit in `success`, and all results which hit
/// the recursion limit in `with_overflow`.
#[derive(derivative::Derivative)]
#[derivative(Default(bound = ""))]
struct CacheEntry<X: Cx> {
    success: Option<Success<X>>,
    with_overflow: HashMap<usize, WithOverflow<X>>,
}

#[derive(derivative::Derivative)]
#[derivative(Debug(bound = ""))]
pub(super) struct CacheData<'a, X: Cx> {
    pub(super) result: X::Result,
    pub(super) proof_tree: X::ProofTree,
    pub(super) additional_depth: usize,
    pub(super) encountered_overflow: bool,
    // FIXME: This is currently unused, but impacts the design
    // by requiring a closure for `Cx::with_global_cache`.
    pub(super) nested_goals: &'a HashSet<X::Input>,
}

#[derive(derivative::Derivative)]
#[derivative(Default(bound = ""))]
pub struct GlobalCache<X: Cx> {
    map: HashMap<X::Input, CacheEntry<X>>,
}

impl<X: Cx> GlobalCache<X> {
    /// Insert a final result into the global cache.
    pub(super) fn insert(
        &mut self,
        cx: X,
        input: X::Input,

        result: X::Result,
        proof_tree: X::ProofTree,
        dep_node: X::DepNodeIndex,

        additional_depth: usize,
        encountered_overflow: bool,
        nested_goals: HashSet<X::Input>,
    ) {
        let data = cx.mk_tracked(QueryData { result, proof_tree }, dep_node);
        let entry = self.map.entry(input).or_default();
        if encountered_overflow {
            let with_overflow = WithOverflow { nested_goals, data };
            let prev = entry.with_overflow.insert(additional_depth, with_overflow);
            assert!(prev.is_none());
        } else {
            let success = Success { additional_depth, nested_goals, data };
            let prev = entry.success.replace(success);
            assert!(prev.is_none());
        }
    }

    /// Try to fetch a cached result, checking the recursion limit
    /// and handling root goals of coinductive cycles.
    ///
    /// If this returns `Some` the cache result can be used.
    pub(super) fn get<'a>(
        &'a self,
        cx: X,
        input: X::Input,
        stack: &IndexVec<StackDepth, StackEntry<X>>,
        available_depth: AvailableDepth,
    ) -> Option<CacheData<'a, X>> {
        let entry = self.map.get(&input)?;

        let nested_goal_on_stack = |nested_goals: &HashSet<X::Input>| {
            stack.iter().any(|e| nested_goals.contains(&e.input))
        };
        if let Some(Success { additional_depth, ref nested_goals, ref data }) = entry.success {
            if available_depth.cache_entry_is_applicable(additional_depth)
                && !nested_goal_on_stack(nested_goals)
            {
                let QueryData { result, proof_tree } = cx.get_tracked(&data);
                return Some(CacheData {
                    result,
                    proof_tree,
                    additional_depth,
                    encountered_overflow: false,
                    nested_goals,
                });
            }
        }

        let additional_depth = available_depth.0;
        if let Some(WithOverflow { nested_goals, data }) =
            entry.with_overflow.get(&additional_depth)
        {
            if !nested_goal_on_stack(nested_goals) {
                let QueryData { result, proof_tree } = cx.get_tracked(data);
                return Some(CacheData {
                    result,
                    proof_tree,
                    additional_depth,
                    encountered_overflow: true,
                    nested_goals,
                });
            }
        }

        None
    }
}
