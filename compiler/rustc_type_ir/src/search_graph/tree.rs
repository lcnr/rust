use std::hash::Hash;

use derive_where::derive_where;
use rustc_index::IndexVec;
use rustc_type_ir::data_structures::{HashMap, HashSet};

use crate::search_graph::{AvailableDepth, Cx, CycleHeads, PathKind, Stack, StackDepth};

#[derive_where(Debug, Clone, Copy, PartialEq, Eq, Hash; X: Cx)]
pub(super) struct GoalInfo<X: Cx> {
    pub input: X::Input,
    pub step_kind_from_parent: PathKind,
    pub available_depth: AvailableDepth,
}

rustc_index::newtype_index! {
    #[orderable]
    #[gate_rustc_only]
    pub struct NodeId {} // TODO: private
}

#[derive_where(Debug; X: Cx)]
pub(super) enum NodeKind<X: Cx> {
    InProgress { cycles: Vec<Cycle<X>> },
    Finished { encountered_overflow: bool, heads: CycleHeads, result: X::Result },
    CycleOnStack { entry_node_id: NodeId, result: X::Result },
    ProvisionalCacheHit { entry_node_id: NodeId },
}

#[derive_where(Debug; X: Cx)]
struct Node<X: Cx> {
    info: GoalInfo<X>,
    parent: Option<NodeId>,
    kind: NodeKind<X>,
}

#[derive_where(Debug; X: Cx)]
pub(super) struct Cycle<X: Cx> {
    pub node_id: NodeId,
    pub provisional_results: HashMap<StackDepth, X::Result>,
}

#[derive_where(Debug, Default; X: Cx)]
pub(super) struct SearchTree<X: Cx> {
    nodes: IndexVec<NodeId, Node<X>>,
}

impl<X: Cx> SearchTree<X> {
    pub(super) fn create_node(
        &mut self,
        stack: &Stack<X>,
        input: X::Input,
        step_kind_from_parent: PathKind,
        available_depth: AvailableDepth,
    ) -> NodeId {
        let info = GoalInfo { input, step_kind_from_parent, available_depth };
        let parent = stack.last().map(|e| e.node_id);
        self.nodes.push(Node { info, parent, kind: NodeKind::InProgress { cycles: vec![] } })
    }

    pub(super) fn global_cache_hit(&mut self, node_id: NodeId) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        self.nodes.pop();
    }

    pub(super) fn provisional_cache_hit(
        &mut self,
        stack: &Stack<X>,
        node_id: NodeId,
        entry_node_id: NodeId,
        heads: &CycleHeads,
        mut provisional_results: impl FnMut() -> HashMap<StackDepth, X::Result>,
    ) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        self.nodes[node_id].kind = NodeKind::ProvisionalCacheHit { entry_node_id };
        for (h, _) in heads.iter() {
            let head_node_id = stack[h].node_id;
            if let NodeKind::InProgress { cycles } = &mut self.nodes[head_node_id].kind {
                cycles.push(Cycle { node_id, provisional_results: provisional_results() });
            };
        }
    }

    pub(super) fn cycle_on_stack(
        &mut self,
        node_id: NodeId,
        entry_node_id: NodeId,
        result: X::Result,
        mut provisional_results: impl FnMut() -> HashMap<StackDepth, X::Result>,
    ) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        if let NodeKind::InProgress { cycles } = &mut self.nodes[entry_node_id].kind {
            cycles.push(Cycle { node_id, provisional_results: provisional_results() });
        };
        self.nodes[node_id].kind = NodeKind::CycleOnStack { entry_node_id, result }
    }

    pub(super) fn finish_evaluation(
        &mut self,
        node_id: NodeId,
        encountered_overflow: bool,
        heads: CycleHeads,
        result: X::Result,
    ) {
        let NodeKind::InProgress { cycles: _ } = self.nodes[node_id].kind else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        };
        self.nodes[node_id].kind = NodeKind::Finished { encountered_overflow, heads, result }
    }

    pub(super) fn node_kind_raw(&self, node_id: NodeId) -> &NodeKind<X> {
        &self.nodes[node_id].kind
    }

    pub(super) fn result_matches(&self, prev: NodeId, new: NodeId) -> bool {
        match (&self.nodes[prev].kind, &self.nodes[new].kind) {
            (
                NodeKind::Finished {
                    encountered_overflow: prev_overflow,
                    heads: prev_heads,
                    result: prev_result,
                },
                NodeKind::Finished {
                    encountered_overflow: new_overflow,
                    heads: new_heads,
                    result: new_result,
                },
            ) => {
                prev_result == new_result
                    && (*prev_overflow || !*new_overflow)
                    && prev_heads.contains(new_heads)
            }
            (
                NodeKind::CycleOnStack { entry_node_id: _, result: prev },
                NodeKind::CycleOnStack { entry_node_id: _, result: new },
            ) => prev == new,
            (&NodeKind::ProvisionalCacheHit { entry_node_id }, _) => {
                self.result_matches(entry_node_id, new)
            }
            (_, &NodeKind::ProvisionalCacheHit { entry_node_id }) => {
                self.result_matches(prev, entry_node_id)
            }
            result_matches => {
                tracing::debug!(?result_matches);
                false
            }
        }
    }

    pub(super) fn rerun_get_and_reset_cycles(&mut self, node_id: NodeId) -> Vec<Cycle<X>> {
        if let NodeKind::InProgress { cycles, .. } = &mut self.nodes[node_id].kind {
            std::mem::take(cycles)
        } else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        }
    }

    pub(super) fn get_heads(&self, node_id: NodeId) -> &CycleHeads {
        if let NodeKind::Finished { heads, .. } = &self.nodes[node_id].kind {
            heads
        } else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        }
    }

    pub(super) fn goal_or_parent_was_reevaluated(
        &self,
        cycle_head: NodeId,
        was_reevaluated: &HashSet<NodeId>,
        node_id: NodeId,
    ) -> bool {
        self.path_contains(cycle_head, node_id, |node_id| was_reevaluated.contains(&node_id))
    }

    pub(super) fn path_contains(
        &self,
        cycle_head: NodeId,
        mut node_id: NodeId,
        mut cond: impl FnMut(NodeId) -> bool,
    ) -> bool {
        loop {
            if node_id == cycle_head {
                return false;
            } else if cond(node_id) {
                return true;
            } else {
                node_id = self.nodes[node_id].parent.unwrap();
            }
        }
    }

    pub(super) fn uwu(
        &self,
        cycle_head: NodeId,
        mut node_id: NodeId,
        mut cond: impl FnMut(NodeId) -> bool,
    ) -> Option<GoalInfo<X>> {
        loop {
            if node_id == cycle_head {
                return None;
            } else  {
                let parent = self.nodes[node_id].parent.unwrap();
                if cond(parent) {
                    return Some(self.nodes[node_id].info);
                } else {
                    node_id = parent;
                };
            }
        }
    }

    /// Compute the list of parents of `node_id` until encountering the node
    /// `until`. We're excluding `until` and are including `node_id`.
    pub(super) fn compute_rev_stack(
        &self,
        mut node_id: NodeId,
        until: NodeId,
    ) -> Vec<(NodeId, GoalInfo<X>)> {
        let mut rev_stack = Vec::new();
        loop {
            if node_id == until {
                return rev_stack;
            }

            let node = &self.nodes[node_id];
            rev_stack.push((node_id, node.info));
            node_id = node.parent.unwrap();
        }
    }
}
