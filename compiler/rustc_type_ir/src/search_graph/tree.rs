use std::hash::Hash;
use std::ops::Range;

use derive_where::derive_where;
use rustc_index::IndexVec;
use rustc_type_ir::data_structures::{BuildHasher, HashMap};

use crate::search_graph::{AvailableDepth, Cx, CycleHeads, PathKind, Stack, StackEntry};

#[derive_where(Debug, Clone, Copy; X: Cx)]
pub(super) struct GoalInfo<X: Cx> {
    input: X::Input,
    step_kind_from_parent: PathKind,
    available_depth: AvailableDepth,
    /// The provisional result used while evaluating this goal. We create a separate
    /// node for every rerun.
    provisional_result: Option<X::Result>,
}

rustc_index::newtype_index! {
    #[orderable]
    #[gate_rustc_only]
    pub(super) struct NodeId {}
}

rustc_index::newtype_index! {
    #[orderable]
    #[gate_rustc_only]
    pub(super) struct CycleId {}
}

#[derive_where(Debug; X: Cx)]
pub(super) enum NodeKind<X: Cx> {
    InProgress {
        cycles_start: CycleId,
    },
    Regular {
        cycles: Range<CycleId>,
        encountered_overflow: bool,
        heads: CycleHeads,
        result: X::Result,
    },
    Rerun {
        prev: NodeId,
        diff: HashMap<NodeId, NodeId>,
        cycles: Range<CycleId>,
    },
    ProvisionalCacheHit {
        entry_node_id: NodeId,
    },
    CycleOnStack {
        entry_node_id: NodeId,
        /// The provisional result used by the cycle. During the first iteration this
        /// depends on the cycle kind.
        result: X::Result,
    },
}

#[derive_where(Debug; X: Cx)]
struct Node<X: Cx> {
    info: GoalInfo<X>,
    parent: Option<NodeId>,
    kind: NodeKind<X>,
}

#[derive_where(Debug, Default; X: Cx)]
pub(super) struct SearchTree<X: Cx> {
    nodes: IndexVec<NodeId, Node<X>>,
    cycles: IndexVec<CycleId, NodeId>,
}

impl<X: Cx> SearchTree<X> {
    pub(super) fn create_node(
        &mut self,
        stack: &Stack<X>,
        input: X::Input,
        step_kind_from_parent: PathKind,
        available_depth: AvailableDepth,
        provisional_result: Option<X::Result>,
    ) -> NodeId {
        let info = GoalInfo { input, step_kind_from_parent, available_depth, provisional_result };
        let parent = stack.last().map(|e| e.node_id);
        self.nodes.push(Node {
            info,
            parent,
            kind: NodeKind::InProgress { cycles_start: self.cycles.next_index() },
        })
    }

    pub(super) fn global_cache_hit(&mut self, node_id: NodeId) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        self.nodes.pop();
    }

    pub(super) fn provisional_cache_hit(&mut self, node_id: NodeId, entry_node_id: NodeId) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        self.cycles.push(node_id);
        self.nodes[node_id].kind = NodeKind::ProvisionalCacheHit { entry_node_id };
    }

    pub(super) fn cycle_on_stack(
        &mut self,
        node_id: NodeId,
        entry_node_id: NodeId,
        result: X::Result,
    ) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        self.cycles.push(node_id);
        self.nodes[node_id].kind = NodeKind::CycleOnStack { entry_node_id, result }
    }

    pub(super) fn finish_evaluate(
        &mut self,
        node_id: NodeId,
        encountered_overflow: bool,
        heads: CycleHeads,
        result: X::Result,
    ) {
        let NodeKind::InProgress { cycles_start } = self.nodes[node_id].kind else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        };
        let cycles_end = self.cycles.next_index();
        self.nodes[node_id].kind = NodeKind::Regular {
            cycles: cycles_start..cycles_end,
            encountered_overflow,
            heads,
            result,
        }
    }

    pub(super) fn cycle_node_id(&mut self, cycle_id: CycleId) -> NodeId {
        self.cycles[cycle_id]
    }

    pub(super) fn node_kind_raw(&self, node_id: NodeId) -> &NodeKind<X> {
        &self.nodes[node_id].kind
    }

    pub(super) fn get_diff(&self, node_id: NodeId) -> &HashMap<NodeId, NodeId> {
        match &self.nodes[node_id].kind {
            NodeKind::Regular { .. } => const { &HashMap::with_hasher(BuildHasher) },
            NodeKind::Rerun { diff, .. } => diff,
            _ => panic!("unexpected node kind: {:?}", self.nodes[node_id]),
        }
    }

    pub(super) fn get_cycles(&mut self, node_id: NodeId) -> Range<CycleId> {
        if let NodeKind::Regular { ref cycles, .. } = self.nodes[node_id].kind {
            cycles.clone()
        } else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        }
    }

    pub(super) fn compute_rev_stack(
        &self,
        diff: &HashMap<NodeId, NodeId>,
        mut node_id: NodeId,
        until: X::Input,
    ) -> Option<Vec<GoalInfo<X>>> {
        let mut rev_stack = Vec::new();
        loop {
            if diff.contains_key(&node_id) {
                return None;
            }
            let node = &self.nodes[node_id];
            if node.info.input == until {
                break;
            }

            rev_stack.push(node.info);
            if let Some(parent) = node.parent {
                node_id = parent;
            } else {
                break;
            }
        }
        Some(rev_stack)
    }
}
