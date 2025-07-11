use std::hash::Hash;
use std::ops::Range;

use derive_where::derive_where;
use rustc_index::IndexVec;
use rustc_type_ir::data_structures::{HashMap, HashSet};

use crate::search_graph::{AvailableDepth, Cx, CycleHeads, PathKind, Stack, StackDepth};

#[derive_where(Debug, Clone, Copy; X: Cx)]
pub(super) struct GoalInfo<X: Cx> {
    pub input: X::Input,
    pub step_kind_from_parent: PathKind,
    pub available_depth: AvailableDepth,
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

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub(super) enum RebaseEntriesKind {
    Normal,
    Ambiguity,
    Overflow,
}

#[derive_where(Debug; X: Cx)]
pub(super) enum NodeKind<X: Cx> {
    InProgress {
        cycles_start: CycleId,
        step_results: Vec<X::Result>,
        rebase_entries_kind: Option<RebaseEntriesKind>,
    },
    Finished {
        step_results: Vec<X::Result>,
        final_result: X::Result,
        rebase_entries_kind: Option<RebaseEntriesKind>,
        encountered_overflow: bool,
        heads: CycleHeads,
    },
    CycleOnStack {
        entry_node_id: NodeId,
        result: X::Result,
    },
    ProvisionalCacheHit {
        entry_node_id: NodeId,
    },
}

#[derive_where(Debug; X: Cx)]
struct Node<X: Cx> {
    info: GoalInfo<X>,
    at_depth: StackDepth,
    parent: Option<(usize, NodeId)>,
    kind: NodeKind<X>,
}

#[derive_where(Debug, Default; X: Cx)]
pub(super) struct SearchTree<X: Cx> {
    nodes: IndexVec<NodeId, Node<X>>,
    cycles: IndexVec<CycleId, NodeId>,
}

impl<X: Cx> SearchTree<X> {
    pub(super) fn next_node_id(&self) -> NodeId {
        self.nodes.next_index()
    }

    pub(super) fn create_node(
        &mut self,
        stack: &Stack<X>,
        input: X::Input,
        step_kind_from_parent: PathKind,
        available_depth: AvailableDepth,
    ) -> NodeId {
        let info = GoalInfo { input, step_kind_from_parent, available_depth };
        let parent = stack.last().map(|e| {
            if let NodeKind::InProgress {
            cycles_start: _,
            step_results,
            rebase_entries_kind: _,
            } = &self.nodes[e.node_id].kind {
                let rerun = step_results.len();
                 (rerun, e.node_id)
            }else {
                panic!("unexpected node kind: {:?}", self.nodes[e.node_id]);
            }
        });
        self.nodes.push(Node {
            info,
            at_depth: stack.next_index(),
            parent,
            kind: NodeKind::InProgress {
                cycles_start: self.cycles.next_index(),
                step_results: Vec::new(),
                rebase_entries_kind: None,
            },
        })
    }

    pub(super) fn global_cache_hit(&mut self, node_id: NodeId) {
        debug_assert_eq!(node_id, self.nodes.last_index().unwrap());
        debug_assert!(matches!(self.nodes[node_id].kind, NodeKind::InProgress { .. }));
        self.nodes.pop();
    }

    pub(super) fn provisional_cache_hit(
        &mut self,
        node_id: NodeId,
        entry_node_id: NodeId,
    ) {
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

    pub(super) fn finish_evaluation(
        &mut self,
        node_id: NodeId,
        encountered_overflow: bool,
        heads: CycleHeads,
        final_result: X::Result,
    ) {
        let NodeKind::InProgress {
            cycles_start: _,
            step_results,
            rebase_entries_kind,
        } = &mut self.nodes[node_id].kind
        else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        };

        self.nodes[node_id].kind = NodeKind::Finished {
            encountered_overflow,
            heads,
            step_results: std::mem::take(step_results),
            final_result,
            rebase_entries_kind: *rebase_entries_kind,
        }
    }

    pub(super) fn get_cycle(&self, cycle_id: CycleId) -> NodeId {
        self.cycles[cycle_id]
    }

    pub(super) fn node_kind_raw(&self, node_id: NodeId) -> &NodeKind<X> {
        &self.nodes[node_id].kind
    }

    pub(super) fn current_rerun(&self, node_id: NodeId) -> (usize, X::Result) {
                if let NodeKind::InProgress {
            cycles_start: _,
            step_results,
            rebase_entries_kind: _,
        } = &self.nodes[node_id].kind
        {
            (step_results.len(), *step_results.last().unwrap())
        } else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        }
    }

    pub(super) fn result_matches(&self, prev: NodeId, new: NodeId) -> bool {
        match (&self.nodes[prev].kind, &self.nodes[new].kind) {
            (
                NodeKind::Finished {
                    step_results: _,
                    final_result: prev_result,
                    encountered_overflow: prev_overflow,
                    heads: prev_heads,
                    rebase_entries_kind: prev_rebase_entries_kind,
                },
                NodeKind::Finished {
                    step_results: _,
                    final_result: new_result,
                    encountered_overflow: new_overflow,
                    heads: new_heads,
                    rebase_entries_kind: new_rebase_entries_kind,
                },
            ) => {
                prev_result == new_result
                    && (*prev_overflow || !*new_overflow)
                    && prev_rebase_entries_kind == new_rebase_entries_kind
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

    pub(super) fn set_rebase_kind(&mut self, node_id: NodeId, rebase_kind: RebaseEntriesKind) {
        if let NodeKind::InProgress {
            cycles_start: _,
            step_results: _,
            rebase_entries_kind,
        } = &mut self.nodes[node_id].kind
        {
            let prev = rebase_entries_kind.replace(rebase_kind);
            debug_assert!(prev.is_none());
        } else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        }
    }

    pub(super) fn rerun_get_and_reset_cycles(
        &mut self,
        node_id: NodeId,
        provisional_result: X::Result,
    ) -> Range<CycleId> {
        if let NodeKind::InProgress {
            cycles_start,
            step_results,
            rebase_entries_kind,
        } = &mut self.nodes[node_id].kind
        {
            debug_assert!(rebase_entries_kind.is_none());
            let prev = *cycles_start;
            *cycles_start = self.cycles.next_index();
            step_results.push(provisional_result);
            prev..self.cycles.next_index()
        } else {
            panic!("unexpected node kind: {:?}", self.nodes[node_id]);
        }
    }

    pub(super) fn node_depends_on_head(&self, mut node_id: NodeId, head: StackDepth) -> bool {
        loop {
            let heads = self.get_heads(node_id);
            for (h, _) in heads.iter() {
                if h == head {
                    return true;
                } else if h > head {
                    while self.nodes[node_id].at_depth > h {
                        node_id = self.nodes[node_id].parent.unwrap().1;
                    }
                }
            }
            return false;
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
        mut node_id: NodeId,
    ) -> bool {
        loop {
            if node_id == cycle_head {
                return false;
            } else if was_reevaluated.contains(&node_id) {
                return true;
            } else {
                node_id = self.nodes[node_id].parent.unwrap().1;
            }
        }
    }

    /// Compute the list of parents of `node_id` until encountering the node
    /// `until`. We're excluding `until` and are including `node_id`.
    pub(super) fn compute_rev_stack(
        &self,
        mut node_id: NodeId,
        until: NodeId,
    ) -> Vec<RevStackEntry<X>> {
        let mut rev_stack = Vec::new();
        let mut rerun = 0usize;
        loop {
            if node_id == until {
                return rev_stack;
            }

            let node = &self.nodes[node_id];
            let NodeKind::Finished { step_results, .. } = &node.kind else {
                panic!("unexpected node kind: {:?}", self.nodes[node_id]);
            };
            let provisional_result = rerun.checked_sub(1).map(|prev| step_results[prev]);
            rev_stack.push(RevStackEntry { node_id, info: node.info, is_final_iteration: rerun == step_results.len(), provisional_result });
            (rerun, node_id) = node.parent.unwrap();
        }
    }
}

pub(super) struct RevStackEntry<X: Cx> {
    pub node_id: NodeId,
    pub info: GoalInfo<X>,
    pub is_final_iteration: bool,
    pub provisional_result: Option<X::Result>,
}