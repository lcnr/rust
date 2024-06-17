use crate::*;

impl<X: Cx> NestedGoals<X> {
    fn is_empty(&self) -> bool {
        self.nested_goals.is_empty()
    }
}

impl<X: Delegate<D>, D> SearchGraph<X, D> {
    #[allow(rustc::potential_query_instability)]
    pub(super) fn check_invariants(&self) {
        if !cfg!(debug_assertions) {
            return;
        }

        let SearchGraph { mode: _, stack, _marker } = self;

        for (depth, entry) in stack.iter_enumerated() {
            let StackEntry {
                input,
                available_depth: _,
                reached_depth: _,
                ref heads,
                encountered_overflow: _,
                has_been_used: _,
                ref nested_goals,
                provisional_result: _,
            } = *entry;

            if let Some(head) = heads.lowest_cycle_head() {
                let mut current_root = head;
                while let Some(parent) = stack[current_root].heads.lowest_cycle_head() {
                    current_root = parent;
                }

                for entry in &stack.raw[current_root.index()..depth.index()] {
                    assert!(entry.nested_goals.contains(input));
                }
            }

            if !nested_goals.is_empty() {
                for entry in stack.iter().take(depth.as_usize()) {
                    assert!(!nested_goals.contains(entry.input));
                }
            }
        }
    }
}
