use crate::*;
use itertools::Itertools;

impl<X: Cx> NestedGoals<X> {
    fn contains(&self, input: X::Input) -> bool {
        self.nested_goals.contains(&input)
    }

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

        let SearchGraph { mode: _, stack, provisional_cache, detached_entries_stash, _marker } =
            self;
        if stack.is_empty() {
            assert!(provisional_cache.is_empty());
        }

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
            let cache_entry = provisional_cache.get(&entry.input).unwrap();
            assert_eq!(cache_entry.stack_depth, Some(depth));

            for (head, usage_kind) in heads.iter() {
                assert!(head < depth);
                assert!(stack[head].has_been_used.unwrap().contains(usage_kind));
            }

            if let Some(lowest_head) = heads.lowest_cycle_head() {
                let mut current_root = lowest_head;
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

        for (&input, entry) in &self.provisional_cache {
            let ProvisionalCacheEntry { stack_depth, with_coinductive_stack, with_inductive_stack } =
                entry;
            assert!(
                stack_depth.is_some()
                    || with_coinductive_stack.is_some()
                    || with_inductive_stack.is_some()
            );

            if let &Some(stack_depth) = stack_depth {
                assert_eq!(stack[stack_depth].input, input);
            }
        }

        for (&input, entries) in detached_entries_stash {
            for comb in entries.iter().combinations(2) {
                assert_ne!(comb[0], comb[1]);
            }

            for entry in entries {
                let StashedDetachedEntry {
                    heads,
                    nested_goals: _,
                    is_coinductive: _,
                    input: _,
                    result: _,
                } = entry;
                assert_eq!(input, heads.last().unwrap().input);
            }
        }
    }
}
