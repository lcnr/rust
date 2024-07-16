use super::*;

impl<D: Delegate<Cx = X>, X: Cx> SearchGraph<D> {
    #[allow(rustc::potential_query_instability)]
    pub(super) fn check_invariants(&self) {
        if !cfg!(debug_assertions) {
            return;
        }/*

        let SearchGraph { mode: _, stack, provisional_cache, _marker } = self;
        if stack.is_empty() {
            assert!(provisional_cache.is_empty());
        }

        for (depth, entry) in stack.iter_enumerated() {
            let StackEntry {
                input,
                available_depth: _,
                reached_depth: _,
                ref cycle_heads,
                encountered_overflow: _,
                has_been_used: _,
                ref nested_goals,
                provisional_result: _,
            } = *entry;
            let cache_entry = provisional_cache.get(&entry.input).unwrap();
            assert_eq!(cache_entry.stack_depth, Some(depth));
            for (&head, _usage_kind) in cycle_heads.heads.iter() {
                assert_ne!(head, input);
                let stack_depth = self.provisional_cache.get(&head).unwrap().stack_depth.unwrap();
                // assert_ne!(stack[stack_depth].has_been_used, None);
            }

            if !nested_goals.nested_goals.is_empty() {
                for entry in stack.iter().take(depth.as_usize()) {
                    assert_eq!(nested_goals.nested_goals.get(&entry.input), None);
                }
            }
        }

        for (&input, entry) in &self.provisional_cache {
            let ProvisionalCacheEntry { stack_depth, detached_entries } = entry;
            assert!(stack_depth.is_some() || !detached_entries.is_empty());

            if let &Some(stack_depth) = stack_depth {
                assert_eq!(stack[stack_depth].input, input);
            }
        }*/
    }
}
