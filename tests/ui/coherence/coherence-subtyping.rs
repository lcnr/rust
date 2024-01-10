// Test that impls whose self types are subtypes of each other and
// which only differ due to a universe error are considered disjoint
// by coherence.

// check-pass

trait TheTrait {
    fn foo(&self) {}
}

impl TheTrait for for<'a, 'b> fn(&'a u8, &'b u8) -> &'a u8 {}

impl TheTrait for for<'a> fn(&'a u8, &'a u8) -> &'a u8 {}

fn main() {}
