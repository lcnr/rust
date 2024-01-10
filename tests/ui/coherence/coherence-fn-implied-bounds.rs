// Test that our leak-check is not smart enough to take implied bounds
// into account (yet). Here we have two types that look like they
// should not be equivalent, but because of the rules on implied
// bounds we ought to know that, in fact, `'a = 'b` must always hold,
// and hence they are.
//
// Rustc can't figure this out and hence it accepts the impls. This is
// a bit unfortunate as we will error here if we ever consider implied bounds
// when equating higher ranked types.

// check-pass

trait Trait {}

impl Trait for for<'a, 'b> fn(&'a &'b u32, &'b &'a u32) -> &'b u32 {}
impl Trait for for<'c> fn(&'c &'c u32, &'c &'c u32) -> &'c u32 {}

fn main() {}
