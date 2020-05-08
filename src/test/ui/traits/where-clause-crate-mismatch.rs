// aux-build:crate_a1.rs
// aux-build:crate_a2.rs

// Issue 22750
// This tests the extra help message reported when a trait bound
// is not met but the struct implements a trait with the same path.
mod inner {
    extern crate crate_a2 as a;
    pub struct B<T: a::Foo>(T);
}

extern crate crate_a1 as a;
pub struct C<T: a::Foo>(B<T>);

fn main() {}
