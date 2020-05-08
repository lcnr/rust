// aux-build:crate_a1.rs
// aux-build:crate_a2.rs

// FIXME(#71954) Paths to extern crates contain the scope of their first appearance.
// If we were to remove this function, `crate_a2` would have the path `inner::a::Bar`
// while `crate_a1` would use `a::Bar`.
pub fn hack() {
    {
        extern crate crate_a1 as a;
    }
    {
        extern crate crate_a2 as a;
    }
}



mod inner {
    extern crate crate_a2 as a;
    pub struct B<T: a::Bar>(T);
    //~^ NOTE required by this bound
    //~| NOTE required by this bound
}

extern crate crate_a1 as a;
pub struct C<T: a::Bar>(inner::B<T>);
//~^ ERROR the trait bound
//~| HELP consider further restricting
//~| NOTE not implemented for `T`
//~| NOTE mismatched crates

trait Bar {}

// Do not warn if the traits have the same name but
// differently named crates.
pub struct D<T: Bar>(inner::B<T>);
//~^ ERROR the trait bound
//~| HELP consider further restricting
//~| NOTE not implemented for `T`

fn main() {}
