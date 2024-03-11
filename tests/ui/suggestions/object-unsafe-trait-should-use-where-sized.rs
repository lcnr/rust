// FIXME(rustfix): this ends up changing `foo` to `foo(&self&self)` because the
// same machine applicable error is emitted twice.
//@no-rustfix
trait Trait {
    fn foo() where Self: Other, { }
    fn bar(self: ()) {} //~ ERROR invalid `self` parameter type
}

fn bar(x: &dyn Trait) {}
//~^ ERROR the trait `Trait` cannot be made into an object
//~| ERROR the trait `Trait` cannot be made into an object
trait Other {}

fn main() {}
