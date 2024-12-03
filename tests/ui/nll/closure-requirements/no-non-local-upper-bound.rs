// This previously ICE'd as it failed to find a non-local universal
// region which is outlived by the `lower_bound` of a type outlives
// when promoting closure requirements. Regression test for #122704.
trait IsStatic: 'static {}

impl<T: 'static> IsStatic for T {}

fn foo<T>(x: Box<T>) -> Box<dyn for<'a> FnOnce(&'a ()) -> Box<dyn IsStatic + 'a>> {
    Box::new(move |_| x)
    //~^ ERROR the parameter type `T` may not live long enough
    //~| ERROR the parameter type `T` may not live long enough
    //~| ERROR the parameter type `T` may not live long enough
}

fn main() {}
