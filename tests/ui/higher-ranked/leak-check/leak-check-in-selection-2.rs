// revisions: old next
//[next] compile-flags: -Znext-solver
//[old] check-pass
trait Trait<T, U> {}

impl<'a> Trait<&'a str, &'a str> for () {}
impl<'a> Trait<&'a str, String> for () {}

fn impls_trait<T: for<'a> Trait<&'a str, U>, U>() {}

fn main() {
    impls_trait::<(), _>();
    //[next]~^ ERROR type annotations needed
}
