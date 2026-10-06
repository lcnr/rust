//@ revisions: rpass
#![feature(generic_const_exprs)]
//~^ WARN `feature(generic_const_exprs)` is not supported with the next-generation trait solver
#![allow(incomplete_features)]

struct Foo;
impl<'a> std::ops::Add<&'a Foo> for Foo
where
    [(); 0 + 0]: Sized,
{
    type Output = ();
    fn add(self, _: &Foo) -> Self::Output {
        loop {}
    }
}

fn main() {}
