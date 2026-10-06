//@ revisions: rpass
#![feature(generic_const_exprs)]
//~^ WARN `feature(generic_const_exprs)` is not supported with the next-generation trait solver
#![allow(incomplete_features)]

pub struct Ref<'a, const NUM: usize>(&'a i32);

impl<'a, const NUM: usize> Ref<'a, NUM> {
    pub fn foo<const A: usize>(r: Ref<'a, A>) -> Self
    where
        ([(); NUM - A], [(); A - NUM]): Sized,
    {
        Self::bar(r)
    }

    pub fn bar<const A: usize>(r: Ref<'a, A>) -> Self
    where
        ([(); NUM - A], [(); A - NUM]): Sized,
    {
        Self(r.0)
    }
}

fn main() {}
