#![feature(rustc_attrs)]

pub struct Foo<const N: usize>;

impl<const N: usize> Foo<N> {
    #[rustc_generic_arg_non_zero(0, 1, 2)]
    pub fn foo<const A: usize, const B: usize, const C: usize>(&self) -> ([u8; A], [u8; B], [u16; C]) {
        todo!()
    }
}

#[rustc_generic_arg_non_zero(1, 3)]
pub fn bar<A, const B: u8, const C: usize, const D: i128>() {}