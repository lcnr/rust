#![feature(array_windows, array_chunks)]

use std::slice::*;

struct Test<const N: usize> {
    a: ArrayChunks<'static, u32, 0>, //~ ERROR expected a non zero
    b: ArrayChunks<'static, u32, N>, //~ ERROR expected a concrete

    c: ArrayChunksMut<'static, u32, 0>, //~ ERROR expected a non zero
    d: ArrayChunksMut<'static, u32, N>, //~ ERROR expected a concrete

    e: ArrayWindows<'static, u32, 0>, //~ ERROR expected a non zero
    f: ArrayWindows<'static, u32, N>, //~ ERROR expected a concrete
}

fn main() {
    let _: Test<17>;
}