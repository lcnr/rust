#![feature(array_windows, array_chunks)]

use std::slice::*;

fn tester<const N: usize>() {
    let mut s = [0, 1, 2];
    s.array_chunks::<0>(); //~ ERROR expected a non zero
    s.array_chunks::<N>(); //~ ERROR expected a concrete

    s.array_chunks_mut::<0>(); //~ ERROR expected a non zero
    s.array_chunks_mut::<N>(); //~ ERROR expected a concrete

    s.array_windows::<0>(); //~ ERROR expected a non zero
    s.array_windows::<N>(); //~ ERROR expected a concrete
}

fn main() {
    tester::<3>();
}