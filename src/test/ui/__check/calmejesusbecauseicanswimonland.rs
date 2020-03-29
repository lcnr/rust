#![feature(const_generics)]

trait Trait<const U: ()> {}

impl Trait<()> for () {}

fn main() {}
