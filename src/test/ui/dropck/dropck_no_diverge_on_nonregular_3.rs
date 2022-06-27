// check-pass
//
// Issue 22443: Reject code using non-regular types that would
// otherwise cause dropck to loop infinitely.
//
// This version is just checking that we still sanely handle a trivial
// wrapper around the non-regular type. (It also demonstrates how the
// error messages will report different types depending on which type
// dropck is analyzing.)
//
// This only emits an error during codegen as we don't call
// `dropck_outlives` for locals which don't contain regions
// local to the current function.

use std::marker::PhantomData;

struct Digit<T> {
    elem: T
}

struct Node<T:'static> { m: PhantomData<&'static T> }

enum FingerTree<T:'static> {
    Single(T),
    // According to the bug report, Digit before Box would infinite loop.
    Deep(
        Digit<T>,
        Box<FingerTree<Node<T>>>,
        )
}

enum Wrapper<T:'static> {
    Simple,
    Other(FingerTree<T>),
}

fn main() {
    let w =
        Some(Wrapper::Simple::<u32>);
}
