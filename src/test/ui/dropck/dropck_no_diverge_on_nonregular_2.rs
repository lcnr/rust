// check-pass
//
// Issue 22443: Reject code using non-regular types that would
// otherwise cause dropck to loop infinitely.
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
    // Bug report said Digit before Box would infinite loop (versus
    // Digit after Box; see dropck_no_diverge_on_nonregular_1).
    Deep(
        Digit<T>,
        Box<FingerTree<Node<T>>>,
        )
}

fn main() {
    let ft =
        FingerTree::Single(1);
}
