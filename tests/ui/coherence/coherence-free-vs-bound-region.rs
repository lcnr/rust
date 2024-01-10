// Capture a coherence pattern from wasm-bindgen that we discovered as part of
// future-compatibility warning #56105. This pattern pattern relies on coherence
// considering implementations to not overlap if there are universe errors.
//
// Key distinction: we are implementing once for `A` (take ownership) and one
// for `&A` (borrow).
//
// c.f. #56105

// check-pass

trait TheTrait {}

impl<'a> TheTrait for fn(&'a u8) {}
impl TheTrait for fn(&u8) {}

fn main() {}
