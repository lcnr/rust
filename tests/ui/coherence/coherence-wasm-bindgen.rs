// Capture a coherence pattern from wasm-bindgen that we discovered as part of
// future-compatibility warning #56105. This pattern relies on universe
// errors impacting selection and is something we want to support.

// check-pass

trait IntoWasmAbi {
    fn some_method(&self) {}
}

trait FromWasmAbi {}
trait RefFromWasmAbi {}
trait ReturnWasmAbi {}

impl<'a, 'b, A, R> IntoWasmAbi for &'a (dyn Fn(A) -> R + 'b)
where
    A: FromWasmAbi,
    R: ReturnWasmAbi,
{
}

// Explicitly writing the bound lifetime.
impl<'a, 'b, A, R> IntoWasmAbi for &'a (dyn for<'x> Fn(&'x A) -> R + 'b)
where
    A: RefFromWasmAbi,
    R: ReturnWasmAbi,
{
}

fn main() {}
