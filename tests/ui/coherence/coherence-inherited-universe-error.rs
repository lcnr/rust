// Test that impls which are only distict due to
// universe errors are accepted. This was previously
// not the case.

// check-pass

struct Foo<T> {
    t: T,
}

impl Foo<for<'a, 'b> fn(&'a u8, &'b u8) -> &'a u8> {
    fn method1(&self) {}
}

impl Foo<for<'a> fn(&'a u8, &'a u8) -> &'a u8> {
    fn method1(&self) {}
}

fn main() {}
