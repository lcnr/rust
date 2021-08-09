// check-pass
// aux-build:aux.rs

extern crate aux;

fn tester<const N: usize>() {
    aux::bar::<u32, 1, 0, 10>();
    let ([_, _], [_], [_, _, _]) = aux::Foo::<3>.foo();
}

fn main() {
    tester::<3>();
}
