// aux-build:aux.rs

extern crate aux;

fn tester<const N: u8>() {
    aux::bar::<u32, 0, 0, 10>(); //~ ERROR expected a non zero value
    aux::bar::<u8, N, 0, 13>(); //~ERROR expected a concrete const
    let ([_, _], [], []) = aux::Foo::<3>.foo();
    //~^ ERROR expected a non zero value
    //~| ERROR expected a non zero value
}

fn main() {
    tester::<3>();
}
