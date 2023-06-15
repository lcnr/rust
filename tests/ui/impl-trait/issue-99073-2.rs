use std::fmt::Display;

fn main() {
    test("hi", true);
}

fn test<T: Display>(t: T, recurse: bool) -> impl Display {
    let f = || {
        let i: u32 = test::<i32>(-1, false);
        //~^ ERROR non-defining opaque type use in defining scope
        println!("{i}");
    };
    if recurse {
        f();
    }
    t
}
