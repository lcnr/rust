// revisions: trait_bound trait_bound_next projection_bound projection_bound_next
//[trait_bound_next] compile-flags: -Znext-solver
//[projection_bound_next] compile-flagss: -Znext-solver
//[trait_bound] check-pass
trait Trait<'a, 'b> {
    type Assoc;
}

trait TraitBound<'b> {}
impl<'b, T: for<'a> Trait<'a, 'b>> TraitBound<'b> for T {}

trait ProjectionBound<'b> {}
impl<'b, T: for<'a> Trait<'a, 'b, Assoc = usize>> ProjectionBound<'b> for T {}

impl<'a, T> Trait<'a, 'static> for T {
    type Assoc = usize;
}

fn trait_bound<'b, T: TraitBound<'b>>() {}
fn projection_bound<'b, T: ProjectionBound<'b>>() {}

#[cfg(any(trait_bound, trait_bound_next))]
fn satisfies_trait_bound<T: for<'b> Trait<'static, 'b>>() {
    trait_bound::<T>()
    //[trait_bound_next]~^ ERROR the trait bound `T: TraitBound<'_>` is not satisfied
}

#[cfg(any(projection_bound, projection_bound_next))]
fn satisfies_projection_bound<T: for<'b> Trait<'static, 'b, Assoc = usize>>() {
    projection_bound::<T>()
    //[projection_bound]~^ ERROR mismatched types
    //[projection_bound_next]~^^ ERROR mismatched types
}

fn main() {}