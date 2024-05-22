//@ revisions: old next
//@[next] compile-flags: -Znext-solver=coherence
//@ check-pass

// A further minimization of issue-90662-projection-caching.rs

// This results causes some quite interesting search graph behavior.
//
// Proving `normalizes-to(<ServiceImpl as Provider<TestModule>Interface)`
// requires 3 fixpoint steps with the following provisional results:
//
// - ambiguous (default inductive cycle)
// - yes, with `NestedNormalizationGoals(TestModule: HasProvider<Foo<'static>>)`
// - yes, without any nested constraints
//
// This causes `TestModule: HasProvider<Foo<'static>>` to cycle in the second
// iteration, but not the third.

trait HasProvider<T: ?Sized> {}
trait Provider<M: ?Sized> {
    type Interface: ?Sized;
}

struct Service;
struct ServiceImpl;
struct Foo<'a>(&'a ());
impl<M: HasProvider<Foo<'static>> + ?Sized> Provider<M> for ServiceImpl {
    type Interface = Service;
}

struct TestModule;
impl HasProvider<Foo<'static>> for TestModule {}
impl HasProvider<<ServiceImpl as Provider<TestModule>>::Interface> for TestModule {}

fn main() {}