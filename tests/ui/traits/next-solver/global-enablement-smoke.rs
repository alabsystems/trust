// Smoke test: basic compilation under -Znext-solver=globally.
// Exercises trait resolution, associated types, and opaque types
// to verify Phase 0 assertion removal allows clean compilation.
//
// Trust: next-solver Phase 0 regression test (#868)
//@ compile-flags: -Znext-solver=globally
//@ check-pass

trait Greet {
    type Name;
    fn greet(&self) -> String;
}

struct World;

impl Greet for World {
    type Name = &'static str;
    fn greet(&self) -> String {
        String::from("Hello, world!")
    }
}

fn generic_greet<T: Greet>(val: &T) -> String {
    val.greet()
}

fn returns_impl_greet() -> impl Greet<Name = &'static str> {
    World
}

fn use_opaque() -> String {
    let w = returns_impl_greet();
    generic_greet(&w)
}

fn main() {
    let w = World;
    assert_eq!(w.greet(), "Hello, world!");
    assert_eq!(generic_greet(&w), "Hello, world!");
    assert_eq!(use_opaque(), "Hello, world!");
}
