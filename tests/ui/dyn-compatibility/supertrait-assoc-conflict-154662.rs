// Trust: Regression test for rust-lang#154662
// Check that conflicting supertrait associated type bounds are detected
// when constructing dyn trait types. When multiple supertraits constrain
// the same associated type with different concrete types, the resulting
// dyn type would be unsound since the associated type cannot simultaneously
// satisfy both constraints.

trait Base {
    type Assoc;
}

// Two traits that each fix Base::Assoc to a different type.
trait Left: Base<Assoc = u32> {}
trait Right: Base<Assoc = String> {}

// A trait inheriting both conflicting constraints.
trait Sub: Left + Right {}
//~^ ERROR type annotations needed: cannot satisfy `<Self as Base>::Assoc == u32`

// Constructing `dyn Sub` should be rejected because Left requires
// Base::Assoc = u32 while Right requires Base::Assoc = String.
fn takes_sub(_: &dyn Sub) {}

// Verify that non-conflicting supertrait bounds still work.
trait LeftOnly: Left {}
fn takes_left_only(_: &dyn LeftOnly<Assoc = u32>) {} // OK

fn main() {}
