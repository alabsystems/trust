//@ known-bug: #859
//@ check-pass
// Trust: Regression test for rust-lang#84533
// "HRTB-trait-objects associated type validity not checked"
//
// When a trait has an associated type with bounds (e.g., `type Assoc: Clone`),
// creating a trait object with a concrete type that violates those bounds
// must be rejected. Previously this was only checked during trait object
// confirmation (when methods were dispatched), not during type well-formedness
// checking.

trait HasCloneAssoc {
    type Assoc: Clone;
}

struct NotClone;

// Should be rejected: NotClone does not implement Clone
fn bad_simple() -> Box<dyn HasCloneAssoc<Assoc = NotClone>> {
    // [pending soundness check] ERROR the trait bound `NotClone: Clone` is not satisfied
    todo!()
}

// Should be accepted: String implements Clone
fn good_simple() -> Box<dyn HasCloneAssoc<Assoc = String>> {
    todo!()
}

// Multiple bounds on associated type
trait HasMultiBoundAssoc {
    type Assoc: Clone + std::fmt::Debug;
}

// Should be rejected: NotClone satisfies neither Clone nor Debug
fn bad_multi() -> Box<dyn HasMultiBoundAssoc<Assoc = NotClone>> {
    // [pending soundness check] ERROR the trait bound `NotClone: Clone` is not satisfied
    todo!()
}

fn main() {}
