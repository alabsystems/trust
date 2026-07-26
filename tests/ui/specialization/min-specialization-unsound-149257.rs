// Regression test for rust-lang#149257: min_specialization unsoundness
// where a specializing impl can be selected even though its where-clauses
// are not provably always applicable, leading to type confusion.
//
// The "always applicable" invariant requires that for every type satisfying
// the specializing impl's bounds, the parent impl ALSO applies. When this
// invariant is violated, removing the specializing impl could break code
// that was using it, which means the compiler might select the wrong impl
// and produce unsound behavior.
//
// Trust: this test ensures our root-cause fix in the specializes() function
// correctly rejects unsound specializations where the parent impl's generic
// parameters cannot be fully resolved during the implication check.

#![feature(min_specialization)]
#![feature(rustc_attrs)]

// Test 1: Cannot specialize on a non-always-applicable trait
trait NotAlwaysApplicable {}

trait MyTrait {
    type Output;
}

impl<T> MyTrait for T {
    default type Output = (); //~ ERROR specialization is experimental
}

impl<T: NotAlwaysApplicable> MyTrait for T {
    //~^ ERROR cannot specialize on trait `NotAlwaysApplicable`
    type Output = T;
}

// Test 2: Cannot specialize with projection predicates that aren't in the parent
trait Assoc {
    type Item;
}

trait Dispatch {
    fn dispatch();
}

impl<T> Dispatch for T {
    default fn dispatch() {}
}

impl<T: Assoc<Item = u32>> Dispatch for T {
    //~^ ERROR cannot specialize on trait `Assoc`
    //~| ERROR cannot specialize on associated type
    fn dispatch() {}
}

fn main() {}
