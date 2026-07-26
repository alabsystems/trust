// Regression test for ICE "unexpected bad final type in method autoderef"
// Part of #866 (tRust)
//
// When autoderef hits the recursion limit and obligation resolution produces
// a concrete type (not an inference variable or error), the compiler should
// report "method not found" instead of triggering an ICE.

use std::ops::Deref;

struct Wrap<T>(T);

impl<T> Deref for Wrap<T> {
    type Target = Wrap<Wrap<T>>;

    fn deref(&self) -> &Self::Target {
        todo!()
    }
}

fn main() {
    let w = Wrap(0u32);
    w.nonexistent_method();
    //~^ ERROR reached the recursion limit while auto-dereferencing
    //~| ERROR no method named `nonexistent_method` found
}
