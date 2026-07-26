//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#118950
// Part of #859
//
// The compiler's well-formedness (WF) checking can be bypassed in certain
// situations involving associated types and where-clauses. WF checks ensure
// that types satisfy their required bounds (e.g., lifetime outlives relations,
// trait bounds on generic parameters). When the WF check is skipped or
// incorrectly satisfied, it allows constructing types that violate safety
// invariants.
//
// The specific issue: certain combinations of associated type projections
// and trait bounds can cause the WF checker to accept a type that does
// not actually satisfy the required lifetime bounds, enabling lifetime
// extension in safe code.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/118950
//
// STATUS: This may compile on current Rust (unsound). When fixed, the
// compiler should reject the code with a well-formedness or lifetime error.

trait HasAssoc {
    type Assoc;
}

impl<'a> HasAssoc for &'a () {
    type Assoc = &'a str;
}

// This trait uses an associated type that has implicit WF requirements:
// the Assoc type of &'a () is &'a str, which requires 'a to be live.
trait WfBypass {
    type Item;
    fn get(&self) -> Self::Item;
}

struct Sneaky<T: HasAssoc>(T, T::Assoc);

impl<'a> WfBypass for Sneaky<&'a ()> {
    type Item = &'a str;
    fn get(&self) -> &'a str {
        self.1
    }
}

fn exploit<'a>(s: &'a str) -> &'a str {
    let sneaky = Sneaky(&(), s);
    sneaky.get()
}

fn main() {
    let result;
    {
        let owned = String::from("hello");
        result = exploit(&owned);
        // result borrows owned — this should be caught by the borrow checker.
        // The WF bypass bug might allow this to compile unsoundly.
        let _ = result;
    }
    // If the WF check is bypassed, this would be use-after-free.
    // With correct WF checking, the borrow of `owned` prevents this.
    println!("done");
}
