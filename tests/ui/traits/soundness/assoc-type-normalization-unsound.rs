// Trust: regression test for rust-lang#114936
// Part of #859
//
// Associated type normalization unsoundness. The compiler can normalize
// an associated type projection in a context where the trait bound is
// only conditionally satisfied, allowing a type mismatch that functions
// as a transmute.
//
// The core issue: when the compiler sees `<T as Trait>::Assoc` and finds
// a unique impl, it normalizes eagerly even when the impl's where-clauses
// are not fully proven. This can be exploited with a blanket impl and
// a more specific impl that provides a different associated type, creating
// a type confusion path.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/114936
//
// STATUS: The compiler rejects this (E0308 in `inner`, E0271 at the call
// site) — the unsound normalization is not accepted.

trait Trait {
    type Assoc;
}

// Blanket impl: for any T, Assoc = T
impl<T> Trait for T {
    type Assoc = T;
}

// The exploit: use a where clause that is trivially true for all types
// but forces the compiler through a normalization path that confuses
// the associated type resolution.
fn transmute_via_normalization<T, U>(t: T) -> U
where
    // This bound is always true (blanket impl), but the normalization
    // of <T as Trait>::Assoc goes through a path that can confuse T and U.
    T: Trait<Assoc = U>,
{
    // The compiler has been told T::Assoc = U via the where clause,
    // and the blanket impl says T::Assoc = T, so it concludes T = U.
    // But this is only valid if T actually equals U — the compiler
    // doesn't enforce this, allowing the transmute.
    fn inner<T: Trait>(t: T) -> T::Assoc {
        t //~ ERROR mismatched types
    }
    inner(t)
}

fn main() {
    // If the compiler accepts this, it's a transmute from u64 to f64.
    // The where clause `u64: Trait<Assoc = f64>` contradicts the blanket
    // impl's `Assoc = u64`, but the compiler may accept it anyway.
    let x: u64 = 0x4048F5C28F5C28F6; // bit pattern of 3.14 as f64
    // Note: this particular instantiation may or may not compile depending
    // on how the trait solver handles the contradictory bounds. The test
    // documents the class of unsoundness.
    let _y: f64 = transmute_via_normalization::<u64, f64>(x);
    //~^ ERROR type mismatch resolving `<u64 as Trait>::Assoc == f64`
}
