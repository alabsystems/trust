//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! The compositional spelling on the EXACT arithmetic of the known-good
//! `s1c_arith_true_ensures_proves`: same `u64` increment, same precondition
//! excluding the single wrap point, same Machine{64} lane — only the ensures
//! is written `bump(x)` instead of `x + 1`.
//!
//! Held separately from the `/` sibling on purpose. If one of the two proves
//! and the other does not, the difference is the OPERATOR's fragment and not
//! the inline, and the pair says which.
//!
//! `bump` carries its own `requires` so that its unguarded `v + 1` is not an
//! open overflow obligation in its own right — the fixture must fail only for
//! reasons about the inline. Note the inline does NOT assume that
//! precondition: it reproduces `bump`'s EXPRESSION over the actual, which is
//! exactly what the caller would have written by hand (see
//! `lower_inlined_call`). The caller's own `requires` is what excludes the
//! wrap point here.
pub fn bump(v: u64) -> u64 requires v < 18446744073709551615 { v + 1 }

pub fn inc(x: u64) -> u64
    requires x < 18446744073709551615
    ensures result == bump(x)
{
    x + 1
}
