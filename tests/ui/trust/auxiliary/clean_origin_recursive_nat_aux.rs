//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "rlib"]

//! Exporting half of the C11 cross-crate structural-induction control.
//!
//! `keep_rec` is a genuine `Nat.rec` fold. Its constructor step rebuilds the
//! input, so it is extensionally the identity but not definitionally equal to
//! `fun n => n` for a symbolic `n`. The compiler may emit the ordinary bignum
//! projection only after the closed axiom-free induction proof succeeds. Its
//! rmeta digest must then carry both `StructuralInduction` and
//! `UnboundedExact`; v1 had no honest representation for either fact.

pub mod m {
    clean {
        def keep_rec : Nat -> Nat
          | 0 => 0
          | n + 1 => Nat.succ (keep_rec n)
    }
}
