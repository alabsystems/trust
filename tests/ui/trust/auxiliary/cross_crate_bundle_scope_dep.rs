//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! An ORDINARY dependency crate, compiled exactly the way `targo` compiles every
//! dependency unit: `-Ztrust-verify=off`, so **nothing in this file is verified**
//! and the compiler says so. It additionally carries `-Zalways-encode-mir`,
//! which is what `targo trust check|build` now injects on every unit so a
//! caller can read a dependency's BODY instead of only its signature.
//!
//! # Why this file exists
//!
//! Until it was written there was **no cross-crate `ensures` fixture anywhere in
//! the repository**. `tests/ui/trust/auxiliary/` held eleven aux crates and not
//! one declared a postcondition; the only fixture naming the postcondition-reuse
//! lane was `//@ ignore-test`. The most load-bearing claim in the composition
//! lane — that a foreign clause is never assumed — was asserted by comment only.
//!
//! The two functions below are a discriminating PAIR, and the discrimination is
//! the whole point:
//!
//! | fn | declared `ensures` | true of the body? |
//! |---|---|---|
//! | `clamp_index` | `result <= 31` | YES |
//! | `overclaims`  | `result <= 3`  | **NO** — `overclaims(10)` returns `10` |
//!
//! `overclaims` is not a mistake and must not be "fixed". It is the negative
//! control for the one failure mode that would make cross-crate bundling
//! unsound: if a caller ASSUMED a foreign `ensures` read out of rmeta instead of
//! re-deriving the callee's body, then a caller of `overclaims` would prove
//! `result <= 3` — a proposition that is false of the code. Because this crate
//! is compiled `-Ztrust-verify=off`, nothing anywhere has checked that clause;
//! it is a claim by the dependency's author, believed by no one.
//!
//! Both are deliberately non-generic and `Assert`-free (a compare and two
//! returns — no `/`, no `%`, no arithmetic). Assert-freedom matters: the
//! bundled-member Assert admission lane refuses any member with a guarded or
//! non-entry-prefix `Assert`, so an Assert-bearing witness would fail these
//! tests for a reason that has nothing to do with what they measure.
#![no_std]
#![crate_name = "xcbundle_dep"]

/// Truthful postcondition. Every value this returns really is `<= 31`.
pub fn clamp_index(k: u32) -> u32 ensures result <= 31 {
    if k > 31 {
        return 31;
    }
    k
}

/// FALSE postcondition, on purpose. `overclaims(10) == 10`, which is not `<= 3`.
/// Nothing has verified this clause — see the module comment.
pub fn overclaims(k: u32) -> u32 ensures result <= 3 {
    if k > 31 {
        return 31;
    }
    k
}
