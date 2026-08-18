//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Admitting resolved std trait calls into the foreign-body lane must not
//! SHADOW a call the bridge already decides.
//!
//! Found by measurement, not by review. The first cut of the trait arm made
//! `a == b` on two `&[u8]` regress from passing to failing:
//!
//! ```text
//! error: an unproven panic-freedom obligation for a call to an absent callee
//!        `core::intrinsics::compare_bytes` ...
//! error: Trust strict verification failed for `probe_slice_eq`:
//!        1 obligation(s) were not fully verified
//! ```
//!
//! The chain is instructive. `<[u8] as PartialEq>::eq` resolves cleanly, its
//! body lowers cleanly, and so does `SlicePartialEq::equal_same_length`
//! underneath it — and then the whole thing bottoms out at
//! `core::intrinsics::compare_bytes`, which has no body for any lane to reach.
//! So bundling replaced a decided call with a fail-closed absent callee:
//! strictly less complete, and not one bit more sound, because
//! `slice_eq_total_builtin` was already the audited answer for that callee.
//!
//! The identity gate cannot catch this, and neither can the bridge's
//! name-keyed `total_no_panic_call_summary` — its `strip_generics` reduces
//! `<[u8] as core::cmp::PartialEq>::eq` to just `"eq"`, which fails the std-root
//! check. The decision lives in a TYPED receiver gate instead, keyed on the
//! lowered element type, and the compiler's collector has no lowered types to
//! consult. So the lane declines by TRAIT IDENTITY: the eight traits the bridge
//! resolves this way (`PartialEq`, `PartialOrd`, `Ord`, `Clone`, `Default`,
//! `Debug`, `Display`, `Hash`) are matched via `get_diagnostic_item` — a
//! registration `#[rustc_diagnostic_item]` reserves for std, so a user trait
//! merely NAMED `PartialEq` does not match and keeps the ordinary
//! obligation-bearing path.
//!
//! These probes all passed before the trait arm existed. They must keep passing:
//! this fixture is the one that notices if the lane starts eating decisions.

pub fn probe_slice_eq(a: &[u8], b: &[u8]) -> bool {
    a == b
}

pub fn probe_slice_ne(a: &[u8], b: &[u8]) -> bool {
    a != b
}

pub fn probe_array_eq(a: [u8; 4], b: [u8; 4]) -> bool {
    a == b
}

pub fn probe_ord_max(a: u8, b: u8) -> u8 {
    std::cmp::Ord::max(a, b)
}

pub fn probe_default_u8() -> u8 {
    <u8 as Default>::default()
}

pub fn probe_clone_u8(a: &u8) -> u8 {
    a.clone()
}

// Not a trait call at all, but the same regression class: the first cut also
// widened the identity gate's naming arguments for NON-trait callees, which
// pulled `core::num::<impl u8>::wrapping_shl` into the bundle and with it
// `unchecked_shl::precondition_check`, which has no body.
pub fn probe_wrapping_shl(a: u8, b: u32) -> u8 {
    a.wrapping_shl(b)
}

fn main() {}
