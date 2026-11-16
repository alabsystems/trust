//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! Trust: 2026-09-15 — THE PRECISION CONTROL for
//! `escaped_local_modulo_divisor_stays_closed.rs`.
//!
//! That file pins that a local whose `&mut` alias escapes can no longer have its
//! value RESOLVED (`local_defs::body_unique_value_def` refuses the
//! `LocalWrite::Escape` channel), because a store through the alias names a place
//! no scan keyed on the local can see.
//!
//! THIS file is the other half, and without it the refusal is unfalsifiable: the
//! SAME modulo-divisor bound, with NO alias anywhere, must still resolve and
//! still prove under the strictest policy. If this file ever starts failing, the
//! escape refusal has grown from a closed hole into a capability loss and must be
//! re-adjudicated with a measurement — it is not licensed to cost an unaliased
//! local.
//!
//! MEASURED on the pristine prebuilt stage1 driver, 2026-09-15 (i.e. BEFORE the
//! refusal landed): rc = 0, "2 proved, 0 failed, 0 unknown, 0 timed out, 0
//! runtime-checked out of 2 obligation(s)". The refusal must leave that
//! untouched, because `m` here is never borrowed at all — a local with no
//! `Rvalue::Ref { mutable: true }` and no `Rvalue::AddressOf` rooted at it is not
//! on the escape channel (`trust_types::Statement::escapes_local`), so the
//! resolver's scan reaches exactly the same single `Assign` it always did.
//!
//! `n % 4 < 4` holds for every `n: usize`, so `b[n % m]` is in range for every
//! input and there is no runtime oracle to disagree with.

#[inline(never)]
pub fn unaliased(n: usize, b: &[u8; 4]) -> u8 {
    let m = 4usize;
    b[n % m]
}
