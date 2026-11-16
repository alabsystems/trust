//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-RTC): the shims the `#[track_caller]` reify arm must NOT admit.
//!
//! `Reify(instance shim)` POOLS structurally unrelated shapes — measured, a
//! `Shim(ShimKind::Clone)` wears the identical string — so the new arm is an
//! affirmative allow-list rather than a widening, and this file is what says so.
//! Each body below reaches `resolve_reify_target` with an `InstanceKind` that is not
//! an `Item` requiring a caller location, and each must keep refusing.
//!
//! Delete any one of gates G1-G7 and one of these stops erroring. Nothing else in the
//! tree would say so: the corpus sweep counts bodies that become CLEAN, and a shim
//! wrongly admitted here becomes clean, which reads as a WIN.

#![allow(dead_code)]

pub trait T {
    fn m(&self) -> i32;
}

pub struct A;

impl T for A {
    fn m(&self) -> i32 {
        1
    }
}

// R1 — the CLONE shim. `<(i32, i32) as Clone>::clone` resolves to
// `Shim(ShimKind::Clone)`, which is compiler-synthesized and has no user body to name
// with a `Constant::FnDef`. It wears the SAME tag the admitted shape wore, which is
// exactly why G3 requires the underlying resolution to be an `Item`.
pub fn clone_shim() -> fn(&(i32, i32)) -> (i32, i32) {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    <(i32, i32) as Clone>::clone
}

// R2 — an ARRAY clone, which is NOT a shim and must stay ADMITTED. It is here as the
// discriminating control: `<[u8; 4] as Clone>::clone` resolves to a real
// `InstanceKind::Item` (arrays have a builtin impl), so a regression that closes the
// whole `Shim` match arm rather than just the non-`Reify` variants would leave R1
// erroring and this body erroring too — and without this line the file could not tell
// those two failures apart.
//
// The DROP-GLUE case is deliberately NOT pinned here: `std::mem::drop::<T>` is an
// ordinary `DefKind::Fn` with an empty body, not a `ShimKind::DropGlue`, and it reifies
// clean today. An earlier draft of this file asserted it as a refusal and was wrong —
// measured, it does not refuse. Pinning a refusal that does not happen is worse than
// pinning nothing: it reads as coverage of a case nobody has actually tested.
pub fn array_clone_still_admits() -> fn(&[u8; 4]) -> [u8; 4] {
    <[u8; 4] as Clone>::clone
}
