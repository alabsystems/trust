//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **L2a: `iN::checked_{add,sub,mul}` IS PANIC-FREE in the native lane.**
//!
//! rustc's extractor stamps a direct call to the signed primitive
//! `checked_add` / `checked_sub` / `checked_mul` with
//! `@trust-rustc-checked-primitive-method::` only after `TyCtxt` confirms the
//! exact `core` inherent method and its `(I, I) -> Option<I>` signature
//! (`tcx_marked_signed_checked_primitive_path`). Before L2a only E6 and the
//! facet scans read that stamp; the trust-ir bridge had no arm for it, so
//! every such call fell to the absent-callee arm and charged a
//! `[trust-absent-callee-assumption] … may panic` row that could never be
//! discharged (17 rows on a3d-kernel, ALab survey 2026-10-07).
//!
//! The bridge now lowers the stamped call as total — no panic row — and havocs
//! the `Option` result (`FreshSymbolicHavoc`): no value fact is granted, so a
//! caller that relies on WHICH variant comes back still has to prove it.
//!
//! `check-pass` under `-Ztrust-policy=certify`, under which any runtime-checked
//! row is a build error, so this fixture states that none of the calls below
//! carries one. A body whose ONLY call is the stamped method has zero rows and
//! prints no note; the gate parity that makes it `proved` (`no_obligations`)
//! rather than an `unknown` native-verification-gap row is pinned unit-level
//! (`extractor_stamped_checked_family_is_lane_consistent_and_fail_closed`).
//! The `*_indexed` twins carry one real bounds row each, so their NOTE pins
//! state the verdict here: proved, with no unknown and no runtime-checked row. The other direction (an UNSTAMPED local `checked_add`
//! that panics keeps its row) is `checked_primitive_unmarked_local_keeps_row.rs`;
//! the forged-metadata, width and arity refusals are unit-level in
//! `trust_ir_bridge` (`test_checked_primitive_marker_metadata_and_shape_fail_closed`).

pub fn add_i64(a: i64, b: i64) -> Option<i64> {
    a.checked_add(b)
}

pub fn sub_i64(a: i64, b: i64) -> Option<i64> {
    a.checked_sub(b)
}

pub fn mul_i64(a: i64, b: i64) -> Option<i64> {
    a.checked_mul(b)
}

pub fn add_i128(a: i128, b: i128) -> Option<i128> {
    a.checked_add(b)
}

pub fn sub_i128(a: i128, b: i128) -> Option<i128> {
    a.checked_sub(b)
}

pub fn mul_i128(a: i128, b: i128) -> Option<i128> {
    a.checked_mul(b)
}

// A narrow width: the stamp covers every signed carrier `i8`..`i128`.
pub fn add_i8(a: i8, b: i8) -> Option<i8> {
    a.checked_add(b)
}

pub fn sub_i32(a: i32, b: i32) -> Option<i32> {
    a.checked_sub(b)
}

// The result is consumed by a real bounds obligation, so each body carries a
// published row and a pinned verdict. The havoc `Option` still says nothing
// about WHICH variant came back; `bool as usize` is in-bounds either way.
pub fn add_i64_indexed(a: i64, b: i64) -> u8 {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1
    let t = [1u8, 2];
    t[a.checked_add(b).is_some() as usize]
}

pub fn mul_i128_indexed(a: i128, b: i128) -> u8 {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1
    let t = [1u8, 2];
    t[a.checked_mul(b).is_none() as usize]
}
