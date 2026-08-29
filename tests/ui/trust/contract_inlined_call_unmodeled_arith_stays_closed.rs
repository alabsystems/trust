//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! The inline is NOT a way to smuggle unmodeled arithmetic past the fragment.
//!
//! `half` expands exactly as intended — the lowered clause is literally
//! `(result) == ((x) / (2))`, so the call was resolved, gated and rendered.
//! The build still FAILS, because integer division is outside the modeled
//! fixed-width machine arithmetic and the verifier API says so
//! ("unmodeled fixed-width machine arithmetic"). Expansion widens what can be
//! WRITTEN; it does not widen what is MODELED, and the fail-closed boundary is
//! downstream of it.
//!
//! Pinning this direction matters because the failure is silent-looking: the
//! clause reads like ordinary arithmetic after expansion, and a future change
//! that starts MODELING division must make this fixture prove rather than
//! quietly leave it unsupported.
pub fn half(v: u64) -> u64 {
    v / 2
}

pub fn halve(x: u64) -> u64 ensures result == half(x) { x / 2 }
//~^ ERROR Trust Level 0 safety verification incomplete
//~| ERROR strict verification failed
