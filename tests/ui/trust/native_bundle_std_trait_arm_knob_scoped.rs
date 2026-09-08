//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ rustc-env:TRUST_NO_BUNDLE_STD_TRAIT_IMPL=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! `TRUST_NO_BUNDLE_STD_TRAIT_IMPL=1` must disable EXACTLY the T-IMPL arm of
//! `native_trust_ir_monomorphic_foreign_callees` — no more, no less.
//!
//! Companion to `native_bundle_std_green_depends_on_bundle.rs` (same eight
//! probes, byte-identical bodies; plan of record §5 step 2a′). That file pins
//! the whole-lane knob in both directions; this one pins the trait-arm knob's
//! SCOPE, which is what makes its A/B measurements meaningful:
//!
//!   * the three probes whose bundled body is admitted through trait-method
//!     RESOLUTION (`<Wrapping<u8> as Add>::add`, `<[u8] as AsRef<[u8]>>::as_ref`,
//!     `<String as AsRef<str>>::as_ref`) must fall to the fail-closed
//!     absent-callee arm and ERROR — annotated below;
//!   * the five probes bundled through the non-trait arm (free fns
//!     `core::cmp::max::<i32>` / `core::io::util::empty`, inherent methods
//!     `Result::ok` / `bool::then_some` / `String::capacity`) must KEEP their
//!     bundle-backed proof. This file deliberately omits
//!     `dont-require-annotations: ERROR`, so any of them going red is an
//!     unannotated error and fails the test — the green half is load-bearing.
//!
//! The knob's read site documents it as restoring "exactly the pre-T-IMPL
//! behavior (every trait callee declined)". If the trait knob starts swallowing
//! non-trait callees, the greens here go red (scope leak, measurement lever
//! over-subtracts). If it stops declining trait callees, the annotated reds go
//! green (the lever under-subtracts, and every trait-arm A/B is inflated).
//! Either way this fixture is the red row.

use std::num::Wrapping;

pub fn probe_max_i32(a: i32, b: i32) -> i32 {
    std::cmp::max(a, b)
}

pub fn probe_result_ok(r: Result<u8, ()>) -> Option<u8> {
    r.ok()
}

pub fn probe_then_some(b: bool) -> Option<u8> {
    b.then_some(1)
}

pub fn probe_wrapping_add(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> { //~ ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_wrapping_add`
    a + b
}

pub fn probe_slice_as_ref(n: &[u8]) -> &[u8] { //~ ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_slice_as_ref`
    n.as_ref()
}

pub fn probe_string_capacity(s: &String) -> usize {
    s.capacity()
}

pub fn probe_string_as_ref(s: &String) -> &str { //~ ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_string_as_ref`
    s.as_ref()
}

pub fn probe_io_empty() -> std::io::Empty {
    std::io::empty()
}

fn main() {}
