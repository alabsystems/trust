//@ needs-trust-verify
//@ revisions: bundled nobundle
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bundled] check-pass
//@[nobundle] rustc-env:TRUST_NO_BUNDLE_STD=1
//@[nobundle] check-fail
//! REGRESSION NET for the B-lane (plan of record
//! `docs/design/2026-08-19-verified-sysroot-scoping.md`, §5 step 2a′):
//! "Add falsification fixtures whose green DEPENDS on a bundled std body. §2.5
//! measured that today's corpus has none: `TRUST_NO_BUNDLE_STD=1` takes it from
//! 124/1 to 125/0. Until such fixtures exist there is no regression net for any
//! of this, and a future refactor could silently delete the B-lane's coverage
//! without a single red row."
//!
//! §2.5's measurement was over the `tests/trust-falsification/proved/` corpus
//! and is correct there. The ui suite was in better shape than the plan
//! records, but only accidentally: of `native_bundle_std_body_proved.rs`'s six
//! probes, exactly ONE (`probe_max_i32`) goes red under `TRUST_NO_BUNDLE_STD=1`
//! — the other five are discharged by audited models, so their green never
//! touched the bundle. (`native_bundle_std_trait_impl_body_proved.rs` is a real
//! net: all five of its probes depend on the lane.) Nothing documented any of
//! that, and no fixture ran the OFF direction at all.
//!
//! This file is the deliberate version. EVERY probe below was measured to
//! prove ONLY via `native_trust_ir_monomorphic_foreign_callees`
//! (trust_verify.rs): green with the lane on, red with it off. The bundled
//! body each green rests on, read from `-Ztrust-dump=native-bundle:<dir>`:
//!
//!   probe_max_i32          <- core::cmp::max::<i32>                 (core, free fn)
//!   probe_result_ok        <- core::result::Result::<u8, ()>::ok    (core, inherent)
//!   probe_then_some        <- core::bool::<impl bool>::then_some::<u8>
//!   probe_wrapping_add     <- <Wrapping<u8> as core::ops::arith::Add>::add   (T-IMPL arm)
//!   probe_slice_as_ref     <- <[u8] as core::convert::AsRef<[u8]>>::as_ref   (T-IMPL arm)
//!   probe_string_capacity  <- alloc::string::String::capacity       (alloc, inherent)
//!   probe_string_as_ref    <- <String as core::convert::AsRef<str>>::as_ref  (alloc, T-IMPL)
//!   probe_io_empty         <- core::io::util::empty  (spelled std::io::empty; the
//!                             body lives in core — no probe here reaches a
//!                             std-crate body, which mirrors the corpus: std
//!                             bodies bottom out in OS plumbing the lane declines)
//!
//! The two revisions are the A/B from §2.5, run on byte-identical probes:
//!
//!   * `bundled` (check-pass): the shipped default. If any probe goes red here,
//!     the lane lost coverage — the silent-deletion refactor the plan warns
//!     about now costs a red row.
//!   * `nobundle` (check-fail): `TRUST_NO_BUNDLE_STD=1`. Every probe must land
//!     on the fail-closed absent-callee arm and ERROR. If any probe stays GREEN
//!     here, either the knob stopped disabling the lane (the §2.5 measurement
//!     lever is broken and every A/B number after that is a lie), or an absent
//!     callee stopped failing closed (a model quietly widened — a soundness
//!     regression, not progress). Both are exactly the "verifier ASSUMES rather
//!     than proves" direction this suite exists to refuse.
//!
//! The knob is documented at its read site as strictly subtractive: "There is
//! no setting of this variable that admits anything, downgrades a policy, or
//! turns an obligation into an assumption." This fixture is what notices if
//! that sentence stops being true in either direction.

use std::num::Wrapping;

pub fn probe_max_i32(a: i32, b: i32) -> i32 { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_max_i32`
    std::cmp::max(a, b)
}

pub fn probe_result_ok(r: Result<u8, ()>) -> Option<u8> { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_result_ok`
    r.ok()
}

pub fn probe_then_some(b: bool) -> Option<u8> { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_then_some`
    b.then_some(1)
}

pub fn probe_wrapping_add(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_wrapping_add`
    a + b
}

pub fn probe_slice_as_ref(n: &[u8]) -> &[u8] { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_slice_as_ref`
    n.as_ref()
}

pub fn probe_string_capacity(s: &String) -> usize { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_string_capacity`
    s.capacity()
}

pub fn probe_string_as_ref(s: &String) -> &str { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_string_as_ref`
    s.as_ref()
}

pub fn probe_io_empty() -> std::io::Empty { //[nobundle]~ ERROR Trust strict verification failed for `native_bundle_std_green_depends_on_bundle::probe_io_empty`
    std::io::empty()
}

fn main() {}
