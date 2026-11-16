//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@ rustc-env:TRUST_NO_BUNDLE_STD_TRAIT_IMPL=1
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! TRUST_NO_SYSROOT_CENSUS (2026-09-26): this file measures the BUNDLING lane, so it
//! runs with the sysroot panic census off. The census (docs/design/trust-std-design.md,
//! amendment 2026-09-26) derives from a std callee's own MIR that it reaches no
//! panic site and discharges the call on the compiler-total channel — which every
//! probe below is (`max`, `Result::ok`, `then_some`, `Wrapping::add`, the `as_ref`s,
//! `String::capacity`, `io::empty` reach no panic), bundled or not. With it on, a
//! dead bundling lane could no longer turn a row red here. The knob is subtractive
//! (it only withholds census grants); the census has its own fixtures in
//! `tests/ui/trust/sysroot_census/`.
//!
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
//!
//! RE-POINTED ONTO `certify` (2026-09-16), and given back a discriminator.
//!
//! Two independent things had broken this file's A/B, neither of them the knob.
//! First, policy B: `1db02fe416` reclassified an absent-SYSROOT-callee
//! panic-freedom row from a build error to a reported warning on the DEFAULT
//! lane, and every probe here calls a sysroot def at foundational types — so all
//! eight landed in the tolerated class and the annotated reds stopped arriving.
//! `-Ztrust-policy=certify` is where an unproved row is still fatal, so that is
//! where this question belongs now. Second, the three trait probes this file was
//! built around are refused even with the lane ON, each for its own downstream
//! reason (a `FatPtr` parameter trust-mc's call-summary reader does not admit, an
//! untrackable `String` aggregate, a public-dialect op with no private producer
//! capability) — a PRE-EXISTING frontier, not a bundling failure. With the knob
//! changing nothing observable, the file could not measure its own subject.
//! (CORRECTED 2026-09-19. Two of those three, not three, are still refused with
//! the lane on — `probe_slice_as_ref` now proves. And the `FatPtr` clause was
//! never sourced: the 2026-09-14 report it came from assigns that probe to
//! "trust-mc: aggregate solved without a proof", not to any `FatPtr` class. See
//! the amendment below and the header of the companion file.)
//!
//! `probe_wrapping_not` is the repair: `!x` on `Wrapping<u8>` routes through the
//! T-IMPL arm and, when this paragraph was written, was the one probe whose
//! verdict still MOVED — measured 1 proved with the lane on, 0 proved with the
//! knob set.
//!
//! AMENDED 2026-09-19 — `probe_slice_as_ref` MOVES TOO, and this file no longer
//! rests on a single discriminator. Whatever refused it with the lane ON has
//! stopped: `<[u8] as AsRef<[u8]>>::as_ref` is bundled (it already was) and
//! trust-mc now discharges the caller's panic-freedom row from it (measured:
//! `route=TriviallySafe`, `ChcSpacer`/`SmtBacked` — a `Trusted` native
//! authority, NOT a Clean kernel re-check). So `probe_slice_as_ref` is 1
//! proved with the lane on and 0 proved with THIS knob alone, exactly like
//! `probe_wrapping_not`, and that pairing is what shows the other file's green
//! to depend on THIS arm specifically rather than on some global effect of the
//! whole-lane knob. (A necessity result, not a cause: what changed downstream to
//! stop the refusal is narrowed to a `first-party/trust-mc` pin range and is NOT
//! established — the other file's header carries that.) Its annotations here
//! are unchanged and still correct — the knob still declines it. The sentence
//! above is kept, marked, because it records what was true when the
//! discriminator was added. Full measurement and the authority read:
//! `native_bundle_std_green_depends_on_bundle.rs`.
//!
//! BOTH DIRECTIONS STILL FAIL LOUDLY. If the trait knob stops declining trait
//! callees (under-subtraction), `probe_wrapping_not` and `probe_slice_as_ref` go
//! green and their annotations go unmatched. If it starts swallowing NON-trait
//! callees (over-subtraction), `probe_max_i32` / `probe_result_ok` /
//! `probe_then_some` go red as unannotated errors — this file deliberately omits
//! `dont-require-annotations: ERROR` so that stays fatal.
//!
//! RE-MEASURED 2026-11-10 (`docs/DECISION_QUEUE.md`, NATIVE-BUNDLE-NET-REMEASURE-1),
//! on a stage 1 of `e66b24d03d` with compiletest's own command. Two non-trait-arm
//! rows moved, neither because of this knob. `probe_io_empty` proves and loses its
//! annotations. `probe_then_some` is refused with the lane fully on as well (the
//! companion file's `[certify]` revision shows it), for the trust-mc reason its doc
//! comment gives, and is annotated. So the over-subtraction detectors are now
//! `probe_max_i32`, `probe_result_ok` and `probe_io_empty`. CONTROL: with
//! `TRUST_NO_BUNDLE_STD=1` added, all three report unannotated errors.
//!
//! The UNDER-subtraction half now rests on `probe_slice_as_ref` ALONE. Without
//! `TRUST_NO_BUNDLE_STD_TRAIT_IMPL` it proves, so its annotation goes unmatched.
//! `probe_wrapping_not` no longer moves: it is refused with the lane fully on too.
//! The bundled `<Wrapping<u8> as Not>::not` body is `ExtractField`, `Not`,
//! `MakeAggregate`, `Return`, and trust-mc declines its direct call summary
//! (`UnsupportedDirectCallSummary`). Its annotations stay: they are still true, and
//! the row returns as a discriminator if trust-mc admits that summary again.

use std::num::Wrapping;

pub fn probe_max_i32(a: i32, b: i32) -> i32 {
    std::cmp::max(a, b)
}

pub fn probe_result_ok(r: Result<u8, ()>) -> Option<u8> {
    r.ok()
}

/// Trust (2026-11-10, NATIVE-BUNDLE-NET-REMEASURE-1): refused with or without this
/// knob, for a reason downstream of the bundle. The bundled `then_some::<u8>` body's
/// `None` arm builds `Option<u8>` from an aggregate `Undef` seed, which trust-mc's
/// operand-consumption gate refuses, so trust-mc declines the call's direct summary
/// (`UnsupportedDirectCallSummary`). The companion file's `probe_then_some` has the
/// whole cause. Annotated rather than dropped: it is a non-trait-arm probe, so if
/// trust-mc's Uninit carrier lands, this annotation goes unmatched and the row
/// rejoins the green half below.
pub fn probe_then_some(b: bool) -> Option<u8> { //~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_trait_arm_knob_scoped::probe_then_some`
//~| ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_then_some`
    b.then_some(1)
}

pub fn probe_wrapping_add(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> { //~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_trait_arm_knob_scoped::probe_wrapping_add`
//~| ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_wrapping_add`
    a + b
}

pub fn probe_slice_as_ref(n: &[u8]) -> &[u8] { //~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_trait_arm_knob_scoped::probe_slice_as_ref`
//~| ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_slice_as_ref`
    n.as_ref()
}

pub fn probe_string_capacity(s: &String) -> usize { //~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_trait_arm_knob_scoped::probe_string_capacity`
//~| ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_string_capacity`
    s.capacity()
}

pub fn probe_string_as_ref(s: &String) -> &str { //~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_trait_arm_knob_scoped::probe_string_as_ref`
//~| ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_string_as_ref`
    s.as_ref()
}

/// Trust (2026-11-10, NATIVE-BUNDLE-NET-REMEASURE-1): GREEN under this knob, as a
/// non-trait-arm probe must be. `core::io::util::empty` is a free fn, bundled through
/// the non-trait arm, and it proves (trust-mc `ChcSpacer`, `Trusted`). It is now an
/// over-subtraction detector: if this knob starts swallowing non-trait callees, the
/// error here is unannotated and this file goes red.
pub fn probe_io_empty() -> std::io::Empty {
    std::io::empty()
}

/// Trust (2026-09-16): THE DISCRIMINATOR. `!x` on `Wrapping<u8>` routes through
/// the T-IMPL arm (`core::num::wrapping::{impl#..}::not`) and is the one probe
/// here whose verdict still MOVES with the knob: measured 1 proved with the lane
/// on, 0 proved with the knob set. Every other trait probe is refused either way
/// for its own downstream reason, so without this one the file could not observe
/// its own subject at all.
///
/// Trust (2026-09-19): "the one probe" is no longer true and is kept because it
/// records why this probe exists. `probe_slice_as_ref` moves with the knob too —
/// whatever refused it with the lane on has stopped — so this file now has TWO
/// under-subtraction discriminators. See the amendment in the header.
///
/// Trust (2026-11-10): this probe no longer moves with the knob. It is refused with
/// the lane fully on as well (trust-mc declines the bundled body's direct call
/// summary), so `probe_slice_as_ref` is the one discriminator left. See RE-MEASURED
/// in the header.
pub fn probe_wrapping_not(x: Wrapping<u8>) -> Wrapping<u8> { //~ ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_trait_arm_knob_scoped::probe_wrapping_not`
//~| ERROR Trust strict verification failed for `native_bundle_std_trait_arm_knob_scoped::probe_wrapping_not`
    !x
}

fn main() {}
