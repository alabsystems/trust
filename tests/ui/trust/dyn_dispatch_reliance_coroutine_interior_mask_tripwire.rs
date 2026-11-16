//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: this function has no obligation of its own
//! TRIPWIRE, not a differential. This file exists because
//! `dyn_principals_in_ty`'s coroutine-interior walk is **UNREACHABLE TODAY**,
//! and somebody has to find out on the day it stops being.
//!
//! Its pair is
//! `dyn_dispatch_reliance_poison_lane_liveness.rs`, which carries the controls
//! this file cannot. Read the "why this is two files" section before merging
//! them.
//!
//! ## What is being pinned, and why it is not a regression test
//!
//! The walk used to answer for `ty::Closure`, `ty::Coroutine`,
//! `ty::CoroutineClosure` and `ty::CoroutineWitness` in ONE arm under one stated
//! premise — *"their held values ... ARE their generic arguments"* — which is
//! false for two of the four: `CoroutineArgsParts` has NO witness field, so a
//! local saved across a suspend point is named nowhere but the MIR coroutine
//! layout. That was a real fail-open and it is fixed.
//!
//! MEASURED 2026-08-20 on stage1 `b38db06a6d`: the fix produces **zero
//! observable change**. This file is byte-identical compiled with and without
//! it. The reason is two independent refusals standing in front of the walk:
//!
//! * **MASK A** — the native typed-TrustIr frontier refuses ACROSS-AWAIT SAVED
//!   LOCALS outright: *"unsupported operation: coroutine frame field 2 is an
//!   across-await saved local (len 1); the single/multi-await native frontier is
//!   not yet modeled"*. An across-await saved local IS the coroutine interior
//!   the walk exists to read, so the mask covers the fail-open's target exactly.
//! * **MASK B** — `drive` below, a plain `fn` whose RETURN PLACE is the
//!   coroutine, **never appears as a verified body at all**. The only name in
//!   the report is `drive::{closure#0}`. Consistent with the
//!   `clean-skip-unrevealed-opaque` decline on an `impl Future` return. Since a
//!   coroutine type is not nameable in surface Rust, the return place is the
//!   only door into a sync signature — so mask B closes that door completely.
//!
//! So there is no differential to assert and none is asserted here. An earlier
//! draft of this file did assert one; it could never have gone green, and
//! pinning it would have been a test that passes for a different reason than it
//! claims.
//!
//! ## WHY THIS IS TWO FILES — a constraint, not a style choice
//!
//! MEASURED, and it is the reason the controls live next door: **a body whose
//! native lowering fails aborts the crate's verification before other bodies are
//! reached, so a fixture containing one cannot carry pins on any other body.**
//! An earlier draft put the poison-lane controls in THIS file. Grepping every
//! body name in its report yielded `drive::{closure#0}` and nothing else — the
//! controls were never verified, so the one that must ERROR silently could not,
//! and the one that must stay CLEAN was vacuously satisfied by never running.
//!
//! MASK A's own evidence is what silences everything else in the file. That is
//! self-defeating for any pin except the two that are ABOUT the coroutine. So:
//!
//! * this file holds MASK A and MASK B, and nothing else;
//! * `dyn_dispatch_reliance_poison_lane_liveness.rs` holds the controls, with no
//!   coroutine in it, where they demonstrably do fire.
//!
//! **Do not merge them back together.** It compiles, it stays green, and it
//! silently re-vacuums both controls.
//!
//! ## What this file actually catches
//!
//! * **MASK A lifting** — `drive::{closure#0}`'s
//!   `native typed-TrustIr lowering did not complete` is REQUIRED below. Model
//!   the across-await frontier and that error disappears, the annotation is not
//!   found, and this file goes RED. That is the signal.
//! * **MASK B lifting** — `drive` carries NO annotation. The moment it is
//!   extracted and refuses, that is an unexpected error and this file goes RED.
//!
//! MASK B's pin is only as meaningful as the claim that the C-FLOW poison lane
//! still refuses anything at all — otherwise "no diagnostic on `drive`" is
//! vacuous. That claim is what
//! `dyn_dispatch_reliance_poison_lane_liveness.rs` exists to hold, on the exact
//! carrier shape `drive` would use. If it goes red, this file's mask B pin is
//! worthless until it is fixed, whatever colour this file is.
//!
//! ## WHEN THIS FILE GOES RED — the next step, written down now
//!
//! Do not "fix" it by deleting an annotation. A red here means the coroutine
//! interior became reachable, and `dyn_principals_in_ty`'s `ty::Coroutine` /
//! `ty::CoroutineWitness` arms just became load-bearing against a false PROVE.
//! Re-cut this file into the differential it could not be: add
//! `//` + `~^ ERROR Trust strict verification failed` to `drive`, confirm it is
//! ABSENT with the arms reverted and PRESENT with them in place, and re-measure
//! the coverage price — which is zero today only because the walk never runs.
//!
//! (Prose in this file never spells the annotation marker literally.
//! `compiletest`'s `parse_expected` regex is UNANCHORED, so the marker inside a
//! `//!` comment is parsed as a real expectation on that comment's own line — a
//! silently broken fixture. See `src/tools/compiletest/src/errors.rs`.)
//!
//! ## 2026-09-29: MASK B lifted, and a third mask stands in its place
//!
//! MASK B was not a decline of `drive` itself. It was the crate-level abort
//! described under "why this is two files": `drive::{closure#0}`'s refusal was
//! emitted inside `run_required_analyses` — the coroutine's layout was read from
//! its `optimized_mir`, which ran TrustVerify there — so `analysis` took it for a
//! FRONT-END error and skipped the whole-crate walk, and `drive` was never
//! verified. The layout is now read from pre-steal elaborated MIR
//! (`trust_local_coroutine_layout`), the coroutine is verified by the walk, and
//! `drive` IS verified: it is refused, and that refusal is now pinned on `drive`.
//!
//! It is still NOT the differential this file asks for. Measured on stage 1 at
//! 21eb33ef5e: `drive`'s only row is the whole-function panic-freedom `[assert]`,
//! RUNTIME-CHECKED — an absent-callee assumption-panic row (the generic class,
//! so strict keeps it fail-closed), with native lowering refusing `drive`'s
//! first `Alloca` ("without an internally bound extent, pointee-type, and
//! alignment derivation"). No dyn-dispatch reliance row appears, so the
//! coroutine-interior arms are still not what refuses it. Call that MASK C: the
//! error pinned on `drive` goes away when MASK C lifts, and that is the day to
//! re-cut this file into the differential (refusal ABSENT with the arms
//! reverted, PRESENT with them in place).
//!
//! The same abort was the premise of "why this is two files": a coroutine
//! whose native lowering fails no longer cuts the walk short, so controls placed
//! here would now be reached. The files stay split anyway; merging them buys
//! nothing and would re-tie the controls to this file's masks.
//!
//! ## The residual, stated rather than hidden
//!
//! If a mask lifts AND the coroutine arms have been reverted, this file stays
//! GREEN. Nothing can cover that: a differential needs a reachable door and
//! there is none. That asymmetry is exactly why the arms ship despite being
//! unobservable — the only thing protecting a coroutine interior right now is a
//! refusal in an unrelated subsystem that nobody promised to keep.
//!
//! One door was NOT measured and may already be open: a sync caller of an
//! `async fn` holds the coroutine in a LOCAL, and `call_output_traits` walks
//! that destination type. It additionally needs the callee to fall outside
//! `observed_bodies` before `deferred_output_poisons` fires. If you want to
//! falsify anything above, that is where to look first.
#![no_std]
#![allow(dead_code)]

use core::future::Future;

pub trait Emit {
    fn emit(&mut self, n: u32) -> u32;
}

pub struct Good;

impl Emit for Good {
    fn emit(&mut self, n: u32) -> u32 {
        n.wrapping_add(1)
    }
}

/// MASK B's subject. A plain `fn`, not a coroutine: its RETURN PLACE is the
/// coroutine carrier and its body holds a witnessed coercion, which is the
/// complete recipe for the fail-open — a mixed bundle where the enumeration
/// looks complete and one vtable came from a place the walk could not see.
///
/// Until 2026-09-29 it carried NO annotation because it produced NO diagnostic:
/// it was not verified at all (MASK B). It is verified now, and refused by
/// MASK C — see the section above. If this refusal disappears, MASK C lifted.
pub fn drive() -> impl Future<Output = u32> {
//~^ ERROR Trust strict verification failed for `dyn_dispatch_reliance_coroutine_interior_mask_tripwire::drive`: 1 obligation(s) were not fully verified
    let mut g = Good;
    // WITNESSED: the coercion the walker sees. It is what would make the
    // enumeration look complete instead of vacuous, if this body were verified.
    let local: &mut dyn Emit = &mut g;
    let a = local.emit(1);
    // The coroutine below IS a separate verified root, and it refuses on two
    // counts that have nothing to do with this slice: the executor-protocol
    // premise of `5e6b929e1b`, and MASK A. Both are pinned so that lifting
    // either one is visible here. (Until 2026-10-03 it also carried a `Trust
    // Level 0 safety verification incomplete` error, whose only failed Level 0
    // row was the `[unsafe] missing SAFETY comment` stand-in on the
    // `Pin::new_unchecked` of rustc's own `.await` lowering. AW-1, `d46ddcc8b2`,
    // stopped charging it; that pin was removed 2026-10-04, measured on a stage 1
    // of `1ab78ed8e8` and one with AW-1, and neither refusal below moved.)
    async move {
        //~^ ERROR coroutine executor-protocol premise is unproved
        //~| ERROR native typed-TrustIr lowering did not complete
        let mut h = Good;
        // NEVER WITNESSED BY `drive`'S BUNDLE. This coercion is in the
        // coroutine's own body, which `drive` builds with an `Aggregate` rvalue
        // rather than calling — so that body is not bundled with `drive`, and
        // this vtable has no witnessed origin there.
        let s: &mut dyn Emit = &mut h;
        // The suspend point. `s` is live across it, so it is saved into the
        // coroutine layout — the one and only place its type is ever named, and
        // the exact construct MASK A refuses.
        core::future::pending::<()>().await;
        s.emit(2).wrapping_add(a)
    }
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
