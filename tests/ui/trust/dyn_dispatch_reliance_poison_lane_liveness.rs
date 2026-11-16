//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): the NEGATIVE CONTROL `control`
//! below is now refused by the zero-row gate (one annotated ERROR, its doc's "no
//! annotation, deliberately" predates that). The C-FLOW poison it controls is still
//! what is pinned: a zero-row refusal carries the "this function has no obligation of
//! its own" note, which says the poison lane did NOT add an obligation there.
//! `dyn_dispatch_reliance_recursive_field_carrier_discharges.rs` is now check-fail for
//! the same reason; it still asserts the discharge, through that pinned NOTE.
//!
//! LIVENESS PIN for the C-FLOW poison lane, in both directions. It asserts
//! nothing new about the compiler; its entire job is to hold up the evidence
//! that a NEIGHBOURING fixture's central pin depends on.
//!
//! Its pair is
//! `dyn_dispatch_reliance_coroutine_interior_mask_tripwire.rs`. Read "why this
//! is two files" below before merging them.
//!
//! ## WHAT THIS IS FOR
//!
//! The tripwire's MASK B pin is an ABSENCE: `drive` there — a plain `fn` whose
//! return place is a coroutine — carries no annotation, because measured, it is
//! never verified at all. The moment it becomes an extracted body and refuses,
//! that unannotated error turns the tripwire RED, and that is the signal the
//! coroutine-interior walk has become load-bearing.
//!
//! An absence is only evidence if the thing that would fill it still works.
//! "No diagnostic names `drive`" is equally consistent with **"the C-FLOW poison
//! lane stopped refusing anything in this crate"** — in which case the tripwire
//! pins nothing and nobody finds out. This file is what excludes that reading,
//! on the exact carrier shape `drive` uses: a `dyn` reachable through a field
//! written concretely.
//!
//! If THIS file goes red, the tripwire's mask B pin is worthless until it is
//! fixed, **whatever colour the tripwire is showing.** That is the whole
//! relationship; there is no mechanism enforcing it, only this sentence and its
//! twin over there.
//!
//! ## WHY THIS IS TWO FILES — a constraint, not a style choice
//!
//! MEASURED 2026-08-20 on stage1 `b38db06a6d`: **a body whose native lowering
//! fails aborts the crate's verification before other bodies are reached, so a
//! fixture containing one cannot carry pins on any other body.** These two
//! functions originally lived in the tripwire, alongside its coroutine. Grepping
//! every body name in that report yielded `drive::{closure#0}` and nothing else:
//! `positive_control` was never verified, so it could not produce the error its
//! annotation required, and `control` was "clean" only by never having run.
//!
//! The tripwire's own subject — a coroutine whose across-await saved local is
//! refused by the native frontier (MASK A) — is exactly such a body. Its
//! evidence silences every other pin in its file. So the controls moved HERE,
//! where the measured output is:
//!
//! ```text
//! note: Trust verification: 0 proved, 0 failed, 1 runtime-checked out of 1 obligation(s)
//! error: Trust strict verification failed for `<crate>::positive_control`
//! --- bodies seen ---  <crate>::positive_control
//! ```
//!
//! **Do not merge these files back together.** It compiles, it stays green, and
//! it silently re-vacuums both pins below.
//!
//! ## The two pins, and their unequal strength
//!
//! * `positive_control` — the STRONG one. A required `ERROR` annotation. If the
//!   poison lane ever stops refusing an unwitnessed field-held `dyn`, the
//!   annotation is not found and this file goes RED. This is the pin the
//!   tripwire leans on.
//! * `control` — the WEAK one, and deliberately labelled as such rather than
//!   oversold. It carries no annotation, so it fires only if a witnessed,
//!   discharging site STARTS erroring — i.e. it catches the poison lane
//!   OVER-firing, not dying. Note what the measurement above does and does not
//!   say: `control` does not appear in "bodies seen" either, which is consistent
//!   with "verified with nothing to report" AND with "not reported". Its silence
//!   is therefore not independent evidence of anything; it is a cheap guard
//!   against a regression in the opposite direction.
//!   `dyn_dispatch_reliance_recursive_field_carrier_discharges.rs` is the
//!   `check-pass` fixture that actually asserts discharge.
//!
//! ## The residual, carried here too because it belongs to the pair
//!
//! If a mask lifts AND the coroutine-interior arms in `dyn_principals_in_ty`
//! have been reverted, NOTHING in either file goes red. No test can cover that:
//! a differential needs a reachable door and there is none. That asymmetry is
//! the honest argument for shipping an unobservable fix — the only thing
//! protecting a coroutine interior right now is a refusal in an unrelated
//! subsystem that nobody promised to keep.
//!
//! (Prose in this file never spells the annotation marker literally.
//! `compiletest`'s `parse_expected` regex is UNANCHORED, so the marker inside a
//! `//!` comment is parsed as a real expectation on that comment's own line — a
//! silently broken fixture. See `src/tools/compiletest/src/errors.rs`.)
#![no_std]
#![allow(dead_code)]

pub trait Emit {
    fn emit(&mut self, n: u32) -> u32;
}

pub struct Good;

impl Emit for Good {
    fn emit(&mut self, n: u32) -> u32 {
        n.wrapping_add(1)
    }
}

/// A `dyn` held in a field written CONCRETELY rather than behind a type
/// parameter — the carrier shape whose invisibility was a LIVE false PROVE,
/// closed at `0fe05a9f3c` and pinned by
/// `dyn_dispatch_reliance_field_held_dyn_root_stays_closed.rs`.
pub struct Bundle<'a> {
    pub sink: &'a mut dyn Emit,
}

/// NEGATIVE CONTROL — no annotation, deliberately. A witnessed site with no
/// unwitnessed carrier anywhere must still DISCHARGE. Fires only on the poison
/// lane OVER-firing; see the header for why this pin is the weaker of the two.
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dyn_dispatch_reliance_poison_lane_liveness::control`
//~v NOTE this function has no obligation of its own
pub fn control() -> u32 {
    let mut g = Good;
    let local: &mut dyn Emit = &mut g;
    local.emit(1)
}

/// POSITIVE CONTROL — this one MUST error, and it is the pin the tripwire next
/// door depends on.
///
/// `local` is the one WITNESSED coercion, so the enumeration is `{Good}` —
/// non-empty and apparently complete. `b.sink` holds a vtable the caller chose
/// and this compilation never saw built, so `Emit` is poisoned through the field
/// walk and NEITHER site discharges. Both calls render one `func_operand_name`,
/// which is why one poisoned trait refuses both.
pub fn positive_control(b: &mut Bundle<'_>) -> u32 {
    //~^ ERROR Trust strict verification failed
    //~| ERROR Trust Level 0 safety verification incomplete
    // (OD-1 item 14 amendment, 2026-10-06: the caller-chosen vtable read through a
    // field is also a class (c) Level-0 refutation, docs/DECISION_QUEUE.md
    // "OD-1-RG-CONCRETE".)
    let mut g = Good;
    let local: &mut dyn Emit = &mut g;
    let a = local.emit(1);
    let c = b.sink.emit(2);
    a.wrapping_add(c)
}
