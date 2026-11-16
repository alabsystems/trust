//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: this function has no obligation of its own
//! REGRESSION, and it was a LIVE FALSE PROVE (measured 2026-08-19): a `dyn`
//! reachable through a ROOT PARAMETER'S FIELD must poison its trait, exactly as
//! one reachable through a root parameter's type argument does.
//!
//! `dyn_principals_in_ty` used to answer for an ADT by walking its GENERIC
//! ARGUMENTS only. `Bundle<'a>`'s arguments are one lifetime, so the walk
//! reported NO principal, `observe_bundle_body`'s root-parameter poison never
//! fired, and `Emit` stayed unpoisoned even though `b.sink` holds a vtable this
//! compilation never saw built.
//!
//! ## The shape is MIXED, and that is what defeats the backstop
//!
//! A field-held `dyn` on its own still failed closed BY ACCIDENT: with no
//! coercion anywhere in the bundle, `coerced.get(trait)` is `None` and
//! `site_discharges` declines on VACUITY. Add ONE unrelated witnessed coercion
//! for the same trait — `local` below — and the guard evaporates: the enumerated
//! set is `{Good}`, non-empty and apparently complete, `<Good as Emit>::emit`
//! proves, and C-FLOW discharges a site whose receiver is not in the
//! enumeration. Both calls render one `func_operand_name`, so the probe reported
//! `(2 site(s)) => DISCHARGED`.
//!
//! Exactly the shape `17b2aaf890` named — "one coercion the walker sees plus a
//! second vtable for the same trait behind an unhandled kind" — reached through
//! the door that commit did NOT close. It closed the `_ =>` catch-all, so an
//! UNHANDLED type kind fails closed; `ty::Adt` is a HANDLED arm that returned
//! nothing, which is indistinguishable from a type that really carries nothing.
//!
//! ## Measured before the fix
//!
//! ```text
//! $ trustc --crate-type lib exploit.rs   # DEFAULT lane, no -Ztrust-verify=on
//! EXIT=0, zero diagnostics
//! $ trustc --crate-type rlib exploit.rs && trustc -L. driver.rs && ./driver
//! thread 'main' panicked at driver.rs: caller-supplied sink panicked
//! RUN EXIT=101
//! ```
//!
//! Certified panic-free as an rlib — the exact scenario C-FLOW exists to serve —
//! and then panicked through a caller-supplied sink. `--crate-type lib` here is
//! therefore an ASSERTION, the same one
//! `dyn_dispatch_reliance_cflow_concrete_sink.rs` documents: do not "fix" this
//! file by changing the crate type.
//!
//! ## Two NEIGHBOURING shapes deliberately absent, each measured rather than assumed
//!
//! Both were predicted to be instances of this bug. Measured on the pre-fix
//! binary NEITHER is, and a fixture for either would have passed for a reason it
//! did not state — the same defect this slice repairs in
//! `dyn_dispatch_reliance_open_sink_stays_closed.rs`:
//!
//! * `Held { sink: Box<dyn Emit> }` ALREADY failed closed, probe reporting
//!   `trait Emit poisoned`. Reading `h.sink` goes through
//!   `<Box<dyn Emit> as DerefMut>::deref_mut`, an unbundled callee whose
//!   DESTINATION type is `&mut dyn Emit` — so `call_output_traits` names the
//!   principal with no field walk involved. A different channel, already sound.
//! * `enum H<'a> { One(&'a mut dyn Emit) }` read through `match` DID discharge
//!   its `dyn` site, but the crate errored anyway from an unrelated refusal
//!   ("native typed-TrustIr lowering did not complete"). The enum carrier is
//!   pinned instead by
//!   `dyn_dispatch_reliance_field_held_dyn_variant_carrier_stays_closed.rs`,
//!   which reaches it with nothing else in the way.
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

/// The `dyn` is held in a FIELD written concretely, not behind a type parameter.
/// `ArgHolder<dyn Emit>`-style shapes were always caught by the generic-argument
/// walk; this one was not.
pub struct Bundle<'a> {
    pub sink: &'a mut dyn Emit,
}

/// One level further out: a field holding a STRUCT that holds the `dyn`. Also
/// MEASURED discharging before the fix (EXIT=0), so the walk has to recurse
/// through field types, not merely look at an ADT's own fields once.
pub struct Inner<'a> {
    pub sink: &'a mut dyn Emit,
}

pub struct Outer<'a> {
    pub inner: Inner<'a>,
}

pub fn drive(b: &mut Bundle<'_>) -> u32 {
    //~^ ERROR Trust strict verification failed
    //~| ERROR Trust Level 0 safety verification incomplete
    // (OD-1 item 14 amendment, 2026-10-06: the caller-chosen vtable read through a
    // field is also a class (c) Level-0 refutation, docs/DECISION_QUEUE.md
    // "OD-1-RG-CONCRETE".)
    let mut g = Good;
    // WITNESSED: this coercion is the one the walker sees. It is what makes the
    // enumeration look complete instead of vacuous.
    let local: &mut dyn Emit = &mut g;
    let a = local.emit(1);
    // NEVER WITNESSED: the caller chose this vtable. The site must keep its
    // obligation.
    let c = b.sink.emit(2);
    a.wrapping_add(c)
}

pub fn drive_nested(o: &mut Outer<'_>) -> u32 {
    //~^ ERROR Trust strict verification failed
    //~| ERROR Trust Level 0 safety verification incomplete
    // (OD-1 item 14 amendment, 2026-10-06: the caller-chosen vtable read through a
    // field is also a class (c) Level-0 refutation, docs/DECISION_QUEUE.md
    // "OD-1-RG-CONCRETE".)
    let mut g = Good;
    let local: &mut dyn Emit = &mut g;
    let a = local.emit(1);
    let c = o.inner.sink.emit(2);
    a.wrapping_add(c)
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
