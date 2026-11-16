//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The VACUITY direction: a `Display::fmt` whose bundle contains NO `dyn Write`
//! coercion at all has an empty enumeration, and an empty case split must stay
//! fail-closed rather than pass for having nothing to check.
//!
//! ## CORRECTED 2026-08-19 — this file never tested the mechanism it named
//!
//! Its title said POISON and its header said `core::fmt::Write` "is POISONED for
//! this bundle". MEASURED with `TRUST_DYN_RELIANCE_PROBE=1`, the poison never
//! happened. The one line the probe printed was:
//!
//! ```text
//! C-FLOW declined: no coercion (vacuous)
//! ```
//!
//! Neither the `opaque` line nor the `trait … poisoned` line ever appeared. The
//! reason is the defect this correction accompanies: `dyn_principals_in_ty`
//! decomposed an ADT through its GENERIC ARGUMENTS only, and `Formatter<'a>`'s
//! arguments are one lifetime — its `buf: &'a mut dyn Write` field was invisible,
//! so nothing was ever poisoned. The verdict was right; the stated reason was
//! not, and the two are not interchangeable. Vacuity EVAPORATES the moment any
//! `dyn Write` coercion joins the bundle, and then the site discharged. That was
//! a live false prove, pinned now by
//! `dyn_dispatch_reliance_open_sink_poison_direction.rs`, which adds exactly such
//! a coercion and must still refuse.
//!
//! So read this file as what it is: a bare `Display::fmt` with no sibling
//! coercion fails closed. The POISON direction is the sibling fixture's job, and
//! it now genuinely exercises it.
//!
//! Both certificates decline here, and the second reason is unchanged:
//!
//! * C-FLOW declines — vacuously above, and by poison once a coercion exists;
//! * C-UNIVERSAL declines — Φ is not (and cannot soundly be) declared on
//!   `fmt::Write::write_str`, because std's private `Adapter` impl forwards to an
//!   arbitrary user `io::Write`.
//!
//! This verdict is CORRECT, not a limitation to be optimized away: a
//! `Display::fmt` really does panic when handed a panicking sink, and any rule
//! that reported it clean would be a false promise. The composite in
//! `dyn_dispatch_reliance_cflow_concrete_sink.rs` — where the caller pins the
//! sink — is the shape that legitimately discharges.
//!
//! ## D1 increment 1 (2026-09-25) — the SITE stays closed; the FUNCTION is now a
//! conditional pass
//!
//! Everything above still holds for the `dyn` site: C-FLOW and C-UNIVERSAL both
//! still decline, and nothing discharges it. What changed is the function's
//! verdict: an impl whose only unproved edge is its own `Formatter`'s writer is
//! now published as the WRITER-RELATIVE class — its row stays unproved and
//! `runtime-checked`, it is reported as an advisory ("panic-free relative to its
//! `Formatter`'s writer"), `-Ztrust-policy=certify` refuses it, and no shared
//! bar or registry reads it as panic-free. The "false promise" this file guards
//! against is a verdict of panic-freedom; the conditional verdict states the
//! condition instead. BEFORE (stage-1 snapshot `4e9fe36bf`): the impl was
//! refused, `error: Trust strict verification failed` on this `fn` (the pin this
//! file carried until then). See `trust_verify/fmt_writer_relative.rs`.
#![no_std]
#![allow(dead_code)]

use core::fmt;

pub struct Tag;

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("tag")
        //~^^ WARN Trust verification advisory
        //~| NOTE panic-free relative to its `Formatter`'s writer
    }
}
