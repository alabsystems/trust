//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ forbid-output: copy operand type mismatch
//@ forbid-output: full TrustIr module validation failed
//! A dyn-coercion-bearing body must produce a WELL-TYPED native TrustIr bundle
//! (red-suite triage 2026-08-13, class 3 — the typed-CHC encoder gap).
//!
//! The extractor deliberately models the `&S1 -> &dyn T` unsize coercion as an
//! opaque constant (sound havoc: no vtable/pointee fact asserted). The bridge
//! used to mint that havoc's `Inst::Undef` seed at a HARDCODED byte-slice fat
//! spelling (`fatptr<slice u8>`), while the `Copy` into the `&dyn T` local
//! declares `fatptr<dyn.N>` — and a promoted `&[&str; N]` table's thin array
//! ref declares plain `ptr` — so the module failed its own typed validation:
//!
//! ```text
//! native trust_mc TrustIr CHC/PDR bundle runner did not produce proof-grade
//! evidence: invalid native solve input `native_trust_ir_bundle.module`:
//! full TrustIr module validation failed: bb0: copy operand type mismatch:
//! expected fatptr<dyn.4241814513>, got fatptr<slice ty.0>
//! ```
//!
//! An ill-typed module is a PRODUCER INVARIANT VIOLATION, not an honest
//! decline: it strips proof authority from EVERY obligation in the body (the
//! guarded arithmetic here included), reporting an internal validation error
//! where the honest per-construct refusal belongs. What this fixture pins is
//! that both producer-invariant messages are GONE — the havoc seed is now
//! minted at the consumer's declared type, so the bundle type-checks and the
//! native lane's refusal (if any) is the per-construct authority gate speaking
//! for a construct it genuinely cannot yet prove over.
//!
//! It was `check-fail` until `trust_verify::static_str_write_fmt` landed: the
//! `write!` chain carried an absent-callee panic-freedom obligation that stayed
//! runtime-checked, which strict policy correctly rejected.
//!
//! ## Why it is `check-pass` now — re-derived, as the previous text demanded
//!
//! That doc said: "if this fixture ever starts passing, re-derive WHY before
//! blessing: either the fmt chain became provable end to end (fine) or a
//! havoc-bearing body was granted proof authority (fail-OPEN)". It is the FIRST
//! arm, measured on a patched compiler, not the second:
//!
//! ```text
//! TRUST_DYN_RELIANCE_PROBE: write_fmt site=<Sink as core::fmt::Write>::write_fmt
//!   => DISCHARGED (reduces to proved <Sink as core::fmt::Write>::write_str)
//! ```
//!
//! `go`'s only obligation was that absent-callee row. The reduction transfers it
//! to `Sink::write_str`, which this crate proves on its own INDEPENDENT verdict,
//! so `go` ends with ZERO obligations — it requests no native solve at all, and
//! the coercion havoc therefore acquires nothing. `go` genuinely cannot panic, so
//! green is the correct verdict.
//!
//! ## The half of this guard that is now UNMANNED
//!
//! Because `go` has zero obligations it no longer exercises "a havoc-bearing body
//! must never acquire proof authority". The `forbid-output` pins above still run
//! (they are the producer-invariant half this file is named for, and they are why
//! it must not simply be deleted), but the proof-authority half needs a NEW
//! fixture: a coercion-bearing body with a SOLVE-REQUIRING obligation. Do not
//! invent one by guessing — a candidate the interval/ay lane can discharge without
//! the native bundle pins nothing.
#![no_std]
#![allow(dead_code)]

use core::fmt::{self, Write as _};

pub trait T {
    fn f(&self) -> u32;
}

pub struct S1;

impl T for S1 {
    fn f(&self) -> u32 {
        7
    }
}

pub struct Sink;

impl fmt::Write for Sink {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        Ok(())
    }
}

// The dyn coercion (`&S1 -> &dyn T`) and a panic-freedom obligation (the
// `write!` chain) share one body, so the native lane must build — and
// type-check — a bundle containing the coercion havoc.
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dyn_coercion_bundle_stays_well_typed::go`
//~v NOTE this function has no obligation of its own
pub fn go(s: &S1, w: &mut Sink) -> fmt::Result {
    let d: &dyn T = s;
    let _ = d.f();
    write!(w, "x")
}
