//~ NOTE "outcome":"unknown","solver":"trust-classifier","time_ms":0,"reason":"the resolved callee is not proved panic-free: the body carries an unproved absent-callee/drop-glue panic obligation
//~| NOTE "outcome":"unknown","solver":"trust-classifier","time_ms":0,"reason":"the resolved callee is not proved panic-free: the body carries an unproved absent-callee/drop-glue panic obligation
//~| NOTE "outcome":"failed","solver":"trust-classifier","time_ms":0,"reason":"the resolved callee is not proved panic-free:
//@ revisions: advisory
//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: discharge_unmodeled_dep=discharge_unmodeled_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//! DISCHARGE-NO-EVIDENCE-1 (2026-10-19): an instance discharge carries the resolved
//! LOCAL callee's own verdict, and reads `failed` only when that callee's ledger holds
//! evidence it can panic. MEASURED on the aterm consumer check of the Trust 0.11.0 cut
//! (`20565c3255a`, `targo trust build --allow-l0-gaps -p aterm`): `Gate: FAIL` on the
//! discharges of `atpkg::machine::LaunchApply::runs::<{closure}>`, the closure
//! `|why| aterm_log::info!("{why}")`, whose own rows were an absent callee
//! (`runtime_checked`) and unmodeled MIR (`unknown`), Level 0 summary "0 failed", and of
//! `aterm_link::cli::run::<{closure}>`, a closure whose one unsafe call (to an upstream
//! `unsafe fn`) is declared sound on its SAFETY comment (an `assumption:safety-comment`
//! row, SAFETY-ASSUME-1) beside an absent callee and unmodeled MIR: each discharge was
//! published `failed` with the bare `trust-classifier` solver, which `FailureBasis`
//! reads as `refuted`, for a callee nothing refuted.
//!
//! * `use_unmodeled` hands `runs` a closure whose only call is to an upstream fn this
//!   crate does not lower (`auxiliary/discharge_unmodeled_dep.rs`): the discharge of
//!   `runs::<{closure}>`'s site is `unknown` (line 1), still not established (a WARN
//!   here, an error on every fail-closed lane, which `discharge_refused_when_callee_
//!   trips_gate.rs` pins for the same outcome).
//! * `use_declared`, the second shape: the closure's only call is an upstream
//!   `unsafe fn` in a block its SAFETY comment declares. The block's unmodeled-call row
//!   is withheld and its `assumption:safety-comment` row discloses the premise; the
//!   call is an absent callee. Its discharge is `unknown` too (line 2). The two
//!   `unknown` pins are the same text: each output line satisfies one annotation, so
//!   both closures' rows are needed. Without the SAFETY-comment admission
//!   (`verdict_rests_on_user_axiom_admitting`) this row stays `failed`.
//! * `use_panicking`, the control: a closure whose own `panic!` is reachable keeps its
//!   `failed` discharge (line 3; the only `failed` discharge in this file, so the pin
//!   stops at the shared reason prefix, whichever conjunct of
//!   `instance_discharges_panic_freedom` refused it): its panic row is a formula some
//!   engine could refute, so the refusal is not evidence-free.
//!
//! No annotation or doc line here carries the SAFETY marker with its colon, which the
//! comment scan would read only directly above a block.
//!
//! BORN RED: before DISCHARGE-NO-EVIDENCE-1 lines 1 and 2 do not match (those rows
//! read `"outcome":"failed"` with the same reason). Not built or run when written.

pub fn runs<F: FnOnce(u32)>(n: u32, say: F) -> bool {
    if n > 1 {
        say(n);
        false
    } else {
        true
    }
}

pub fn use_unmodeled(n: u32) -> bool {
    runs(n, |m| discharge_unmodeled_dep::note(m))
}

pub fn use_declared(n: u32) -> bool {
    runs(n, |m| {
        // SAFETY: `take` has no precondition; it is an `unsafe fn` only for this shape.
        let _ = unsafe { discharge_unmodeled_dep::take(m) };
    })
}

pub fn use_panicking(n: u32) -> bool {
    runs(n, |m| {
        if m > 3 {
            panic!("big");
        }
    })
}
