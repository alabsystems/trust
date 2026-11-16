//@ needs-trust-verify
//@ revisions: default
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//! Trust (W5, 2026-10-01): a callee that carries a `requires` is never MIR-inlined
//! in a verifying session, so its precondition row survives every way of turning
//! the MIR inliner on.
//!
//! Before the fix, each non-default revision compiled with exit 0 and the binary
//! returned 44 (`200 + 100` wrapped): the inliner copied `callee` — whose overflow
//! `Assert` Trust had elided because it is proved UNDER `requires x < 100` — into
//! `caller`, and the precondition row went away with the `Call` (MEASURED on stage
//! 1 `30387be11`, docs/KNOWN_HAZARDS.md "under explicit MIR inlining"). Every
//! revision must report the violated precondition, exactly as the default does.
//! `check-fail` exercises it: the inliner runs in the MIR a check build verifies
//! (MEASURED with the pre-fix pack `4d9a20e3daf`: `--emit=metadata` with
//! `-Zinline-mir=yes` or `-Zmir-opt-level=3` exited 0 with no `[precond] FAILED`).

fn callee(x: u8) -> u8
    requires x < 100
{
    x + 100
}

fn caller() -> u8 { //~ ERROR Trust strict verification failed for `w5_requires_callee_not_mir_inlined::caller`
    callee(200)
}

fn main() {
    let _ = caller();
}
