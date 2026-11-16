//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! ADVERSARIAL CONTROL for the memory-safe demotion. `pick` MUST stay refused.
//!
//! The guarded exit is a DIVERGING CALL: MIR lowers `std::process::exit` to
//! `Call { target: None }` with no cleanup edge, and `rustc_codegen_ssa` finishes it
//! with a bare `unreachable` in this frame.
//!
//! 2026-09-24 (`fd5e19dac9`) re-derived this file GREEN on the argument that
//! `a53999401d` made the call a faithful `Call { target: None }`. That was not the
//! mechanism: the native lowering still REFUSED the call ("diverging call
//! `std::process::exit` … has no normal-return target and no modelled cleanup
//! successor"), and `pick` went green because memory-safe collapsed the refusal into
//! one `assumption:native-lowering` row and admitted it (measured on stage-1
//! `b4bc7cdf9d`: rc=0, JSON rows = the proved index, the demoted overflow and the
//! skipped collapse row). The collapse stood for a charge the lowering never
//! minted; the same collapse admitted an unverified dependency's arbitrary-address
//! read (`reject_lowering_gap_launders_uncharged_callee.rs`).
//!
//! Since `a84aa67936` (T2) the call lowers: the bundle follows it and charges the
//! absent callee (`[trust-absent-callee-assumption] call to absent callee
//! std::process::exit`, runtime-checked), which memory-safe does not admit — so
//! `pick` is refused on that charge, as its lowerable twin with a live `String`
//! always was. Measured on stage-1 `f0e3202c07`: rc=1 with this file's error, and
//! this file's previous `check-pass` failing there. The collapse no longer decides
//! this body; if a future lowering regression made it fail again, the collapse
//! would still refuse it, because `std::process::exit` is not a local verified
//! function (`memory_safe_assumption_uncharged_edges`).
//!
//! Kept from the earlier record: a MIR scan cannot establish "every exit traps"
//! (the `Unreachable` after the call is erased by the required
//! `LintAndRemoveUninhabited` pass and re-created by codegen), so neither a scan
//! nor a demotion may green this file. What may: a MODEL of `std::process::exit`
//! (a total, defined termination) that the native bundle discharges instead of
//! charging. The uninhabited-enum twin is `reject_uninhabited_return_call_gap.rs`.
pub fn pick(v: &[u32], i: usize) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_diverging_call_gap::pick`
    //~| WARN Trust Level 0 safety verification incomplete for `reject_diverging_call_gap::pick`
    if i >= v.len() {
        std::process::exit(1);
    }
    v[i] + 1
}
