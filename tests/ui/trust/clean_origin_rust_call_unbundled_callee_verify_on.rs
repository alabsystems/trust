//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//! **W5 INCREMENT 3 — THE FIXTURE THAT ACTUALLY PINS THE `RustCallChain` CALL MODEL.**
//!
//! Two earlier fixtures of mine did NOT pin it and were deleted rather than kept as
//! decoration: both measured byte-identical (modulo `elapsed_ms`) with the charge
//! disabled, so their green was unearned. The reason is that a local Clean-origin def's emitted MIR body is normally
//! BUNDLED into its caller's native verification module, so the call is
//! discharged from the real body and `clean_origin_call_model_of_record`
//! is never consulted for a licence.
//!
//! REPRODUCING THE BORN-RED MEASUREMENT. The development run used a temporary
//! `TRUST_NO_RUSTCALL_CHARGE` env switch that is deliberately NOT in the shipped
//! compiler, so do not look for it — citing it as a live control would be citing a
//! measurement nobody can repeat. To reproduce from this tree: comment out the
//! `trust_charge_clean_rust_callees(tcx);` call in
//! `compiler/rustc_mir_transform/src/trust_verify.rs` (the pre-walk charge, just
//! above the Clean-origin panic-free registration loop), `./x.py build`, and
//! recompile this file. Measured that way 2026-09-25: exit 0 with the charge,
//! exit 1 without it, failing on the bridge's absent-callee arm.
//!
//! THE MECHANISM THIS FIXTURE DEPENDS ON — READ BEFORE EDITING.
//! `main` calls 95 other local functions first. `main` + 95 fillers exactly
//! fills `NATIVE_TRUST_IR_MAX_BUNDLE_FUNCTIONS` (96, `trust_verify.rs`), so
//! `twice_winc` is EVICTED from the bundle and its call reaches the fatal
//! absent-callee arm in `trust-ir-bridge`'s `lower_terminator_normal`. The only
//! thing that can discharge it there is `clean_origin_call_model_of_record`
//! returning `Some` for `RustCallChain` — i.e. increment 3's
//! `trust_charge_clean_rust_callees` certifying `winc`
//! `Pure ∧ Total ∧ Deterministic ∧ NoPanic`.
//!
//! MEASURED on a stage1 `trustc`, 2026-09-25:
//!   charge on  -> exit 0, `main` mints no obligation at all
//!   charge off -> exit 1,
//!     error: Trust strict verification failed for `<crate>::main`:
//!            1 obligation(s) were not fully verified
//!     with the v7/D3 note "`<crate>::twice_winc` ... is a local Clean-origin
//!     function ... this declaration's shape is not yet modeled, so the call
//!     fails closed rather than guessing", and the JSON row
//!     "[trust-absent-callee-assumption] call to absent callee
//!      `<crate>::twice_winc` (body not in the lowered bundle) may panic".
//!
//! THIS FIXTURE GOES VACUOUS IF THE CAP MOVES. At 94 fillers `twice_winc` fits
//! in the bundle again and both sides are green — measured. If
//! `NATIVE_TRUST_IR_MAX_BUNDLE_FUNCTIONS` is ever raised, RAISE THE FILLER
//! COUNT WITH IT, or this test silently stops testing anything. The cap's
//! `break` is currently SILENT (no `trust_bundle_trace` call), so there is no
//! diagnostic this fixture can pin to detect that.
//!
//! Negative control: `clean_origin_rust_call_unbundled_uncertified_callee_refused.rs`.

#![allow(dead_code)]

fn winc(x: u64) -> u64 { x.wrapping_add(1) }

// 95 fillers: `main` + 95 == NATIVE_TRUST_IR_MAX_BUNDLE_FUNCTIONS (96).
macro_rules! filler_defs {
    ($($n:ident),* $(,)?) => { $( fn $n(x: u64) -> u64 { x.wrapping_mul(3) } )* };
}
macro_rules! filler_calls {
    ($a:ident; $($n:ident),* $(,)?) => { $( $a = $n($a); )* };
}

filler_defs!(
    f00, f01, f02, f03, f04, f05, f06, f07, f08, f09,
    f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29,
    f30, f31, f32, f33, f34, f35, f36, f37, f38, f39,
    f40, f41, f42, f43, f44, f45, f46, f47, f48, f49,
    f50, f51, f52, f53, f54, f55, f56, f57, f58, f59,
    f60, f61, f62, f63, f64, f65, f66, f67, f68, f69,
    f70, f71, f72, f73, f74, f75, f76, f77, f78, f79,
    f80, f81, f82, f83, f84, f85, f86, f87, f88, f89,
    f90, f91, f92, f93, f94
);

clean {
    def twice_winc (x : UInt64) : UInt64 := winc (winc x)
}

fn main() {
    let mut a: u64 = 1;
    filler_calls!(a;
        f00, f01, f02, f03, f04, f05, f06, f07, f08, f09,
        f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
        f20, f21, f22, f23, f24, f25, f26, f27, f28, f29,
        f30, f31, f32, f33, f34, f35, f36, f37, f38, f39,
        f40, f41, f42, f43, f44, f45, f46, f47, f48, f49,
        f50, f51, f52, f53, f54, f55, f56, f57, f58, f59,
        f60, f61, f62, f63, f64, f65, f66, f67, f68, f69,
        f70, f71, f72, f73, f74, f75, f76, f77, f78, f79,
        f80, f81, f82, f83, f84, f85, f86, f87, f88, f89,
        f90, f91, f92, f93, f94
    );
    let _v = twice_winc(a);
}
