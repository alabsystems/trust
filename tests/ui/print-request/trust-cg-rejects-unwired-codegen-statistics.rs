//! LLVM pass diagnostics and generic codegen statistics have no Trust-CG
//! implementation yet. Every spelling must fail before code generation rather
//! than inheriting a silent no-op backend hook.

//@ needs-trust-cg-backend
//@ revisions: print_passes time_passes print_stats stats_json
//@ build-fail
//@ dont-check-compiler-stderr
//~? ERROR LLVM pass controls and codegen statistics are not implemented by the trust-cg backend
//@[print_passes] compile-flags: -Zprint-llvm-passes
//@[time_passes] compile-flags: -Ztime-llvm-passes
//@[print_stats] compile-flags: -Zprint-codegen-stats
//@[stats_json] compile-flags: -Zprint-codegen-stats-json=trust-cg-stats.json
//@ compile-flags: --crate-type=rlib -Cpanic=abort -Cdebuginfo=0 -Ccodegen-units=1 -Zcodegen-backend=trust-cg -Ztrust-verify=off

pub fn admitted_scalar() -> u64 {
    1
}
