//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ check-fail
//! ADVERSARIAL CONTROL (2026-09-24), split out of `reject_diverging_call_gap.rs`
//! when that file was re-derived green. A call whose callee returns an
//! uninhabited ENUM (not the literal `!`) is also lowered to `Call { target: None }`
//! (`LintAndRemoveUninhabited`), and codegen again finishes it with a bare
//! `unreachable` in this frame. Its non-return is NOT established by a
//! `TyKind::Never` output, so the lowering keeps it opaque and the memory-safe lane
//! must keep REFUSING it: a row whose body can reach an unestablished bare
//! `unreachable` never passes as monitored. Measured on stage-1 2026-09-24: rc=1.
pub enum Void {}

pub fn never_void() -> Void {
    //~^ ERROR Trust memory-safe verification failed for `reject_uninhabited_return_call_gap::never_void`
    loop {}
}

pub fn pick2(v: &[u32], i: usize) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_uninhabited_return_call_gap::pick2`
    if i >= v.len() {
        let _x: Void = never_void();
    }
    v[i] + 1
}
