#![no_std]
//! PASS variant. Measured 2026-08-27: `targo trust check` exit 0,
//! `Gate: PASS [strict lane, exit 0]`, `Coverage: 1/1 (complete)`,
//! `Summary: 2 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 unknown (2 total)`.
//!
//! NON-VACUITY: neither proved row is `VcKind::Unreachable` (whose formula is
//! `Bool(true)`). The two rows are `[division_by_zero]` PROVED by ay-in-process
//! (kernel-rechecked) and its `[hardened_panic_boundary]
//! mir_assert::DivisionByZero` twin, PROVED.
//!
//! WHY UNSIGNED. `u32 / u32` emits a zero-divisor assert and NO overflow assert.
//! The signed twin `Overflow(Div)` — like `Overflow(Add/Sub/Mul/Shl)` — is NOT
//! discharged by the default `unix_hardened` profile even when the primary
//! arithmetic row PROVES, so any signed arithmetic here would fail the lane.
pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    if d == 0 { return 0; }
    n / d
}
