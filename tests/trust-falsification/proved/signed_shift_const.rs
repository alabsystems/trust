#![crate_type = "lib"]
// A constant signed right-shift. The shift-amount obligation is a CLOSED
// contradiction over compile-time constants — `Or([2 < 0, 2 >= 32])` — which the
// clean CIC kernel certifies IN-PROCESS (zero-trust de Bruijn re-check) via the
// closed-constant refutation path, and which the native trust-mc CHC/PDR runner
// proves under -full. The shift amount `2` is statically in `0..32`, so both the
// shift-range check and the paired shift-width cast check discharge: -full
// reports both kernel-Certified (task #35 — superior to rustc, which only inserts
// a runtime panic for variable shifts and cannot certify this statically).
pub fn signed_shift_const(a: i32) -> i32 {
    a >> 2
}
