#![crate_type = "lib"]
// MUTANT / SOUNDNESS LOCK for Imp1's `operand_value_is_stable` guard. The cast source
// `a` is REASSIGNED after the cast, so the global `Eq(_d, a)` (conjoined onto EVERY VC)
// would — if emitted UNGUARDED — bind `_d` to the stale pre-reassignment value while a
// downstream VC reads `a` as its NEW value. Here `a = x.max(1)` gives `a >= 1`; an
// unguarded `Eq(_d, a)` plus `_d >= 1` would FALSELY prove `a >= 1` after `a = b`, so
// `100 % a` (b can be 0) would be wrongly discharged. The guard sees `a` has TWO stores
// (the `.max(1)` init and `a = b`) so it is NOT stable -> the `Eq` is dropped -> the
// Rem-by-zero stays a real obligation. This program GENUINELY divides by zero when b==0,
// so `-full` MUST refute it (exit 1). If this ever PROVES, the guard has regressed and
// reopened the P0 stale-link false-proof.
pub fn f(x: u64, b: u64) -> u64 {
    let mut a = x.max(1); // a >= 1 here
    let _d = a as u128; // value-preserving widen; unguarded Eq(_d, a) would carry a>=1
    a = b; // REASSIGN: a is now b, which may be 0
    100 % a // MUST refute: divide-by-zero when b == 0
}
