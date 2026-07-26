#![crate_type = "lib"]
// REGRESSION (assert-refutation soundness, adversarial hunt 2026-06-23): a
// PARAMETER mutated through a projection store. After `a.0 = v`, `a.0 == v` holds
// for ALL inputs — the assert can never panic, so `-full` MUST NOT refute it.
// It once did: `v2_input_free_locals` admitted the parameter `a` as input-free
// and modelled the field `a.0` as a free leaf, missing that `a.0 = v` reassigns
// it (a projected store does not go through a direct `Assign` to the base local),
// so `a.0 != v` was spuriously SAT. Fixed by excluding any local with a projected
// store (and any `&mut`/`&raw` borrow) from input-free — its post-mutation value
// is never treated as a free leaf. Verifies (exit 0), never refuted.
pub fn f(mut a: (u32, u32), v: u32) -> u32 {
    a.0 = v;
    assert!(a.0 == v);
    a.0
}
