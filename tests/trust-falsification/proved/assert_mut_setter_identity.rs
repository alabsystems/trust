#![crate_type = "lib"]
// REGRESSION (assert-refutation soundness, adversarial hunt 2026-06-23): a local
// mutated through a `&mut` passed to a setter. After `set(&mut a, v)`, `a == v`
// holds for ALL inputs — the assert can never panic, so `-full` MUST NOT refute
// it. The `&mut a` borrow can reassign `a` WITHOUT a direct `Assign`, so the
// single-assignment leaf-read rule would model the stale pre-call `a == x` and
// false-refute `a != v`. Fixed by excluding `&mut`/`&raw`-borrowed locals from
// input-free. Verifies (exit 0), never refuted.
fn set(p: &mut u32, v: u32) {
    *p = v;
}
pub fn f(x: u32, v: u32) -> u32 {
    let mut a = x;
    set(&mut a, v);
    assert!(a == v);
    a
}
