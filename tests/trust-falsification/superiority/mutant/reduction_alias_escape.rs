#![crate_type = "lib"]
// SOUNDNESS REGRESSION for the accumulator bound (#50). The accumulator `t` is mutated
// through a `&mut t` ALIAS (`*p = 65000`) before the reduction, so its true value can be
// 65000 + (4 * 255) = 66020 > u16::MAX — a genuine overflow. The whole-local def scan in
// `accumulator_init_const` only sees `t = 0` and the self-add, so WITHOUT the
// mutable-borrow guard it would emit the FALSE fact `t <= 1020` and vacuously discharge
// the overflow check (a false PROVE). The guard recognizes `&mut t` and withholds the
// bound, leaving the obligation to fail / runtime-check (the unsafe add is retained).
// This fixture goes GREEN-as-mutant precisely BECAUSE the bound is correctly NOT emitted.
pub fn reduction_alias_escape(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    let p = &mut t;
    *p = 65000;
    for &x in a {
        t += x as u16;
    }
    t
}
