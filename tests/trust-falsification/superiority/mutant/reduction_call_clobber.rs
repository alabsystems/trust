#![crate_type = "lib"]
// SOUNDNESS REGRESSION for the accumulator bound (#50). The accumulator `t` is clobbered
// by a CALL (`t = seed()`) — a `Terminator::Call` whose dest is `t` — before the
// reduction, so its true value is an unconstrained return (here 65000), and
// 65000 + (4 * 255) = 66020 > u16::MAX overflows. The statement-only def scan in
// `accumulator_init_const` cannot see the call-terminator write, so WITHOUT the
// call-dest guard it would emit the FALSE fact `t <= 1020` and vacuously discharge the
// overflow check (a false PROVE). The guard bails on any `Call` whose dest is the
// accumulator, withholding the bound so the unsafe add stays retained.
#[inline(never)]
fn seed() -> u16 {
    65000
}

pub fn reduction_call_clobber(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    t = seed();
    for &x in a {
        t += x as u16;
    }
    t
}
