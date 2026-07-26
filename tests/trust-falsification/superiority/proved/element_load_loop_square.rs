#![crate_type = "lib"]
// In-loop widening MULTIPLY overflow, proved BY DEFAULT (#50). `(a[i] as u32) * (a[i] as
// u32)` cannot overflow u32 (each widened u8 factor is <= 255, product <= 65025), and the
// non-loop form already proves. The in-loop form previously fell to a retained runtime
// mul-overflow check: the canonical mul VC is a QF_BV goal, and inside a loop its formula
// carries a switch-discriminant context disjunct `_8 == 0 || _8 == 1`, on which the
// interval backend's `prove_no_overflow` used to BAIL (`return false`) before reaching the
// provable BV mul goal. The fix skips such conjoined context `Or`s (sound: dropping a
// conjoined term only weakens the premise of an UNSAT proof), so the multiply discharges
// via the proof-grade interval lane — instead of ay's QF_BV `:rule trust` proof, which the
// carcara cross-check correctly rejects as unreconstructed. Pairs with the
// genuine-overflow mutant (`element_load_loop_u8_square`).
pub fn element_load_loop_square(a: &[u8; 4], out: &mut [u32; 4]) {
    for i in 0..4 {
        out[i] = (a[i] as u32) * (a[i] as u32);
    }
}
