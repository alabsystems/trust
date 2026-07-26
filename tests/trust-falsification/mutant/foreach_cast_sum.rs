#![crate_type = "lib"]
// MUTANT of proved/foreach_cast_sum.rs: widens the ELEMENT type to u16 while keeping
// the accumulator at u16, so the per-iteration max is MAX(u16) = 65535 and the
// reduction bound is `t <= 0 + 16 * 65535 = 1048560`, which EXCEEDS u16::MAX (65535).
// The accumulator bound is therefore self-limiting — it does NOT discharge the
// checked-add overflow VC `t + (x as u16) <= u16::MAX`, which stays SAT (a real
// overflow: 16 elements at u16::MAX overflow a u16). The native (-full) lane must
// REFUSE this (fail closed / runtime-check), proving the bound is a genuine
// arithmetic fact and not a blanket "any for-each cast sum proves".
pub fn foreach_cast_sum(a: &[u16; 16]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        t += x as u16;
    }
    t
}
