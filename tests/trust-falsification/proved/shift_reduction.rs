#![crate_type = "lib"]
// COMPLETENESS (fuzzer-revealed 2026-06-24, `shift`): `t += (x as u16) << 4` over
// `[u8;16]`. Bounded: each addend `<= 255<<4 = 4080`, sum `<= 16*4080 = 65280 <
// u16::MAX`. The per-add overflow check `acc_old + addend <= MAX` was runtime-checked:
// the loose `acc <= bound` over-approximates `acc_old` by one addend (`<= 69360 >
// 65535`), and the `<<4` addend is a mixed Int/BitVec round-trip ay leaves Unknown.
// Fixed by emitting the TIGHT post-add sum bound `acc_old + addend <= bound`
// (build_accumulator_bound_facts) + a structural arithmetic discharge
// (conjuncts_carry_arith_contradiction + Or case-split) that refutes both overflow
// branches. The genuinely-overflowing `->u8` form stays runtime-checked (mutant below).
pub fn f(a: &[u8; 16]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        t += (x as u16) << 4;
    }
    t
}
