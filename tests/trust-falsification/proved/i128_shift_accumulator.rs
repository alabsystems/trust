#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): a SIGNED i128 shift-reduction accumulator.
// `t += (x as i128) << 4` over `&[u8;16]` keeps t in [0, 65280], far inside i128. The i128 add
// overflow is BV-encoded (the Int accumulator bound doesn't bind to the disjoint BV operand vars);
// `v2_signed_bv_accumulator_constraints` now renders `acc in [0,65280]` / `addend in [0,4080]` in
// SIGNED BV onto the fresh `__trust_ovf_bv_*` operands, so the BV overflow formula is UNSAT.
pub fn f(a: &[u8; 16]) -> i128 {
    let mut t: i128 = 0;
    for &x in a {
        t += (x as i128) << 4;
    }
    t
}
