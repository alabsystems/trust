#![crate_type = "lib"]
// Source of the BMC bounded-reduction real-MIR fixtures. Kept beside the dumps so
// every row can be re-derived (see bmc_reduction_real_mir.rs for the command).
//
// `shift_reduction_overflow`: `tests/trust-falsification/mutant/shift_reduction_overflow.rs`
// verbatim — `[u8; 64]` summed into a `u8` accumulator with a `<< 4` per element.
// It GENUINELY overflows (witness elem62 = 1, elem63 = 15).
pub fn shift_reduction_overflow(a: &[u8; 64]) -> u8 {
    let mut t: u8 = 0;
    for &x in a {
        t += (x as u8) << 4;
    }
    t
}

// The SAFE twin: `[u8; 16]` shifted by 4 into a `u16` — `16 * (255 << 4) = 65280`,
// which fits `u16::MAX`. Must NEVER be refuted.
pub fn safe_widening_reduction(a: &[u8; 16]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        t += (x as u16) << 4;
    }
    t
}
