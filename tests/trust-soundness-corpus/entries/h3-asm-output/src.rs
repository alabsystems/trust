// trust-soundness-corpus entry `h3-asm-output` (H3 (OPAQUE-ASM-OUTPUT)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
use core::arch::asm;

pub fn h3a_out_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    unsafe { asm!("mov {0}, #4", out(reg) k) };
    t[k]
}

// Twin (h3c2): the bound is established after the asm.
pub fn h3c2_fact_after_asm_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let mut m = n;
    unsafe { asm!("add {0}, {0}, #4", inout(reg) m) };
    let k = m & 3;
    t[k]
}
