// LANE SC (follow-on) — `expr::types::BigNat::is_zero::{closure#0}`: the `|&l| l == 0` closure
// whose ONLY difference from a converting twin is the DESTRUCTURING PARAMETER PATTERN.
#![allow(dead_code, clippy::all)]

// the CONVERTING twin, measured by G25: a plain `&u64` parameter — `markers_exact: true`
pub fn g2a(x: &u64) -> bool {
    *x == 0
}

pub struct BigNat {
    limbs: Vec<u64>,
}

impl BigNat {
    // THE CORPUS SHAPE: `limbs.iter().all(|&l| l == 0)`
    pub fn is_zero_ref_pat(&self) -> bool {
        self.limbs.iter().all(|&l| l == 0)
    }
    // the same with a NON-destructuring closure parameter
    pub fn is_zero_plain(&self) -> bool {
        self.limbs.iter().all(|l| *l == 0)
    }
}

// the two closure forms in isolation, so the extra local is attributable to the pattern alone
pub fn c_refpat() -> impl Fn(&u64) -> bool {
    |&l| l == 0
}
pub fn c_plain() -> impl Fn(&u64) -> bool {
    |l| *l == 0
}
