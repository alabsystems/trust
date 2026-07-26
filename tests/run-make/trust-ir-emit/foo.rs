//! Trust: minimal vanilla crate for the `--emit=trust-ir` artifact test —
//! a scalar-fragment body (lowers + splices) and an RPIT body (the E0391
//! cycle regression shape; must lower fail-open, never abort).
pub fn add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn evens(n: u32) -> impl Iterator<Item = u32> {
    (0..n).filter(|x| x % 2 == 0)
}
