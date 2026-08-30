//! Trust: minimal vanilla crate for the `--emit=trust-ir` artifact test —
//! a scalar-fragment body (lowers + splices), an RPIT body (the E0391 cycle
//! regression shape; must lower fail-open, never abort), and a body OUTSIDE
//! the lowerable fragment, which is what keeps the unsupported-shape and
//! leaf-demand histograms under test.
pub fn add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn evens(n: u32) -> impl Iterator<Item = u32> {
    (0..n).filter(|x| x % 2 == 0)
}

/// Outside the lowerable fragment: `dyn` dispatch has no static callee, so the
/// direct THIR lowering records `Call(dyn dispatch)` and declines the body.
///
/// This body exists to keep the coverage HISTOGRAMS under test. `evens` used to
/// play that role, but the lowering improved and it now lowers (symbolically);
/// with every body in this crate lowering, the assertions that a DECLINED body
/// publishes both its first-fail inventory and its collect-all leaf demand
/// would have had no subject and would have passed vacuously.
pub fn dyn_call(f: &dyn Fn(u32) -> u32) -> u32 {
    f(1)
}
