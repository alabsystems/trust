// The dependency of trust-proof-session-dependency-mir, built three ways by
// rmake.rs. Leaf bodies with no calls, so the verified dependent bundles them
// as members and reads their encoded MIR: at `mir-opt-level` 2 GVN folds the
// repeated division and the checked arithmetic around it, so that MIR depends
// on the pipeline that built it.

#[inline]
pub fn clamp_sum(a: u32, b: u32) -> u32 {
    if a < 1000 && b < 1000 { a + b } else { 0 }
}

#[inline]
pub fn quarters(a: u32) -> u32 {
    let b = a / 4;
    let c = a / 4;
    b + c
}
