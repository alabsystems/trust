#![crate_type = "lib"]
// PROVED (faithful narrowing — min-bounded value fits the target): `x.min(u32::MAX as u64)` is
// `<= u32::MAX`, so the high 32 bits are provably 0 and `as u32` is lossless. The cast-overflow
// edge's SAFE condition (re-extend(low 32 bits) == value) is VALID here, so `¬safe` is UNSAT —
// no error edge — and it PROVES. Locks that the new narrowing-cast check does NOT over-reject a
// genuinely-lossless narrowing. (exit 0)
pub fn clamp_cast(x: u64) -> u32 {
    x.min(u32::MAX as u64) as u32
}
