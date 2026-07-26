#![crate_type = "lib"]
// PROVED (widening cast skipped by the narrowing-only guard): `num_partitions: u32 as u64` is a
// value-preserving WIDENING (dst_w 64 > src_w 32), so the cast-overflow check's `dst_w < src_w`
// guard skips it entirely — no spurious obligation, no false refutation. Locks that the new
// check fires ONLY on narrowing casts (never on the astream `num_partitions as u64` divisor
// widening). MUST verify (exit 0).
pub fn widen(num_partitions: u32) -> u64 {
    num_partitions.max(1) as u64
}
