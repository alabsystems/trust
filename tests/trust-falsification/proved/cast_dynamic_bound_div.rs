#![crate_type = "lib"]
// PROVED (Imp1, value-preserving widening cast carries a DYNAMIC bound): astream's
// canonical partition-assignment core. `n = num_partitions.max(1) as u64` is `>= 1`
// (the `.max(1)` Ord fact `n_u32 >= 1`), and the value-preserving `as u64` cast is the
// IDENTITY, so `n_u64 == n_u32 >= 1` — the divisor of `h % n` is provably non-zero and
// the Rem-by-zero obligation discharges. Before Imp1 the cast emitted only the STATIC
// source range (`0 <= n_u64 <= u32::MAX`, which ADMITS n=0), so `h % n` was [unknown].
// `native_widening_cast_facts` now also conjoins `Eq(n_u64, n_u32)` (source-stability
// guarded), carrying the dynamic `>= 1` across the cast. MUST verify (exit 0).
pub fn assign_partition(num_partitions: u32, h: u64) -> u32 {
    let n = num_partitions.max(1) as u64;
    (h % n) as u32
}
