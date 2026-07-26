#![crate_type = "lib"]
// COMPLETENESS (bounded-reduction, fuzzer-revealed 2026-06-23): `t += x as ACC`
// over a fixed-size array is bounded (`t <= N * MAX(ELEM)`), so it provably cannot
// overflow. Trust used to RUNTIME-CHECK the accumulator's `[overflow:add]` (the
// fuzzer's `sum_foreach` / `sq_store` completeness-gap class) even though the
// shift form `t += (x as ACC) << k` already proved. Root cause: the per-add
// overflow check `t_old + addend <= MAX` needs BOTH the accumulator bound AND the
// addend's own bound; only the accumulator bound was emitted. Fixed by also
// emitting `addend <= per_max` in `build_accumulator_bound_facts`. This class is
// now a STATIC PROOF (default headline: 0 runtime-checked for the add), so the
// falsification gate guards it. 256 u8 elements, each <= 255, sum <= 65280 < u32::MAX.
pub fn f(a: &[u8; 256]) -> u32 {
    let mut t: u32 = 0;
    for &x in a {
        t += x as u32;
    }
    t
}
