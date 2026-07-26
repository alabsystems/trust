#![crate_type = "lib"]
// Manual-INDEX bounded reduction (#50): `for i in 0..4 { t += a[i] as u16 }` — the
// ubiquitous indexed-sum idiom. rustc keeps the per-iteration add-overflow runtime check;
// Trust discharges it BY DEFAULT via the accumulator bound `t <= K * MAX(ELEM)` where the
// trip count `K = end - start = 4` comes from the exclusive `Range` driving the loop
// (`index_range_reduction_bound`) and the per-addend bound `255` is the loaded element's
// own `u8` type. Pairs with the discriminating mutants (overflow-by-size, repeat-index).
pub fn reduction_index_range(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    for i in 0..4 {
        t += a[i] as u16;
    }
    t
}
