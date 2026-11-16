// Fixture source for crates/trust-vcgen/tests/deref_store_reload_realmir.rs.
//
// A store through `&mut` followed by a reload of the same place, in ONE block,
// after a checked add in the PREVIOUS block. The hardened twin of the reload's
// `Overflow(Sub)` assert used to drop the entry fact `_2.0 == count* + 1` (it
// mentions `count*`, which the block writes) and was refuted at `_2.0 = 0`.

/// SAFE: the reload reads `old + 1 >= 1`.
pub fn bump(count: &mut usize) -> usize {
    *count += 1;
    *count - 1
}

/// UNSAFE: `old + 1 - 2` underflows at `old = 0`.
pub fn bump_then_sub_two(count: &mut usize) -> usize {
    *count += 1;
    *count - 2
}

/// UNSAFE: the second store replaces the bumped value with `v`, so the reload
/// is `v - 1`, which underflows at `v = 0`. The entry fact about `old + 1`
/// must not reach the value read after the second store.
pub fn bump_then_overwrite(count: &mut usize, v: usize) -> usize {
    *count += 1;
    *count = v;
    *count - 1
}

/// UNSAFE: the guard tests the value BEFORE the store; the reload reads 0.
pub fn guard_then_zero(count: &mut usize) -> usize {
    if *count > 0 {
        *count = 0;
        return *count - 1;
    }
    0
}
