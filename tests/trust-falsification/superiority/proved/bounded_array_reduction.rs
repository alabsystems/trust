#![crate_type = "lib"]
// A bounded fixed-array REDUCTION (#50): summing a `&[u8; 4]` into a u16. rustc keeps
// the per-iteration mul... add-overflow runtime check; Trust discharges it BY DEFAULT
// via the accumulator bound `t <= 4 * 255 = 1020 < u16::MAX`. The loop abstraction
// otherwise leaves `t` unbounded; `build_accumulator_bound_facts` recognizes the
// single-loop for-each over a fixed array with a self-add of the widened element and
// emits the globally-true, self-limiting bound. Pairs with the discriminating mutants
// (overflow-by-size, nested-loop, range-index-link).
pub fn bounded_array_reduction(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        t += x as u16;
    }
    t
}
