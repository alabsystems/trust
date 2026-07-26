#![crate_type = "lib"]
// A PROVABLE arithmetic obligation alongside a TOTAL external call. `(a as u32)+1`
// cannot overflow (u8 widened is <= 255, +1 <= 256), and `Ord::min` cannot panic —
// the bridge models its result bound, so native lowering completes and the whole
// function proves under the default strict policy. Pairs with the mutant, which swaps
// the total `min` for a PANICKING `pow`. Guards #48: a provable obligation must NOT
// let an unmodeled panicking call slip through, yet a provable obligation alongside
// a TOTAL call must still prove (no over-rejection of the modeled-call case).
pub fn mixed_total_call(a: u8) -> u32 {
    let x = (a as u32) + 1;
    x.min(1000)
}
