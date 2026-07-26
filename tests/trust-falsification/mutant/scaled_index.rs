#![crate_type = "lib"]
// MUTANT of `proved/scaled_index.rs`: the guard is loosened to `i < 5`, so `i`
// can be 4 and `i * 2 == 8` is out of bounds for the length-8 array. The lift
// gives `i <= 4 ⟹ i*2 <= 8`, which does NOT contradict `i*2 >= 8` (8 >= 8), so
// the chain cannot close; the verifier MUST fail closed.
pub fn scaled_index(a: &[i32; 8], i: usize) -> i32 {
    if i < 5 { a[i * 2] } else { 0 }
}
