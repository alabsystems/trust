#![crate_type = "lib"]
// MUTANT of `proved/const_array_index.rs`: the index is now a runtime `usize`
// with NO `< arr.len()` guard, so `arr[i]` can read out of bounds. The bounds
// obligation `i >= 4` is now SAT (i could be >= 4), so neither the interval
// refutation nor the solver can discharge it; the verifier MUST fail closed
// (`[bounds] FAILED`), never certify.
pub fn const_array_index(i: usize) -> i32 {
    let arr = [10, 20, 30, 40];
    arr[i]
}
