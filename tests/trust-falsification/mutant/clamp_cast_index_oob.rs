#![crate_type = "lib"]
// MUTANT (clamp-cast soundness twin): `i.clamp(0, 12)` can yield 12, which is OUT OF BOUNDS for a
// length-10 array, so this genuinely panics at runtime and `-full` MUST refute (exit 1). The fact
// `(j as usize) <= 12` is SOUND but does NOT discharge `< 10` — pinning that the propagated bound
// carries the clamp's ACTUAL hi (not the array length) and is self-limiting.
pub fn f(i: i32, arr: &[u8; 10]) -> u8 {
    let j = i.clamp(0, 12);
    arr[j as usize]
}
