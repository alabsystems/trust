#![crate_type = "lib"]
// MUTANT (cast-bound soundness twin): `n.rem_euclid(7)` is in `[0,6]`, so the value 6 is OUT OF
// BOUNDS for a length-6 array (valid 0..=5). The propagated bound `(cast) <= 6` is SOUND but
// COMPATIBLE with the violation `(cast) >= 6` (6 is not > 6), so the incompatible-const-bounds
// discharge does NOT fire — the access stays unproven and `-full` MUST refute (exit 1). Pins that
// the propagated bound carries the source's ACTUAL max (|c|-1) and is self-limiting.
pub fn f(n: i32, arr: &[u8; 6]) -> u8 {
    arr[n.rem_euclid(7) as usize]
}
