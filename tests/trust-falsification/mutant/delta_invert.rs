#![crate_type = "lib"]
// MUTANT of proved/delta_invert.rs: the i32::MIN exclusion is dropped, so the
// negation overflows at exactly one input. MUST be refused (exit 1).
pub fn delta_invert(n: i32) -> i32 {
    -n
}
