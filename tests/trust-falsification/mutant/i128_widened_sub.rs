#![crate_type = "lib"]
// MUTANT of proved/i128_widened_sub.rs: the operands are now full-range i128 (no
// i64 widening), so `a - b` CAN overflow (e.g. i128::MIN - i128::MAX). The
// no-overflow obligation becomes SAT; the verifier MUST fail closed. Guards the
// i128 widening recognition against pinning an arbitrary i128 to i64 range.
pub fn i128_widened_sub(a: i128, b: i128) -> i128 {
    a - b
}
