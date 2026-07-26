#![crate_type = "lib"]
// MUTANT (guarded-subtraction soundness twin): an UNGUARDED `a - b` over unsigned
// UNDERFLOWS whenever a < b (e.g. a=0, b=1). Genuinely violable, so `-full` MUST refute
// (exit 1). Pins that the guarded-subtraction discharge fires ONLY when the `a >= b`
// guard is present, never on a bare subtraction.
pub fn f(a: u8, b: u8) -> u8 {
    a - b
}
