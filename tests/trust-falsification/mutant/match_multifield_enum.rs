#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: the A arm uses `+` (real add), which overflows when
// a + b > u32::MAX. MUST be refused (exit 1). Guards that the TWO variant fields a and
// b are independent real values — if the variant-field resolution aliased them (e.g.
// both to field 0), `a + b` behaviour would differ and a mis-model could hide it.
pub enum E {
    A(u32, u32),
    B,
}
pub fn match_multifield_enum(e: E) -> u32 {
    match e {
        E::A(a, b) => a + b,
        E::B => 0,
    }
}
