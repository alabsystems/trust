#![crate_type = "lib"]
// Was MUTANT of proved/guarded_cast.rs (the upper `x < 256` guard dropped, so
// `x as u8` is value-changing for x > 255). RECLASSIFIED per 9f4b2c8417:
// signed→unsigned `as` narrowing is DEFINED Rust semantics (bit-pattern
// truncation, never a panic), so Trust accepts it with NO obligation.
// HONESTY NOTE: zero-obligation drop-in ACCEPTANCE fixture, not a proof (no
// verification headline). Kept in proved/ so a future change that re-refutes
// defined casts flips the gate RED. The "partial guard does not launder a
// truncated INDEX" hazard is separately covered by
// mutant/cast_trunc_guarded_index_oob.rs (which genuinely panics and refutes).
pub fn cast_truncate_signed_partial_guard(x: i32) -> u8 {
    if x >= 0 { x as u8 } else { 0 }
}
