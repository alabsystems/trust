#![crate_type = "lib"]
// Was MUTANT of proved/channel_to_u8.rs (the `v <= 255` guard dropped).
// RECLASSIFIED per 9f4b2c8417: defined int `as` truncation is valid Rust —
// `v as u8` truncates (v % 256) and cannot panic — so Trust accepts it with
// NO obligation. HONESTY NOTE: zero-obligation drop-in ACCEPTANCE fixture,
// not a proof (no verification headline). Kept in proved/ so a future change
// that re-refutes defined casts flips the gate RED. Panic-adjacent coverage:
// mutant/cast_trunc_{index_oob,div_zero,guarded_index_oob}.rs.
pub fn cast_truncate_unguarded(v: u32) -> u8 {
    v as u8
}
