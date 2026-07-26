#![crate_type = "lib"]
// Was MUTANT of proved/cast_lossless_narrow.rs (the `& 0xFF` mask dropped).
// RECLASSIFIED per 9f4b2c8417: defined int `as` truncation is valid Rust —
// it never panics and is not UB — so Trust no longer fabricates a losslessness
// obligation and this compiles green. HONESTY NOTE: this is a zero-obligation
// drop-in ACCEPTANCE fixture, not a proof (no "Trust verification:" headline is
// emitted). It is kept in proved/ so the acceptance is itself gate-covered: if
// a future change re-fabricates a lossy-cast refutation, this flips the gate
// RED. The real panic coverage the old mutant stood in for now lives in
// mutant/cast_trunc_{index_oob,div_zero,guarded_index_oob}.rs.
pub fn cast_truncate_unmasked(x: u32) -> u8 {
    x as u8
}
