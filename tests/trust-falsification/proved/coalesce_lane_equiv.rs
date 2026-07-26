#![crate_type = "lib"]
// PROVED (coalescing / lane-equivalence — the aterm wide-wrap-tail class —
// reduced to the bounds-safety refinement this Trust build statically
// discharges). The screen is a pure function of the output-byte log regardless
// of chunking, so the fast "bulk" write lane must REFINE the reference
// "single-char" lane. Here: a width-2 glyph wrapping off the last column writes
// the skipped tail cell. The single-char lane keeps that write inside the row
// (power-of-2 width N, index = col & (N-1) ∈ [0, N)); the bulk lane must write
// the SAME in-bounds cell. The interval backend proves `col & 7 ∈ [0, 8)`.
//
// NOTE: the stronger value-equality form (bulk's tail cell == single's, i.e. it
// blanks with the current background, not 0) is a Postcondition obligation,
// which on this build is gated on trust-wp's pure-expr lowering — see
// docs/BOOTSTRAP_FROM_SCRATCH.md. The temporal 2-safety form is checked by the
// aterm `coalesce_model` under `ty`; the dynamic form by the aterm differential
// gate. This fixture is the memory-safety refinement of the same property.
pub fn wrap_tail_write(row: &mut [u32; 8], col: usize, bg: u32) {
    row[col & 7] = bg; // FIXED: refines the single lane's in-bounds tail write
}
