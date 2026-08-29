// LANE SC (follow-on) — FAMILY C1: the single-block aggregate with a NON-SCALAR by-value field.
// The task's standing warning is that taking this family "as-is" is a NET LOSS: satisfying the
// marker channel makes the derived body carry a STRUCT temp, which the flip fragment gate refuses
// (`flip.rs`, "struct temp used outside call-dest / bare store / whole read / scalar field read"),
// so the body gains `markers_exact` and LOSES its flip. This fixture is the pair the next lane
// needs to check BOTH halves of that claim on its own driver.
#![allow(dead_code, clippy::all)]

#[derive(Clone, Copy)]
pub struct AId(pub u64);

pub struct P3 {
    pub a: AId,
    pub b: usize,
    pub c: usize,
}
pub struct S3 {
    pub a: u64,
    pub b: usize,
    pub c: usize,
}

// h4 — ONE by-value STRUCT field (== memory_model::MemoryRegion::new). G25 measured this refused,
// first divergence `mk b0.0:live s0:adt:…`, identical to the corpus row.
pub fn h4_struct_field(a: AId, b: usize, c: usize) -> P3 {
    P3 { a, b, c }
}
// h1 — the CONVERTING control: the same aggregate from three SCALAR params.
pub fn h1_all_scalar(a: u64, b: usize, c: usize) -> S3 {
    S3 { a, b, c }
}
// h5 — the same, `const fn` (G25: also converts).
pub const fn h5_all_scalar_const(a: u64, b: usize, c: usize) -> S3 {
    S3 { a, b, c }
}
