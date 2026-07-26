#![crate_type = "lib"]
// A doubly-guarded narrowing cast. HISTORY: pre-9f4b2c8417 Trust discharged a
// fabricated cast-range obligation `x>=0 ∧ x<256 ∧ Or([x<0, x>255])` via the
// clean CIC kernel (Or.rec case-split + integer-strengthened chain edges, task
// #38). Since 9f4b2c8417 defined int `as` casts emit NO obligation (defined
// Rust semantics, cannot panic) — zero-obligation drop-in ACCEPTANCE fixture.
pub fn guarded_cast(x: i32) -> u8 {
    if x >= 0 {
        if x < 256 { x as u8 } else { 0 }
    } else {
        0
    }
}
