#![crate_type = "lib"]
// MUTANT + DISCRIMINATING soundness guard for the nested-struct model: the Some arm
// asserts `p.x == p.y`, which CAN FAIL (the two struct fields are independent). The
// verifier MUST refuse it (exit 1). If the struct-id collision (Pair vs Option both
// id 0) re-appeared, the Pair payload would resolve to the WRONG struct and the
// fields could alias / mis-resolve — a soundness hole this mutant catches.
pub struct Pair {
    x: u32,
    y: u32,
}
pub fn match_struct_payload(o: Option<Pair>) -> u32 {
    match o {
        Some(p) => {
            assert!(p.x == p.y);
            0
        }
        None => 0,
    }
}
