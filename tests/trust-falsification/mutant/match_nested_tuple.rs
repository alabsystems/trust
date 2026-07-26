#![crate_type = "lib"]
// MUTANT of proved/match_nested_tuple.rs + the DISCRIMINATING soundness guard for
// the recursive nested-aggregate model: the Some arm asserts `a == b`, which CAN
// FAIL — the two tuple fields are independent. The verifier MUST refuse it (exit 1).
// If the nested-aggregate leaf indexing were wrong (e.g. `a` and `b` aliased the
// SAME CHC leaf), `assert!(a == b)` would FALSELY prove and this mutant would
// survive — a soundness hole. A correct model keeps the leaves independent, so the
// assert is refutable and the function fails closed.
pub fn match_nested_tuple(o: Option<(u32, u32)>) -> u32 {
    match o {
        Some((a, b)) => {
            assert!(a == b);
            0
        }
        None => 0,
    }
}
