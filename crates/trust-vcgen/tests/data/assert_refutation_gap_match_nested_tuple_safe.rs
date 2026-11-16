#![crate_type = "lib"]
// SOURCE OF `assert_refutation_gap_match_nested_tuple_safe.json`, kept next to it
// so the fixture's provenance is in-tree and re-dumpable. It is the SAFE twin of
// `tests/trust-falsification/mutant/match_nested_tuple.rs`: each payload field is
// compared to ITSELF, so both asserts hold for every input and both panic blocks
// are unreachable. It deliberately does NOT live in the falsification corpus —
// that corpus is a compiler-level gate this crate cannot run, and the property
// under test here is a vcgen one: the payload-projection and discriminant pins
// must ground these formulas and leave them UNSAT.
//
// TWO SEPARATE asserts, one per field, rather than one `a == a && b == b`: that
// exercises BOTH sibling projections (`o@1.0.0` and `o@1.0.1`, whose disjointness
// is the claim `refutation_names_may_alias` makes) while keeping each panic block
// on a SINGLE control-flow path, which is what the lane's per-path split and the
// kernel certifier both want.
//
//   trustc --edition 2021 --crate-type lib --emit=metadata -Cpanic=abort \
//          -Ztrust-policy=advisory \
//          -Ztrust-dump=mir-only:<dir> \
//          crates/trust-vcgen/tests/data/assert_refutation_gap_match_nested_tuple_safe.rs
pub fn match_nested_tuple_safe(o: Option<(u32, u32)>) -> u32 {
    match o {
        Some((a, b)) => {
            assert!(a == a);
            assert!(b == b);
            0
        }
        None => 0,
    }
}
