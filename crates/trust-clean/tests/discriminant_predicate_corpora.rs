// Production-pipeline regression coverage for the general discriminant-predicate
// lane. These are real rustc MIR dumps, not hand-authored recognizer examples.
//
// The two versioned corpora intentionally cover different dimensions:
// - enum-discr-predicates: non-Option/Result enums and both direct/Not forms;
// - optres-discr-innertypes: payload breadth, including niche-optimized types.
//
// The adjacent slice-len-isempty corpus is deliberately NOT included here. Its
// `results-baseline.tsv` and PROVENANCE mark it as a deferred SHAPE_GAP; it must
// only join a fully-faithful assertion after the PtrMetadata/Len lane lands.

use std::path::Path;

use trust_clean::{ProveScorecard, prove_dump_dir};

fn prove_fixture_dumps(fixture: &str) -> ProveScorecard {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join(fixture).join("dumps");
    assert!(dir.is_dir(), "fixture dump directory missing at {}", dir.display());
    prove_dump_dir(&dir).unwrap_or_else(|err| panic!("read {}: {err}", dir.display()))
}

fn assert_all_mirsem_fully_faithful(fixture: &str, expected_total: usize) {
    let sc = prove_fixture_dumps(fixture);

    assert_eq!(sc.total, expected_total, "every checked-in {fixture} dump must deserialize");
    assert_eq!(sc.kernel_rejected, 0, "kernel rejected a {fixture} witness: {:?}", sc.rejections);
    assert_eq!(
        sc.fully_faithful, expected_total,
        "every checked-in {fixture} body must remain fully faithful: {:?}",
        sc.rejections
    );
    assert_eq!(
        sc.fully_faithful_via_trustir, 0,
        "{fixture} is a MirSem discriminant-predicate lane, not a trust-ir shape lane"
    );
    assert_eq!(
        sc.fully_faithful_mirsem_fallback, expected_total,
        "every {fixture} certificate must traverse the intended MirSem lane"
    );
}

#[test]
fn general_enum_discriminant_predicates_are_fully_faithful() {
    assert_all_mirsem_fully_faithful("enum-discr-predicates-2026-07-16", 9);
}

#[test]
fn option_result_discriminants_are_payload_type_agnostic() {
    assert_all_mirsem_fully_faithful("optres-discr-innertypes-2026-07-16", 11);
}
