//! End-to-end parity gate for immutable-reference method-forwarder cascades.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_clean::mirsem::{
    CalleeFact, function_fully_faithful_witness_with_callees,
};
use trust_types::VerifiableFunction;

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/ref-fwd-cascade-2026-07-17/dumps")
}

fn load_corpus() -> BTreeMap<String, VerifiableFunction> {
    let mut functions = BTreeMap::new();
    for entry in std::fs::read_dir(fixture_dir()).expect("fixture directory") {
        let path = entry.expect("fixture entry").path();
        if path.extension().and_then(|extension| extension.to_str()) != Some("json") {
            continue;
        }
        let function: VerifiableFunction =
            serde_json::from_slice(&std::fs::read(path).expect("fixture bytes"))
                .expect("fixture parses");
        assert!(functions.insert(function.def_path.clone(), function).is_none());
    }
    functions
}

#[test]
fn committed_reference_forwarder_cascade_passes_the_production_gate() {
    let score = trust_clean::prove_dump_dir(&fixture_dir()).expect("production census succeeds");
    assert_eq!(score.total, 10, "the committed census must stay complete");
    assert_eq!(score.fully_faithful, 10, "every row must pass the complete production gate");
    assert_eq!(score.kernel_rejected, 0);
    assert_eq!(score.declined, 0);
    assert_eq!(
        score.fully_faithful,
        score.fully_faithful_via_trustir + score.fully_faithful_mirsem_fallback,
        "the trust-ir-primary/fallback partition must stay exact"
    );
}

#[test]
fn reference_forwarders_have_semantic_witnesses_callees_first() {
    let functions = load_corpus();
    assert_eq!(functions.len(), 10, "the committed census must stay complete");

    let mut certified = BTreeMap::<String, CalleeFact>::new();
    let mut progress = true;
    while progress {
        progress = false;
        for (path, function) in &functions {
            if certified.contains_key(path) {
                continue;
            }
            if function_fully_faithful_witness_with_callees(function, &certified)
                .is_some_and(|certificate| certificate.is_modulo_3())
            {
                certified.insert(path.clone(), CalleeFact::of_certified(function));
                progress = true;
            }
        }
    }

    // This is deliberately the resolver-focused MirSem subcheck. The complete
    // production gate above also admits the remaining cmp chain through its
    // trust-ir-primary lane and enforces safety/requires discharge.
    for required in [
        "direct_fwd",
        "wrap_set",
        "cfg_has_name",
        "cfg_no_name",
        "std::option::Option::<i32>::is_some",
        "std::option::Option::<i32>::is_none",
        "std::option::Option::<u8>::is_some",
    ] {
        assert!(
            certified.contains_key(required),
            "`{required}` did not certify in the real callee cascade; certified={:?}",
            certified.keys().collect::<Vec<_>>()
        );
    }
}
