//! Current-corpus regression for the authenticated bit-method composition.
//!
//! The 12 compiler-authenticated direct leaves, 8 W-PREOP count-zero leaves,
//! and 12 W-CAST signed delegates must all certify modulo 3. Detached controls
//! still pin the intrinsic marker, classifier, arity, and ABI boundaries.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_clean::mirsem::{
    CalleeFact, PureTotalIntrinsic, function_fully_faithful_witness_with_callees,
};
use trust_types::{Terminator, VerifiableFunction};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/stdlib-leaf-bitmethods-2026-07-16")
}

fn load(rel: &str) -> VerifiableFunction {
    let bytes = std::fs::read(corpus_dir().join(rel)).expect("bitmethods fixture present");
    serde_json::from_slice(&bytes).expect("bitmethods fixture parses")
}

fn sole_call(function: &VerifiableFunction) -> (&str, usize, bool) {
    let calls: Vec<_> = function
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func, args, is_foreign, .. } => {
                Some((func.as_str(), args.len(), *is_foreign))
            }
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{} must contain exactly one Call", function.def_path);
    calls[0]
}

fn unsigned_primary_registry() -> BTreeMap<String, CalleeFact> {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    let mut registry = BTreeMap::new();
    for ty in ["u8", "u16", "u32", "u64"] {
        for (method, expected) in [
            ("leading_zeros", PureTotalIntrinsic::Ctlz),
            ("swap_bytes", PureTotalIntrinsic::Bswap),
            ("reverse_bits", PureTotalIntrinsic::Bitreverse),
        ] {
            let rel = format!("dumps/num__<impl {ty}>__{method}.json");
            let function = load(&rel);
            let (callee, arity, foreign) = sole_call(&function);
            assert_eq!(PureTotalIntrinsic::classify(callee), Some(expected), "{rel}");
            assert_eq!(arity, 1, "{rel}");
            assert!(!foreign, "{rel}");
            let witness = function_fully_faithful_witness_with_callees(&function, &empty);
            assert!(
                witness.as_ref().is_some_and(|certificate| certificate.is_modulo_3()),
                "{rel}: authenticated direct intrinsic must have a kernel witness"
            );
            registry.insert(function.def_path.clone(), CalleeFact::of_certified(&function));
        }
    }
    registry
}

#[test]
fn all_thirty_two_bit_method_leaves_certify_modulo_3() {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    let registry = unsigned_primary_registry();
    let mut certified = 12usize;

    for ty in ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"] {
        let rel = format!("dumps/num__<impl {ty}>__count_zeros.json");
        let function = load(&rel);
        let witness = function_fully_faithful_witness_with_callees(&function, &empty);
        assert!(
            witness.as_ref().is_some_and(|certificate| certificate.is_modulo_3()),
            "{rel}: W-PREOP must have a kernel witness"
        );
        certified += 1;
    }
    for ty in ["i8", "i16", "i32", "i64"] {
        for method in ["leading_zeros", "swap_bytes", "reverse_bits"] {
            let rel = format!("dumps/num__<impl {ty}>__{method}.json");
            let function = load(&rel);
            let witness = function_fully_faithful_witness_with_callees(&function, &registry);
            assert!(
                witness.as_ref().is_some_and(|certificate| certificate.is_modulo_3()),
                "{rel}: W-CAST delegate must have a kernel witness"
            );
            certified += 1;
        }
    }
    assert_eq!(certified, 32, "the complete bit-method family must certify");
}

#[test]
fn six_controls_isolate_marker_name_arity_and_abi_gates() {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    let negative = [
        ("forgeries/forgery__F1_fake_ctlz_defpath.json", None, 1, false),
        ("forgeries/forgery__F2_nontotal_ctlz_nonzero.json", None, 1, false),
        ("forgeries/forgery__F3_wrong_arity_ctlz.json", Some(PureTotalIntrinsic::Ctlz), 2, false),
        ("forgeries/forgery__F4_foreign_ctlz.json", Some(PureTotalIntrinsic::Ctlz), 1, true),
        ("forgeries/forgery__F5_unmodeled_intrinsic_transmute.json", None, 1, false),
    ];
    for (rel, classifier, arity, foreign) in negative {
        let function = load(rel);
        let (callee, actual_arity, actual_foreign) = sole_call(&function);
        assert_eq!(PureTotalIntrinsic::classify(callee), classifier, "{rel}");
        assert_eq!(actual_arity, arity, "{rel}");
        assert_eq!(actual_foreign, foreign, "{rel}");
        assert!(function_fully_faithful_witness_with_callees(&function, &empty).is_none(), "{rel}");
        assert!(
            !trust_clean::diagnose_fully_faithful_gate(&function, &empty).fully_faithful,
            "{rel}"
        );
    }

    let rel = "forgeries/forgery__F6_valid_control_leading_zeros.json";
    let function = load(rel);
    let (callee, arity, foreign) = sole_call(&function);
    assert_eq!(PureTotalIntrinsic::classify(callee), Some(PureTotalIntrinsic::Ctlz));
    assert_eq!(arity, 1);
    assert!(!foreign);
    let witness = function_fully_faithful_witness_with_callees(&function, &empty);
    assert!(witness.as_ref().is_some_and(|certificate| certificate.is_modulo_3()), "{rel}");
}

#[test]
fn six_preop_controls_pin_the_public_acceptance_boundary() {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    for rel in [
        "forgeries/preop__G1_wrong_callee_evil.json",
        "forgeries/preop__G2_wrong_method_trailing_zeros.json",
        "forgeries/preop__G3_sideeffect_preop_binaryop.json",
        "forgeries/preop__G4_preop_unmodeled_value.json",
        "forgeries/preop__G5_multiwrite_preop_temp.json",
    ] {
        let function = load(rel);
        assert!(
            function_fully_faithful_witness_with_callees(&function, &empty).is_none(),
            "{rel}: W-PREOP forgery must decline"
        );
        assert!(
            !trust_clean::diagnose_fully_faithful_gate(&function, &empty).fully_faithful,
            "{rel}: W-PREOP forgery must fail the public gate"
        );
    }

    let rel = "forgeries/preop__G6_valid_control_count_zeros.json";
    let function = load(rel);
    let witness = function_fully_faithful_witness_with_callees(&function, &empty);
    assert!(
        witness.as_ref().is_some_and(|certificate| certificate.is_modulo_3()),
        "{rel}: genuine W-PREOP control must have a kernel witness"
    );
    assert!(trust_clean::diagnose_fully_faithful_gate(&function, &empty).fully_faithful);
}
