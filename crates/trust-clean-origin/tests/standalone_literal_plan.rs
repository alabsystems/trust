// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use trust_certify::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
use trust_clean_origin::emit::plan_standalone_clean_origin_body;
use trust_clean_origin::{CleanOriginShape, plan_clean_origin_body};

fn checked(source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Literals".into(),
            path: "Literals.lean".into(),
            source: source.into(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "{:?}", batch.errors());
    batch
}

#[test]
fn mixed_literal_plans_preserve_complete_telescope_and_never_become_mir_plans() {
    let mut source = String::new();
    for width in [8, 16, 32, 64] {
        let maximum = (1_u128 << width) - 1;
        source.push_str(&format!(
            "def lit{width} (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt{width} := {maximum}\n\
             def reversed{width} (a : UInt64) (b : UInt8) : UInt{width} := 0\n"
        ));
    }
    let batch = checked(&source);
    let context = batch.accepted_context().unwrap();
    assert_eq!(context.owned_declarations().len(), 8);
    for width in [8, 16, 32, 64] {
        for (prefix, expected, params) in [
            ("lit", (1_u128 << width) - 1, vec!["UInt8", "UInt16", "UInt32", "UInt64"]),
            ("reversed", 0, vec!["UInt64", "UInt8"]),
        ] {
            let name = format!("{prefix}{width}");
            let plan = plan_standalone_clean_origin_body(context.environment(), &name).unwrap();
            assert_eq!(plan.shape(), &CleanOriginShape::ConstantUint { value: expected });
            assert_eq!(
                plan.signature().arguments().iter().map(|c| c.clean().name()).collect::<Vec<_>>(),
                params
            );
            assert_eq!(plan.signature().result().clean().name(), format!("UInt{width}"));
            assert!(plan.legacy_plan().is_none(), "standalone must not mint a legacy plan");
            assert!(
                plan_clean_origin_body(context.environment(), &name).is_err(),
                "legacy MIR reflection remains single-domain"
            );
        }
    }
}

#[test]
fn nullary_and_uniform_literal_shapes_match_existing_plans() {
    let batch = checked(
        "def literalZero : UInt8 := 0\ndef literalMax (a b : UInt64) : UInt64 := 18446744073709551615",
    );
    let context = batch.accepted_context().unwrap();
    for name in ["literalZero", "literalMax"] {
        let standalone = plan_standalone_clean_origin_body(context.environment(), name).unwrap();
        let legacy = plan_clean_origin_body(context.environment(), name).unwrap();
        assert_eq!(standalone.name(), legacy.name());
        assert_eq!(standalone.shape(), legacy.shape());
        assert_eq!(standalone.signature(), legacy.signature());
        assert!(standalone.legacy_plan().is_none());
    }
}

#[test]
fn unsupported_carriers_hypotheses_and_numerals_are_not_erased() {
    for source in [
        "def bad (n : Bool) : UInt8 := 7",
        // The existing elaborated-explicit-ofNat reader boundary stays visible.
        "def bad (a : UInt16) : UInt8 := UInt8.ofNat 0",
        "def bad (a : UInt16) (h : a = a) : UInt8 := 7",
    ] {
        let batch = checked(source);
        let context = batch.accepted_context().unwrap();
        assert!(
            plan_standalone_clean_origin_body(context.environment(), "bad").is_err(),
            "{source}"
        );
    }
}

#[test]
fn nonliteral_bodies_still_use_the_exact_legacy_plan() {
    let batch = checked(
        "def choose (a : UInt8) (b : UInt64) : UInt64 := b\ndef add8 (a b : UInt8) : UInt8 := a + b\ndef composed8 (a b : UInt8) : UInt8 := (a + b) + a",
    );
    let context = batch.accepted_context().unwrap();
    for name in ["choose", "add8", "composed8"] {
        let standalone = plan_standalone_clean_origin_body(context.environment(), name).unwrap();
        let legacy = plan_clean_origin_body(context.environment(), name).unwrap();
        assert_eq!(standalone.legacy_plan().unwrap().shape(), legacy.shape());
        assert_eq!(standalone.signature(), legacy.signature());
    }
}

/// Trust (WS5.20, `STANDALONE.p18_literal_out_of_range`): an out-of-range
/// surface numeral plans its Lean residue (`OfNat` at `UInt{w}` is mod `2^w`:
/// `(300 : UInt8)` IS 44) on the STANDALONE lane only — the standalone gate
/// then kernel-checks the emitted residue against the untouched source numeral
/// (`trust-clean-ir-gate` `standalone_literal_residue`). The MIR lane's planner
/// still refuses it (`control_9` `half_8`), because it has no such check.
#[test]
fn out_of_range_numerals_plan_their_lean_residue_on_the_standalone_lane_only() {
    let batch = checked(
        "def lit300 : UInt8 := 300\n\
         def bad (a : UInt16) : UInt8 := 256\n\
         def wide : UInt16 := 65537\n",
    );
    let context = batch.accepted_context().unwrap();
    for (name, residue) in [("lit300", 44), ("bad", 0), ("wide", 1)] {
        let plan = plan_standalone_clean_origin_body(context.environment(), name)
            .unwrap_or_else(|refusal| panic!("{name}: {refusal:?}"));
        assert_eq!(plan.shape(), &CleanOriginShape::ConstantUint { value: residue }, "{name}");
        assert!(plan.legacy_plan().is_none());
        assert!(
            plan_clean_origin_body(context.environment(), name).is_err(),
            "{name}: the MIR lane never reduces a numeral"
        );
    }
}
