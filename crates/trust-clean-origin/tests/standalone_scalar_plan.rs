// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trust (WS5.20, F-096): the standalone lane's SCALAR vocabulary
//! (`plan_standalone_scalar_body_for_name`) — a connective of two comparisons
//! (`STANDALONE.p20`), a `&&&`/`|||` tree (`p15`) and total division (`p13`).
//! It is consulted only after the shared planner declines, never plans a shape
//! the shared planner owns, and the MIR lane's planner still refuses all three.

use clean_kernel::Name;
use trust_certify::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
use trust_clean_origin::emit::{
    StandaloneBitwiseExpr, StandaloneBitwiseOp, StandaloneComparison, StandaloneScalarShape,
    plan_standalone_clean_origin_body, plan_standalone_scalar_body_for_name,
};
use trust_clean_origin::plan_clean_origin_body;
use trust_types::admissible_body::{ArithOperand, BoolBinOp, SelectCmp};

fn checked(source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Scalars".into(),
            path: "Scalars.lean".into(),
            source: source.into(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "{:?}", batch.errors());
    batch
}

#[test]
fn the_three_part_a_probes_plan_their_standalone_scalar_shapes() {
    let batch = checked(
        "def both (a b c : UInt64) : Bool := a < b && b < c\n\
         def mask (a b : UInt64) : UInt64 := (a &&& b) ||| 1\n\
         def quot (a b : UInt64) : UInt64 := a / b\n",
    );
    let context = batch.accepted_context().unwrap();
    let env = context.environment();
    for name in ["both", "mask", "quot"] {
        assert!(plan_standalone_clean_origin_body(env, name).is_err(), "{name}: shared planner");
        assert!(plan_clean_origin_body(env, name).is_err(), "{name}: the MIR lane never plans it");
    }
    let plan = |name: &str| {
        plan_standalone_scalar_body_for_name(env, &Name::from_string(name))
            .unwrap_or_else(|refusal| panic!("{name}: {refusal:?}"))
            .shape()
            .clone()
    };
    assert_eq!(
        plan("both"),
        StandaloneScalarShape::ComparisonConnective {
            op: BoolBinOp::And,
            left: StandaloneComparison { cmp: SelectCmp::Lt, left: 0, right: 1 },
            right: StandaloneComparison { cmp: SelectCmp::Lt, left: 1, right: 2 },
        }
    );
    assert_eq!(
        plan("mask"),
        StandaloneScalarShape::Bitwise {
            expr: StandaloneBitwiseExpr::Bin {
                op: StandaloneBitwiseOp::Or,
                left: Box::new(StandaloneBitwiseExpr::Bin {
                    op: StandaloneBitwiseOp::And,
                    left: Box::new(StandaloneBitwiseExpr::Operand(ArithOperand::Param(0))),
                    right: Box::new(StandaloneBitwiseExpr::Operand(ArithOperand::Param(1))),
                }),
                right: Box::new(StandaloneBitwiseExpr::Operand(ArithOperand::Const(1))),
            },
        }
    );
    assert_eq!(plan("quot"), StandaloneScalarShape::TotalDivision { dividend: 0, divisor: 1 });
}

#[test]
fn the_scalar_vocabulary_never_takes_a_shared_shape_or_a_mixed_carrier() {
    let batch = checked(
        "def oneAnd (a b : UInt64) : UInt64 := a &&& b\n\
         def byThree (a : UInt64) : UInt64 := a / 3\n\
         def mixed (a : UInt8) (b : UInt64) : Bool := a < 3 && b < 4\n\
         def rem (a b : UInt64) : UInt64 := a % b\n\
         def either (a b : UInt32) : Bool := a == b || b <= a\n",
    );
    let context = batch.accepted_context().unwrap();
    let env = context.environment();
    let scalar = |name: &str| plan_standalone_scalar_body_for_name(env, &Name::from_string(name));
    // A single raw operator is the shared RawBinOp shape: never planned twice.
    assert!(plan_standalone_clean_origin_body(env, "oneAnd").is_ok());
    assert!(scalar("oneAnd").is_err());
    // A positive numeral divisor is the shared shape's; the scalar reader only
    // takes a VARIABLE divisor.
    assert!(scalar("byThree").is_err());
    // Mixed carriers, literal comparison operands and `%` stay outside.
    assert!(scalar("mixed").is_err());
    assert!(scalar("rem").is_err());
    // `||` and `==`/`<=` leaves are in the vocabulary.
    assert_eq!(
        scalar("either").unwrap().shape(),
        &StandaloneScalarShape::ComparisonConnective {
            op: BoolBinOp::Or,
            left: StandaloneComparison { cmp: SelectCmp::Eq, left: 0, right: 1 },
            right: StandaloneComparison { cmp: SelectCmp::Le, left: 1, right: 0 },
        }
    );
}

/// NEGATIVE TWIN (the `p16_tree_33_nodes` bound): a 33-operator `&&&`/`|||`
/// tree is outside the scalar vocabulary's budget, exactly as a 33-operator
/// wrapping tree is outside the shared planner's; 32 operators plan.
#[test]
fn a_bitwise_tree_past_the_operator_budget_stays_refused() {
    let chain = |ops: usize| {
        let mut body = "a".to_owned();
        for i in 0..ops {
            body = format!("({body} {} b)", if i % 2 == 0 { "&&&" } else { "|||" });
        }
        body
    };
    let batch = checked(&format!(
        "def within (a b : UInt64) : UInt64 := {}\ndef beyond (a b : UInt64) : UInt64 := {}\n",
        chain(32),
        chain(33)
    ));
    let context = batch.accepted_context().unwrap();
    let env = context.environment();
    assert!(plan_standalone_scalar_body_for_name(env, &Name::from_string("within")).is_ok());
    assert!(plan_standalone_scalar_body_for_name(env, &Name::from_string("beyond")).is_err());
}
