// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Original source elaboration, actual template emission and independent
//! emitted-body reflection. Mutations never alter the source declaration.

use clean_kernel::Environment;
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, TemplateOperand, TemplateRvalue, TemplateTerminator,
    TemplateTy, admit_lowering, body_template, plan_clean_origin_body,
};
use trust_types::admissible_body::SelectCmp;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn island(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let result = session.check_all(&[source]);
    assert!(!result.is_rejected(), "original island must kernel-check: {result:?}");
    session.environment().unwrap().clone()
}

fn operand(value: TemplateOperand) -> Operand {
    match value {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        TemplateOperand::ResultScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        other => panic!("unexpected conditional operand: {other:?}"),
    }
}

fn emitted(env: &Environment, name: &str) -> (CleanOriginPlan, VerifiableFunction) {
    let plan = plan_clean_origin_body(env, name).unwrap();
    assert!(matches!(plan.shape(), CleanOriginShape::UnsignedConditional { .. }));
    let row = trust_clean_origin::table::ladder_row(plan.shape()).unwrap();
    let template = body_template(row, &plan).unwrap();
    let ty = plan.signature().result().rust().clone();
    let locals = template
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| LocalDecl {
            index,
            name: None,
            ty: match local.ty {
                TemplateTy::Result | TemplateTy::Param { .. } => ty.clone(),
                TemplateTy::Bool => Ty::Bool,
                other => panic!("unexpected conditional local: {other:?}"),
            },
        })
        .collect();
    let blocks = template
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| BasicBlock {
            id: BlockId(index),
            stmts: block
                .stmts
                .iter()
                .map(|statement| Statement::Assign {
                    place: Place::local(statement.place),
                    span: SourceSpan::default(),
                    rvalue: match statement.rvalue {
                        TemplateRvalue::Use(value) => Rvalue::Use(operand(value)),
                        TemplateRvalue::Compare { cmp, left, right } => Rvalue::BinaryOp(
                            match cmp {
                                SelectCmp::Lt => BinOp::Lt,
                                SelectCmp::Le => BinOp::Le,
                                SelectCmp::Eq => BinOp::Eq,
                            },
                            operand(left),
                            operand(right),
                        ),
                        other => panic!("unexpected conditional instruction: {other:?}"),
                    },
                })
                .collect(),
            terminator: match block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                TemplateTerminator::Goto(target) => Terminator::Goto(BlockId(target)),
                TemplateTerminator::SwitchIntZero { discr, zero, otherwise } => {
                    Terminator::SwitchInt {
                        discr: operand(discr),
                        targets: vec![(0, BlockId(zero))],
                        otherwise: BlockId(otherwise),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    }
                }
                _ => panic!("a pure conditional cannot call"),
            },
        })
        .collect();
    let function = VerifiableFunction {
        name: name.into(),
        def_path: format!("conditional::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    (plan, function)
}

#[test]
fn original_classifier_shapes_and_forked_trees_pass_the_independent_gate() {
    for width in [8, 16, 32, 64] {
        let source = format!(
            "\
def gpr (reg : UInt{width}) : UInt{width} := if reg < 19 then 0 else if reg < 30 then 1 else 0\n\
def fpr (reg : UInt{width}) : UInt{width} := if reg < 8 then 0 else if reg < 16 then 1 else 0\n\
def fork (a b : UInt{width}) : UInt{width} := if a < b then (if a < 3 then a else b) else (if b < 7 then 9 else a)\n\
def ordered (a b : UInt{width}) : UInt{width} := if a <= b then (if a = b then b else a) else b\n\
def equal_root (a b : UInt{width}) : UInt{width} := if a = b then (if a <= b then 1 else 0) else a\n\
def literal_relations (a : UInt{width}) : UInt{width} := if a <= 10 then (if a = 7 then 1 else 2) else 3\n"
        );
        let env = island(&source);
        for name in ["gpr", "fpr", "fork", "ordered", "equal_root", "literal_relations"] {
            let (plan, function) = emitted(&env, name);
            admit_lowering(&env, &plan, &function)
                .unwrap_or_else(|failure| panic!("{width}/{name}: {failure:?}"));
        }
    }
}

#[test]
fn each_nested_comparison_boundary_and_polarity_is_bound_to_original_source() {
    let env = island(
        "def classify (reg : UInt8) : UInt8 := if reg < 19 then 0 else if reg < 30 then 1 else 0",
    );
    let (plan, function) = emitted(&env, "classify");
    admit_lowering(&env, &plan, &function).unwrap();
    for (block, expected) in [(0, 19), (2, 30)] {
        let mut changed = function.clone();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, right), .. } =
            &mut changed.body.blocks[block].stmts[0]
        else {
            panic!("expected actual comparison")
        };
        assert!(
            matches!(&*right, Operand::Constant(ConstValue::Uint(value, 8)) if *value == expected)
        );
        *right = Operand::Constant(ConstValue::Uint(expected - 1, 8));
        admit_lowering(&env, &plan, &changed).expect_err("changed threshold must refuse");
        let mut changed = function.clone();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), .. } =
            &mut changed.body.blocks[block].stmts[0]
        else {
            unreachable!()
        };
        *op = BinOp::Le;
        admit_lowering(&env, &plan, &changed).expect_err("changed strictness must refuse");
        let mut changed = function.clone();
        let Terminator::SwitchInt { targets, otherwise, .. } =
            &mut changed.body.blocks[block].terminator
        else {
            unreachable!()
        };
        std::mem::swap(&mut targets[0].1, otherwise);
        admit_lowering(&env, &plan, &changed).expect_err("changed branch polarity must refuse");
    }

    let literal_env = island(
        "def literal_relations (a : UInt8) : UInt8 := \
         if a <= 10 then (if a = 7 then 1 else 2) else 3",
    );
    let (literal_plan, literal_function) = emitted(&literal_env, "literal_relations");
    admit_lowering(&literal_env, &literal_plan, &literal_function).unwrap();
    let comparisons: Vec<_> = literal_function
        .body
        .blocks
        .iter()
        .enumerate()
        .filter_map(|(block, bb)| {
            bb.stmts.iter().find_map(|statement| match statement {
                Statement::Assign {
                    rvalue: Rvalue::BinaryOp(op, _, Operand::Constant(ConstValue::Uint(value, 8))),
                    ..
                } => Some((block, *op, *value)),
                _ => None,
            })
        })
        .collect();
    assert_eq!(comparisons, [(0, BinOp::Le, 10), (1, BinOp::Eq, 7)]);
    for (block, original_op, value) in comparisons {
        let mut changed = literal_function.clone();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, right), .. } =
            &mut changed.body.blocks[block].stmts[0]
        else {
            unreachable!()
        };
        *right = Operand::Constant(ConstValue::Uint(value + 1, 8));
        admit_lowering(&literal_env, &literal_plan, &changed)
            .expect_err("changed literal threshold must refuse");

        let mut changed = literal_function.clone();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), .. } =
            &mut changed.body.blocks[block].stmts[0]
        else {
            unreachable!()
        };
        *op = if original_op == BinOp::Le { BinOp::Lt } else { BinOp::Le };
        admit_lowering(&literal_env, &literal_plan, &changed)
            .expect_err("changed literal comparison must refuse");

        for wrong in [ConstValue::Uint(value, 16), ConstValue::Uint(256, 8)] {
            let mut changed = literal_function.clone();
            let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, right), .. } =
                &mut changed.body.blocks[block].stmts[0]
            else {
                unreachable!()
            };
            *right = Operand::Constant(wrong);
            admit_lowering(&literal_env, &literal_plan, &changed)
                .expect_err("literal comparison must retain its carrier and range");
        }

        let mut changed = literal_function.clone();
        let Terminator::SwitchInt { targets, otherwise, .. } =
            &mut changed.body.blocks[block].terminator
        else {
            unreachable!()
        };
        std::mem::swap(&mut targets[0].1, otherwise);
        admit_lowering(&literal_env, &literal_plan, &changed)
            .expect_err("changed literal branch polarity must refuse");
    }
}

#[test]
fn literal_leaves_signature_changes_and_effects_fail_closed() {
    let env = island(
        "def classify (a b : UInt8) : UInt8 := if a < b then 0 else if b < 30 then 1 else a",
    );
    let (plan, function) = emitted(&env, "classify");
    admit_lowering(&env, &plan, &function).unwrap();
    let mut changed = function.clone();
    let Statement::Assign { rvalue, .. } = &mut changed.body.blocks[3].stmts[0] else {
        unreachable!()
    };
    *rvalue = Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 8)));
    admit_lowering(&env, &plan, &changed).expect_err("wrong literal arm must refuse");
    for value in [ConstValue::Uint(1, 64), ConstValue::Uint(256, 8)] {
        let mut changed = function.clone();
        let Statement::Assign { rvalue, .. } = &mut changed.body.blocks[3].stmts[0] else {
            unreachable!()
        };
        *rvalue = Rvalue::Use(Operand::Constant(value));
        admit_lowering(&env, &plan, &changed)
            .expect_err("literal encoding must retain its carrier and range");
    }
    let mut changed = function.clone();
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, left, _), .. } =
        &mut changed.body.blocks[0].stmts[0]
    else {
        unreachable!()
    };
    *left = Operand::Copy(Place::local(2));
    admit_lowering(&env, &plan, &changed).expect_err("wrong source parameter must refuse");
    let mut changed = function.clone();
    changed.body.arg_count += 1;
    admit_lowering(&env, &plan, &changed).expect_err("extra ignored formal must refuse");
    let mut changed = function.clone();
    changed.body.locals[1].ty = Ty::u64();
    admit_lowering(&env, &plan, &changed).expect_err("wrong argument carrier must refuse");
    let mut changed = function.clone();
    changed.body.blocks.push(BasicBlock {
        id: BlockId(5),
        stmts: Vec::new(),
        terminator: Terminator::Unreachable,
    });
    admit_lowering(&env, &plan, &changed).expect_err("unowned unreachable emission must refuse");
    let mut changed = function.clone();
    changed.body.blocks[0].stmts.push(Statement::Intrinsic {
        name: "externally_effectful_intrinsic".into(),
        args: Vec::new(),
    });
    admit_lowering(&env, &plan, &changed)
        .expect_err("a reached intrinsic cannot disappear from the reflection");
    let mut changed = function.clone();
    changed.body.blocks.push(BasicBlock {
        id: BlockId(5),
        stmts: vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 8)),
            ),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    });
    admit_lowering(&env, &plan, &changed)
        .expect_err("unreachable unplanned arithmetic must refuse before reflection");
    let mut changed = function.clone();
    changed.body.blocks[0].terminator = Terminator::Goto(BlockId(0));
    admit_lowering(&env, &plan, &changed)
        .expect_err("a looping body cannot denote a total conditional tree");
}

#[test]
fn single_selects_keep_the_existing_plan_and_mixed_signatures_refuse() {
    let env = island(
        "def single (a : UInt8) : UInt8 := if a < 19 then 0 else 1\n\
         def literal_lt (a b : UInt8) : UInt8 := if a < 19 then a else b\n\
         def literal_le (a b : UInt8) : UInt8 := if a <= 19 then a else b\n\
         def literal_eq (a b : UInt8) : UInt8 := if a = 19 then a else b\n\
         def range_le (a b : UInt8) : UInt8 := if a <= 256 then a else b\n\
         def range_eq (a b : UInt8) : UInt8 := if a = 256 then a else b\n\
         def mixed (a : UInt8) (unused : UInt16) : UInt8 := if a < 19 then 0 else if a < 30 then 1 else 0",
    );
    assert!(matches!(
        plan_clean_origin_body(&env, "single").unwrap().shape(),
        CleanOriginShape::SelectOperands { .. }
    ));
    for (name, expected_cmp) in [
        ("literal_lt", SelectCmp::Lt),
        ("literal_le", SelectCmp::Le),
        ("literal_eq", SelectCmp::Eq),
    ] {
        assert!(matches!(
            plan_clean_origin_body(&env, name).unwrap().shape(),
            CleanOriginShape::SelectLiteral { cmp, literal: 19, .. } if *cmp == expected_cmp
        ));
    }
    for name in ["range_le", "range_eq"] {
        assert!(plan_clean_origin_body(&env, name).is_err());
    }
    assert!(plan_clean_origin_body(&env, "mixed").is_err());
}

#[test]
fn whole_tree_budget_is_not_just_a_depth_limit() {
    fn balanced(depth: usize) -> String {
        if depth == 0 {
            "a".into()
        } else {
            let child = balanced(depth - 1);
            format!("if a < 3 then ({child}) else ({child})")
        }
    }
    let source = format!(
        "def within (a : UInt8) : UInt8 := {}\ndef beyond (a : UInt8) : UInt8 := {}",
        balanced(5),
        balanced(6)
    );
    let env = island(&source);
    assert!(matches!(
        plan_clean_origin_body(&env, "within").unwrap().shape(),
        CleanOriginShape::UnsignedConditional { .. }
    ));
    assert!(plan_clean_origin_body(&env, "beyond").is_err());
}

#[test]
fn exact_source_decision_budget_accepts_32_and_refuses_33() {
    fn chain(count: usize) -> String {
        (0..count).fold("a".to_owned(), |inner, _| format!("if a < 3 then a else ({inner})"))
    }
    let source = format!(
        "def within (a : UInt8) : UInt8 := {}\ndef beyond (a : UInt8) : UInt8 := {}",
        chain(32),
        chain(33)
    );
    let env = island(&source);
    assert!(matches!(
        plan_clean_origin_body(&env, "within").unwrap().shape(),
        CleanOriginShape::UnsignedConditional { .. }
    ));
    assert!(plan_clean_origin_body(&env, "beyond").is_err());
}
