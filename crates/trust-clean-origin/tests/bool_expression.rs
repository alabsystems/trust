// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Composed Boolean Clean-origin bodies use the existing, independent E6
//! tree reader on the emitted body. These controls obtain the declaration
//! through real island elaboration and mutate the materializer's output.
//! Neither the expected gate result nor the mutated body comes from a second
//! renderer of the Clean expression.

use clean_kernel::Environment;
use trust_clean_origin::{
    BOOL_EXPRESSION_MAX_OPS, CleanOriginPlan, CleanOriginShape, TemplateOperand, TemplateRvalue,
    TemplateTerminator, TemplateTy, admit_lowering, body_template, plan_clean_origin_body,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

const CUSTODY: &str = "def release (reaped poll_ok exit_observed : Bool) : Bool := reaped || (poll_ok && exit_observed)";

fn island(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    assert!(!batch.is_rejected(), "the source island must kernel-check: {batch:?}");
    session.environment().expect("a checked island has an environment").clone()
}

fn operand(source: TemplateOperand) -> Operand {
    match source {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
        other => panic!("unexpected Boolean template operand: {other:?}"),
    }
}

/// Translate the actual materializer output without rebuilding the expression
/// from the plan. Each temporary and assignment stays in its emitted order.
fn emitted(env: &Environment, name: &str) -> (CleanOriginPlan, VerifiableFunction) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    assert!(matches!(plan.shape(), CleanOriginShape::BoolExpression { .. }));
    let row = trust_clean_origin::table::ladder_row(plan.shape())
        .expect("a composed Boolean plan must select a row");
    let template = body_template(row, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}` must materialize: {refusal:?}"));
    let locals = template
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| {
            assert!(
                matches!(
                    local.ty,
                    TemplateTy::Result | TemplateTy::Param { .. } | TemplateTy::Bool
                ),
                "every Boolean local must be typed as bool: {local:?}"
            );
            LocalDecl { index, ty: Ty::Bool, name: None }
        })
        .collect();
    let blocks = template
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| {
            assert!(matches!(block.terminator, TemplateTerminator::Return));
            let stmts = block
                .stmts
                .iter()
                .map(|statement| {
                    let rvalue = match statement.rvalue {
                        TemplateRvalue::Use(value) => Rvalue::Use(operand(value)),
                        TemplateRvalue::RawBin { op, left, right } => {
                            Rvalue::BinaryOp(op.mir_binop(), operand(left), operand(right))
                        }
                        TemplateRvalue::BoolNot(value) => {
                            Rvalue::UnaryOp(UnOp::Not, operand(value))
                        }
                        other => panic!("unexpected Boolean template rvalue: {other:?}"),
                    };
                    Statement::Assign {
                        place: Place::local(statement.place),
                        rvalue,
                        span: SourceSpan::default(),
                    }
                })
                .collect();
            BasicBlock { id: BlockId(index), stmts, terminator: Terminator::Return }
        })
        .collect();
    assert_eq!(template.blocks.len(), 1, "Boolean expressions emit a single pure block");
    let function = VerifiableFunction {
        name: name.to_owned(),
        def_path: format!("crate::decision::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: Ty::Bool,
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

fn assignments(function: &mut VerifiableFunction) -> impl Iterator<Item = &mut Rvalue> {
    function.body.blocks.iter_mut().flat_map(|block| {
        block.stmts.iter_mut().filter_map(|statement| match statement {
            Statement::Assign { rvalue, .. } => Some(rvalue),
            _ => None,
        })
    })
}

#[test]
fn real_composed_boolean_bodies_pass_the_kernel_gate() {
    for (name, source) in [
        ("release", CUSTODY),
        ("nested_not", "def nested_not (a b c : Bool) : Bool := not (a || (b && not c))"),
        ("literal", "def literal (a b : Bool) : Bool := a || (b && true)"),
        ("repeated", "def repeated (a b : Bool) : Bool := a || (b && not a)"),
    ] {
        let env = island(source);
        let (plan, function) = emitted(&env, name);
        admit_lowering(&env, &plan, &function).unwrap_or_else(|refusal| {
            panic!("`{source}` must admit its actual emission: {refusal:?}")
        });
    }
}

#[test]
fn changing_the_inner_connective_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    let mut changed = 0;
    for rvalue in assignments(&mut function) {
        if let Rvalue::BinaryOp(op @ BinOp::BitAnd, _, _) = rvalue {
            *op = BinOp::BitOr;
            changed += 1;
        }
    }
    assert_eq!(changed, 1, "the control must change the actual inner conjunction");
    admit_lowering(&env, &plan, &function)
        .expect_err("poll success alone must not substitute for observing exit");
}

#[test]
fn changing_the_inner_exit_operand_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    let mut changed = 0;
    for rvalue in assignments(&mut function) {
        if let Rvalue::BinaryOp(BinOp::BitAnd, _, right) = rvalue {
            *right = Operand::Copy(Place::local(2));
            changed += 1;
        }
    }
    assert_eq!(changed, 1, "the control must change the actual inner conjunction");
    admit_lowering(&env, &plan, &function)
        .expect_err("duplicating poll_ok must not erase exit_observed");
}

#[test]
fn changing_the_outer_connective_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    let mut changed = 0;
    for rvalue in assignments(&mut function) {
        if let Rvalue::BinaryOp(op @ BinOp::BitOr, _, _) = rvalue {
            *op = BinOp::BitAnd;
            changed += 1;
        }
    }
    assert_eq!(changed, 1, "the control must change the actual outer disjunction");
    admit_lowering(&env, &plan, &function)
        .expect_err("an already reaped child must not also require a successful poll");
}

#[test]
fn changing_an_emitted_boolean_literal_is_refused() {
    let source = "def literal (a b : Bool) : Bool := a || (b && true)";
    let env = island(source);
    let (plan, mut function) = emitted(&env, "literal");
    let mut changed = 0;
    for rvalue in assignments(&mut function) {
        if let Rvalue::BinaryOp(BinOp::BitAnd, _, Operand::Constant(ConstValue::Bool(value))) =
            rvalue
        {
            assert!(*value, "the source literal must be true");
            *value = false;
            changed += 1;
        }
    }
    assert_eq!(changed, 1, "the control must change an actual emitted literal");
    admit_lowering(&env, &plan, &function)
        .expect_err("changing a Boolean literal in the emitted body must fail the gate");
}

#[test]
fn a_non_boolean_temporary_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    let first_temporary = function.body.arg_count + 1;
    let local = function
        .body
        .locals
        .get_mut(first_temporary)
        .expect("a two-operation body must emit an intermediate temporary");
    local.ty = Ty::Int { width: 8, signed: false };
    admit_lowering(&env, &plan, &function)
        .expect_err("a Boolean operator with a non-Boolean local must be refused");
}

#[test]
fn the_source_operator_bound_is_enforced() {
    let source = |operators| {
        let body = (0..operators).fold("b".to_owned(), |right, _| format!("a && ({right})"));
        format!("def bounded (a b : Bool) : Bool := {body}")
    };

    // Exercise actual source elaboration and planning at both sides of the
    // limit. No hand-built plan can stand in for the recognizer's bound.
    let env = island(&source(BOOL_EXPRESSION_MAX_OPS));
    let plan = plan_clean_origin_body(&env, "bounded")
        .expect("the maximum operator count must still plan");
    assert!(matches!(plan.shape(), CleanOriginShape::BoolExpression { .. }));

    let env = island(&source(BOOL_EXPRESSION_MAX_OPS + 1));
    plan_clean_origin_body(&env, "bounded")
        .expect_err("a source expression above the operator count must be refused");
}

#[test]
fn a_different_return_carrier_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    function.body.return_ty = Ty::Int { width: 8, signed: false };
    function.body.locals[0].ty = function.body.return_ty.clone();
    admit_lowering(&env, &plan, &function)
        .expect_err("an emitted integer result must not replace the Boolean carrier");
}

#[test]
fn a_different_parameter_count_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    function.body.arg_count -= 1;
    admit_lowering(&env, &plan, &function)
        .expect_err("the actual emitted arity must match the admitted signature");
}

#[test]
fn a_different_parameter_carrier_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    function.body.locals[1].ty = Ty::Int { width: 8, signed: false };
    admit_lowering(&env, &plan, &function)
        .expect_err("an integer parameter cannot stand in for the original Boolean input");
}

#[test]
fn association_uses_the_existing_checked_induction_gate() {
    let env = island("def left_nested (a b c : Bool) : Bool := (a && b) && c");
    let (plan, function) = emitted(&env, "left_nested");
    let faithful = admit_lowering(&env, &plan, &function)
        .expect("the existing gate can prove the original associativity equation by induction");
    assert_eq!(faithful.name(), "left_nested");
    assert_eq!(
        faithful.method(),
        trust_clean_origin::FaithfulnessMethod::StructuralInduction,
        "the original declaration must earn the existing kernel-checked proof route"
    );

    let mut wrong = function;
    let outer = assignments(&mut wrong)
        .filter(|rvalue| matches!(rvalue, Rvalue::BinaryOp(BinOp::BitAnd, _, _)))
        .last()
        .expect("the actual emission must contain its outer conjunction");
    let Rvalue::BinaryOp(op, _, _) = outer else { unreachable!() };
    *op = BinOp::BitOr;
    admit_lowering(&env, &plan, &wrong)
        .expect_err("checked induction must reject (a && b) || c for the original function");
}

#[test]
fn a_temporary_used_before_its_definition_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    let statements = &mut function.body.blocks[0].stmts;
    assert!(statements.len() >= 3, "two operations and the return assignment must be present");
    statements.swap(0, 1);
    admit_lowering(&env, &plan, &function)
        .expect_err("the outer operation cannot read the inner temporary before its definition");
}

#[test]
fn writing_to_a_parameter_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    function.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
            span: SourceSpan::default(),
        },
    );
    admit_lowering(&env, &plan, &function)
        .expect_err("a parameter write must not be interpreted as its original entry value");
}

#[test]
fn an_extra_effect_is_refused() {
    let env = island(CUSTODY);
    let (plan, mut function) = emitted(&env, "release");
    function.body.blocks[0].stmts.insert(0, Statement::Deinit { place: Place::local(1) });
    admit_lowering(&env, &plan, &function)
        .expect_err("a correct returned expression cannot hide an additional effect");
}

#[test]
fn unlisted_boolean_operators_are_refused() {
    let env = island(CUSTODY);
    let (plan, function) = emitted(&env, "release");
    for forbidden in [BinOp::BitXor, BinOp::Eq] {
        let mut mutant = function.clone();
        let mut changed = 0;
        for rvalue in assignments(&mut mutant) {
            if let Rvalue::BinaryOp(op @ BinOp::BitAnd, _, _) = rvalue {
                *op = forbidden;
                changed += 1;
            }
        }
        assert_eq!(changed, 1, "the control must change the actual inner conjunction");
        admit_lowering(&env, &plan, &mutant)
            .expect_err("XOR and comparisons are outside the Boolean-expression vocabulary");
    }
}

#[test]
fn a_different_control_flow_grammar_is_refused() {
    let env = island(CUSTODY);
    let (plan, function) = emitted(&env, "release");

    let mut loop_body = function.clone();
    loop_body.body.blocks[0].terminator = Terminator::Goto(BlockId(0));
    admit_lowering(&env, &plan, &loop_body)
        .expect_err("a loop must not enter the bounded straight-line expression slice");

    let mut extra_block = function;
    extra_block.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: Vec::new(),
        terminator: Terminator::Return,
    });
    admit_lowering(&env, &plan, &extra_block)
        .expect_err("even an unreachable extra block is outside this emission vocabulary");
}
