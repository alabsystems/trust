// trust-integration-tests/tests/contract_e2e.rs: Contract & trust_wp VC error detection tests
//
// Tests that Trust's verification pipeline correctly generates and verifies
// contract-based VCs across 8 VcKind variants:
// 1. Precondition — caller violates function precondition
// 2. Postcondition — function violates its postcondition
// 3. LoopInvariantInitiation — invariant fails at loop entry
// 4. LoopInvariantConsecution — invariant not preserved by iteration
// 5. LoopInvariantSufficiency — invariant too weak for postcondition
// 6. TypeRefinementViolation — value outside refined type constraint
// 7. FrameConditionViolation — writing to variable not in modifies set
// 8. FunctionalCorrectness — function produces incorrect result
//
// Each category: buggy version (ay finds counterexample) + safe version (ay proves correct).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_integration_tests::ay_test_support::require_ay;
use trust_router::VerificationBackend;
use trust_types::*;

/// Build a VerifiableFunction with given contracts and locals.
fn make_contract_function(
    name: &str,
    contracts: Vec<Contract>,
    locals: Vec<LocalDecl>,
    arg_count: usize,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty: Ty::usize(),
        },
        contracts,
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Build a VerificationCondition directly for ay formula tests.
fn make_vc(kind: VcKind, function: &str, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

/// Standard single-arg function locals: [_0 (return), x (arg)].
fn single_arg_locals() -> Vec<LocalDecl> {
    vec![
        LocalDecl { index: 0, ty: Ty::usize(), name: None },
        LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
    ]
}

/// Two-arg function locals: [_0 (return), x (arg), result (local)].
fn two_named_locals() -> Vec<LocalDecl> {
    vec![
        LocalDecl { index: 0, ty: Ty::usize(), name: None },
        LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("result".into()) },
    ]
}

// ===========================================================================
// Section A: Pipeline tests — verify generate_vcs() produces correct VcKinds
// ===========================================================================

#[test]
fn test_pipeline_precondition_vc() {
    let func = make_contract_function(
        "precond_fn",
        vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }],
        single_arg_locals(),
        1,
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    let precond_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::Precondition { .. })).collect();

    assert!(
        !precond_vcs.is_empty(),
        "generate_vcs must produce Precondition VC for Requires contract"
    );
    if let VcKind::Precondition { callee } = &precond_vcs[0].kind {
        assert_eq!(callee, "precond_fn");
    }
}

#[test]
fn test_pipeline_postcondition_vc() {
    let func = make_contract_function(
        "postcond_fn",
        vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= 0".to_string(),
        }],
        single_arg_locals(),
        1,
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    let postcond_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();

    assert!(
        !postcond_vcs.is_empty(),
        "generate_vcs must produce Postcondition VC for Ensures contract"
    );
}

#[test]
fn test_pipeline_loop_invariant_generates_three_vcs() {
    let func = make_contract_function(
        "loop_inv_fn",
        vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "bb0: sum >= 0".to_string(),
        }],
        single_arg_locals(),
        1,
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    let init_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::LoopInvariantInitiation { .. }))
        .collect();
    let consec_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .collect();
    let suff_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::LoopInvariantSufficiency { .. }))
        .collect();

    assert_eq!(
        init_vcs.len(),
        1,
        "LoopInvariant contract must produce exactly 1 LoopInvariantInitiation VC"
    );
    assert_eq!(
        consec_vcs.len(),
        1,
        "LoopInvariant contract must produce exactly 1 LoopInvariantConsecution VC"
    );
    assert_eq!(
        suff_vcs.len(),
        1,
        "LoopInvariant contract must produce exactly 1 LoopInvariantSufficiency VC"
    );

    // Check that the invariant string and header_block are preserved.
    if let VcKind::LoopInvariantInitiation { invariant, header_block } = &init_vcs[0].kind {
        assert_eq!(invariant, "sum >= 0");
        assert_eq!(*header_block, 0);
    }
}

#[test]
fn test_pipeline_type_refinement_vc() {
    let func = make_contract_function(
        "refine_fn",
        vec![Contract {
            kind: ContractKind::TypeRefinement,
            span: SourceSpan::default(),
            body: "x: x > 0".to_string(),
        }],
        single_arg_locals(),
        1,
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    let refine_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::TypeRefinementViolation { .. }))
        .collect();

    assert!(
        !refine_vcs.is_empty(),
        "generate_vcs must produce TypeRefinementViolation VC for TypeRefinement contract"
    );

    if let VcKind::TypeRefinementViolation { variable, predicate } = &refine_vcs[0].kind {
        assert_eq!(variable, "x");
        assert_eq!(predicate, "x > 0");
    }
}

#[test]
fn test_pipeline_frame_condition_vc() {
    let func = make_contract_function(
        "frame_fn",
        vec![Contract {
            kind: ContractKind::Modifies,
            span: SourceSpan::default(),
            body: "result".to_string(),
        }],
        two_named_locals(),
        1,
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    let frame_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::FrameConditionViolation { .. }))
        .collect();

    assert!(
        !frame_vcs.is_empty(),
        "generate_vcs must produce FrameConditionViolation VC for variable not in modifies set"
    );

    // The VC should be for 'x' (not in modifies set), not 'result' (in modifies set).
    let has_x_frame = frame_vcs
        .iter()
        .any(|vc| matches!(&vc.kind, VcKind::FrameConditionViolation { variable, .. } if variable == "x"));

    assert!(has_x_frame, "FrameConditionViolation must be generated for 'x' (not in modifies set)");

    // 'result' should NOT have a frame VC since it's in the modifies set.
    let has_result_frame = frame_vcs
        .iter()
        .any(|vc| matches!(&vc.kind, VcKind::FrameConditionViolation { variable, .. } if variable == "result"));

    assert!(
        !has_result_frame,
        "FrameConditionViolation must NOT be generated for 'result' (in modifies set)"
    );
}

// ===========================================================================
// Section B: AY formula tests — buggy (SAT) and safe (UNSAT) for each VcKind
// ===========================================================================

// --- B1: Precondition ---

#[test]
fn test_precondition_buggy() {
    let ay = require_ay();
    // Precondition: x > 0. Negated check: NOT(x > 0) with unconstrained x.
    // SAT — ay finds x = 0 (or negative) as counterexample.
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::Not(Box::new(Formula::Gt(Box::new(x), Box::new(Formula::Int(0)))));

    let vc = make_vc(
        VcKind::Precondition { callee: "buggy_precond".to_string() },
        "buggy_precond",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("precondition buggy: {:?}", result);
    assert!(result.is_failed(), "ay must find precondition violation. Got: {result:?}");
}

#[test]
fn test_precondition_safe() {
    let ay = require_ay();
    // Under precondition x > 0, check x > 0 holds (tautology).
    // Negated: x > 0 AND NOT(x > 0) — UNSAT.
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0))),
        Formula::Not(Box::new(Formula::Gt(Box::new(x), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(
        VcKind::Precondition { callee: "safe_precond".to_string() },
        "safe_precond",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("precondition safe: {:?}", result);
    assert!(result.is_proved(), "ay must prove precondition holds. Got: {result:?}");
}

// --- B2: Postcondition ---

#[test]
fn test_postcondition_buggy() {
    let ay = require_ay();
    // Postcondition: result >= 0. Negated check: NOT(result >= 0) with unconstrained result.
    // SAT — ay finds result = -1.
    let result_var = Formula::Var("result".into(), Sort::Int);
    let formula =
        Formula::Not(Box::new(Formula::Ge(Box::new(result_var), Box::new(Formula::Int(0)))));

    let vc = make_vc(VcKind::Postcondition, "buggy_postcond", formula);

    let result = ay.verify(&vc);
    eprintln!("postcondition buggy: {:?}", result);
    assert!(result.is_failed(), "ay must find postcondition violation. Got: {result:?}");
}

#[test]
fn test_postcondition_safe() {
    let ay = require_ay();
    // result = x + 1 with x >= 0 => result >= 1 >= 0.
    // Negated: x >= 0 AND result == x + 1 AND NOT(result >= 0) — UNSAT.
    let x = Formula::Var("x".into(), Sort::Int);
    let result_var = Formula::Var("result".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0))),
        Formula::Eq(
            Box::new(result_var.clone()),
            Box::new(Formula::Add(Box::new(x), Box::new(Formula::Int(1)))),
        ),
        Formula::Not(Box::new(Formula::Ge(Box::new(result_var), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(VcKind::Postcondition, "safe_postcond", formula);

    let result = ay.verify(&vc);
    eprintln!("postcondition safe: {:?}", result);
    assert!(result.is_proved(), "ay must prove postcondition holds. Got: {result:?}");
}

// --- B3: LoopInvariantInitiation ---

#[test]
fn test_loop_invariant_initiation_buggy() {
    let ay = require_ay();
    // Invariant: sum >= 0. At entry sum starts unconstrained.
    // Negated check: NOT(sum >= 0) — SAT (sum can be negative).
    let sum = Formula::Var("sum".into(), Sort::Int);
    let formula = Formula::Not(Box::new(Formula::Ge(Box::new(sum), Box::new(Formula::Int(0)))));

    let vc = make_vc(
        VcKind::LoopInvariantInitiation { invariant: "sum >= 0".to_string(), header_block: 0 },
        "loop_init_buggy",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("loop invariant initiation buggy: {:?}", result);
    assert!(
        result.is_failed(),
        "ay must find loop invariant initiation violation. Got: {result:?}"
    );
}

#[test]
fn test_loop_invariant_initiation_safe() {
    let ay = require_ay();
    // Invariant: sum >= 0. At entry sum == 0 (properly initialized).
    // Check: sum == 0 AND NOT(sum >= 0) — UNSAT (0 >= 0 is true).
    let sum = Formula::Var("sum".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Eq(Box::new(sum.clone()), Box::new(Formula::Int(0))),
        Formula::Not(Box::new(Formula::Ge(Box::new(sum), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(
        VcKind::LoopInvariantInitiation { invariant: "sum >= 0".to_string(), header_block: 0 },
        "loop_init_safe",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("loop invariant initiation safe: {:?}", result);
    assert!(result.is_proved(), "ay must prove loop invariant holds at entry. Got: {result:?}");
}

// --- B4: LoopInvariantConsecution ---

#[test]
fn test_loop_invariant_consecution_buggy() {
    let ay = require_ay();
    // Invariant: i < 10. After iteration: i' = i + 1.
    // Check: i < 10 AND NOT(i + 1 < 10) — SAT at i = 9 (9 < 10 but 10 < 10 is false).
    let i = Formula::Var("i".into(), Sort::Int);
    let i_next = Formula::Add(Box::new(i.clone()), Box::new(Formula::Int(1)));
    let formula = Formula::And(vec![
        Formula::Lt(Box::new(i), Box::new(Formula::Int(10))),
        Formula::Not(Box::new(Formula::Lt(Box::new(i_next), Box::new(Formula::Int(10))))),
    ]);

    let vc = make_vc(
        VcKind::LoopInvariantConsecution { invariant: "i < 10".to_string(), header_block: 0 },
        "loop_consec_buggy",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("loop invariant consecution buggy: {:?}", result);
    assert!(
        result.is_failed(),
        "ay must find loop invariant consecution violation. Got: {result:?}"
    );
}

#[test]
fn test_loop_invariant_consecution_safe() {
    let ay = require_ay();
    // Invariant: i <= 10. After iteration: i' = i + 1 (loop guard: i < 10).
    // Check: i <= 10 AND i < 10 AND NOT(i + 1 <= 10) — UNSAT.
    // (i < 10 means i <= 9, so i + 1 <= 10.)
    let i = Formula::Var("i".into(), Sort::Int);
    let i_next = Formula::Add(Box::new(i.clone()), Box::new(Formula::Int(1)));
    let formula = Formula::And(vec![
        Formula::Le(Box::new(i.clone()), Box::new(Formula::Int(10))),
        Formula::Lt(Box::new(i), Box::new(Formula::Int(10))),
        Formula::Not(Box::new(Formula::Le(Box::new(i_next), Box::new(Formula::Int(10))))),
    ]);

    let vc = make_vc(
        VcKind::LoopInvariantConsecution { invariant: "i <= 10".to_string(), header_block: 0 },
        "loop_consec_safe",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("loop invariant consecution safe: {:?}", result);
    assert!(
        result.is_proved(),
        "ay must prove loop invariant preserved by iteration. Got: {result:?}"
    );
}

// --- B5: LoopInvariantSufficiency ---

#[test]
fn test_loop_invariant_sufficiency_buggy() {
    let ay = require_ay();
    // Invariant: sum >= 0. Postcondition: sum > 0.
    // At loop exit with invariant: sum >= 0 AND NOT(sum > 0) — SAT at sum = 0.
    // The invariant is too weak to imply the postcondition.
    let sum = Formula::Var("sum".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Ge(Box::new(sum.clone()), Box::new(Formula::Int(0))),
        Formula::Not(Box::new(Formula::Gt(Box::new(sum), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(
        VcKind::LoopInvariantSufficiency { invariant: "sum >= 0".to_string(), header_block: 0 },
        "loop_suff_buggy",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("loop invariant sufficiency buggy: {:?}", result);
    assert!(
        result.is_failed(),
        "ay must find loop invariant too weak for postcondition. Got: {result:?}"
    );
}

#[test]
fn test_loop_invariant_sufficiency_safe() {
    let ay = require_ay();
    // Invariant: sum > 0. Postcondition: sum >= 0.
    // At loop exit: sum > 0 AND NOT(sum >= 0) — UNSAT (stronger implies weaker).
    let sum = Formula::Var("sum".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Gt(Box::new(sum.clone()), Box::new(Formula::Int(0))),
        Formula::Not(Box::new(Formula::Ge(Box::new(sum), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(
        VcKind::LoopInvariantSufficiency { invariant: "sum > 0".to_string(), header_block: 0 },
        "loop_suff_safe",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("loop invariant sufficiency safe: {:?}", result);
    assert!(
        result.is_proved(),
        "ay must prove loop invariant implies postcondition. Got: {result:?}"
    );
}

// --- B6: TypeRefinementViolation ---

#[test]
fn test_type_refinement_buggy() {
    let ay = require_ay();
    // Refinement: x > 0. With unconstrained x: NOT(x > 0) — SAT.
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::Not(Box::new(Formula::Gt(Box::new(x), Box::new(Formula::Int(0)))));

    let vc = make_vc(
        VcKind::TypeRefinementViolation {
            variable: "x".to_string(),
            predicate: "x > 0".to_string(),
        },
        "refine_buggy",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("type refinement buggy: {:?}", result);
    assert!(result.is_failed(), "ay must find type refinement violation. Got: {result:?}");
}

#[test]
fn test_type_refinement_safe() {
    let ay = require_ay();
    // x == 5 and check x > 0: x == 5 AND NOT(x > 0) — UNSAT.
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Eq(Box::new(x.clone()), Box::new(Formula::Int(5))),
        Formula::Not(Box::new(Formula::Gt(Box::new(x), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(
        VcKind::TypeRefinementViolation {
            variable: "x".to_string(),
            predicate: "x > 0".to_string(),
        },
        "refine_safe",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("type refinement safe: {:?}", result);
    assert!(result.is_proved(), "ay must prove type refinement holds. Got: {result:?}");
}

// --- B7: FrameConditionViolation ---

#[test]
fn test_frame_condition_buggy() {
    let ay = require_ay();
    // Frame condition: old(x) == x. With unconstrained x__old and x:
    // NOT(x__old == x) — SAT.
    let x_old = Formula::Var("x__old".into(), Sort::Int);
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::Not(Box::new(Formula::Eq(Box::new(x_old), Box::new(x))));

    let vc = make_vc(
        VcKind::FrameConditionViolation {
            variable: "x".to_string(),
            function: "frame_buggy".into(),
        },
        "frame_buggy",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("frame condition buggy: {:?}", result);
    assert!(result.is_failed(), "ay must find frame condition violation. Got: {result:?}");
}

#[test]
fn test_frame_condition_safe() {
    let ay = require_ay();
    // Frame condition holds: x__old == x AND NOT(x__old == x) — UNSAT.
    let x_old = Formula::Var("x__old".into(), Sort::Int);
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Eq(Box::new(x_old.clone()), Box::new(x.clone())),
        Formula::Not(Box::new(Formula::Eq(Box::new(x_old), Box::new(x)))),
    ]);

    let vc = make_vc(
        VcKind::FrameConditionViolation {
            variable: "x".to_string(),
            function: "frame_safe".into(),
        },
        "frame_safe",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("frame condition safe: {:?}", result);
    assert!(result.is_proved(), "ay must prove frame condition holds. Got: {result:?}");
}

// --- B8: FunctionalCorrectness ---

#[test]
fn test_functional_correctness_buggy() {
    let ay = require_ay();
    // Property: result == x + 1. With unconstrained result and x:
    // NOT(result == x + 1) — SAT.
    let x = Formula::Var("x".into(), Sort::Int);
    let result_var = Formula::Var("result".into(), Sort::Int);
    let formula = Formula::Not(Box::new(Formula::Eq(
        Box::new(result_var),
        Box::new(Formula::Add(Box::new(x), Box::new(Formula::Int(1)))),
    )));

    let vc = make_vc(
        VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "increment function".to_string(),
        },
        "func_correct_buggy",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("functional correctness buggy: {:?}", result);
    assert!(result.is_failed(), "ay must find functional correctness violation. Got: {result:?}");
}

#[test]
fn test_functional_correctness_safe() {
    let ay = require_ay();
    // result == x + 1 with x >= 0: check result > 0.
    // x >= 0 AND result == x + 1 AND NOT(result > 0) — UNSAT.
    let x = Formula::Var("x".into(), Sort::Int);
    let result_var = Formula::Var("result".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0))),
        Formula::Eq(
            Box::new(result_var.clone()),
            Box::new(Formula::Add(Box::new(x), Box::new(Formula::Int(1)))),
        ),
        Formula::Not(Box::new(Formula::Gt(Box::new(result_var), Box::new(Formula::Int(0))))),
    ]);

    let vc = make_vc(
        VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "increment function".to_string(),
        },
        "func_correct_safe",
        formula,
    );

    let result = ay.verify(&vc);
    eprintln!("functional correctness safe: {:?}", result);
    assert!(result.is_proved(), "ay must prove functional correctness. Got: {result:?}");
}
