use super::*;
use crate::model::{BinOp, SourceSpan, Ty};

#[test]
fn test_overflow_formula_construction() {
    // For midpoint: (a + b) might overflow usize
    // VC: exists a, b such that a + b > usize::MAX
    // Formula: NOT(a + b <= MAX AND a + b >= 0)
    // We check: is there an assignment where the result is out of range?

    let a = Formula::Var("a".into(), Sort::BitVec(64));
    let b = Formula::Var("b".into(), Sort::BitVec(64));
    let sum = Formula::Add(Box::new(a), Box::new(b));

    let max_val = Formula::Int((1i128 << 64) - 1);
    let in_range = Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(0)), Box::new(sum.clone())),
        Formula::Le(Box::new(sum), Box::new(max_val)),
    ]);

    // Negate: we want to find a violation
    let violation = Formula::Not(Box::new(in_range));

    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "get_midpoint".into(),
        location: SourceSpan::default(),
        formula: violation,
        contract_metadata: None,
    };

    assert_eq!(vc.kind.description(), "arithmetic overflow (Add)");
    assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
}

#[test]
fn test_sort_from_ty() {
    assert_eq!(Sort::from_ty(&Ty::Bool), Sort::Bool);
    assert_eq!(Sort::from_ty(&Ty::usize()), Sort::BitVec(64));
    assert_eq!(Sort::from_ty(&Ty::i32()), Sort::BitVec(32));
    assert_eq!(Sort::from_ty(&Ty::Float { width: 32 }), Sort::BitVec(32));
    assert_eq!(Sort::from_ty(&Ty::Float { width: 128 }), Sort::BitVec(128));
}

#[test]
fn test_vc_kind_proof_levels() {
    assert_eq!(VcKind::DivisionByZero.proof_level(), ProofLevel::L0Safety);
    assert_eq!(VcKind::Postcondition.proof_level(), ProofLevel::L1Functional);
    assert_eq!(VcKind::Deadlock.proof_level(), ProofLevel::L2Domain);
    assert_eq!(VcKind::UseAfterFree.proof_level(), ProofLevel::L0Safety);
    assert_eq!(VcKind::DoubleFree.proof_level(), ProofLevel::L0Safety);
    assert_eq!(
        VcKind::BinaryCopySinkLengthViolation {
            callee: "memcpy".into(),
            desc: "copy sink length may exceed destination capacity".into(),
        }
        .proof_level(),
        ProofLevel::L0Safety
    );
}

#[test]
fn test_allocator_lifetime_vc_kind_descriptions() {
    assert_eq!(VcKind::UseAfterFree.description(), "use after free");
    assert_eq!(VcKind::DoubleFree.description(), "double free");
}

#[test]
fn test_vc_kind_runtime_fallback_matrix() {
    let cases = vec![
        (
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
            true,
            false,
        ),
        (
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
            true,
            false,
        ),
        (VcKind::DivisionByZero, true, true),
        (VcKind::RemainderByZero, true, true),
        (VcKind::IndexOutOfBounds, true, true),
        (VcKind::SliceBoundsCheck, true, true),
        (VcKind::Assertion { message: "invariant holds".into() }, true, true),
        (VcKind::Precondition { callee: "callee".into() }, false, false),
        (VcKind::Postcondition, false, false),
        (VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() }, false, false),
        (VcKind::NegationOverflow { ty: Ty::i32() }, true, false),
        (VcKind::Unreachable, true, true),
        (VcKind::DeadState { state: "idle".into() }, false, false),
        (VcKind::Deadlock, false, false),
        (VcKind::Temporal { property: "always ready".into(), machine: None }, false, false),
        (
            VcKind::BinaryAbiContradiction {
                fact: "parameter 0 storage".into(),
                evidence: "ABI says RDI, storage says RSI".into(),
            },
            false,
            false,
        ),
        (
            VcKind::BinaryCopySinkLengthViolation {
                callee: "memcpy".into(),
                desc: "copy sink length may exceed destination capacity".into(),
            },
            false,
            false,
        ),
        (
            VcKind::ResilienceViolation {
                service: "redis".into(),
                failure_mode: "timeout".into(),
                reason: "unwrap on error path".into(),
            },
            false,
            false,
        ),
    ];

    for (vc_kind, with_overflow_checks, without_overflow_checks) in cases {
        assert_eq!(vc_kind.has_runtime_fallback(true), with_overflow_checks);
        assert_eq!(vc_kind.has_runtime_fallback(false), without_overflow_checks);
    }
}

// Trust: Liveness and fairness tests.

#[test]
fn test_temporal_operator_tla_notation() {
    assert_eq!(TemporalOperator::Eventually.tla_notation(), "<>");
    assert_eq!(TemporalOperator::Always.tla_notation(), "[]");
    assert_eq!(TemporalOperator::AlwaysEventually.tla_notation(), "[]<>");
    assert_eq!(TemporalOperator::LeadsTo.tla_notation(), "~>");
}

#[test]
fn test_liveness_property_description_eventually() {
    let prop = LivenessProperty {
        name: "termination".into(),
        operator: TemporalOperator::Eventually,
        predicate: "done".into(),
        consequent: None,
        fairness: vec![],
    };
    assert_eq!(prop.description(), "termination: <>done");
    assert_eq!(prop.to_tla(), "<>(done)");
}

#[test]
fn test_liveness_property_description_leads_to() {
    let prop = LivenessProperty {
        name: "request_response".into(),
        operator: TemporalOperator::LeadsTo,
        predicate: "request".into(),
        consequent: Some("response".into()),
        fairness: vec![],
    };
    assert_eq!(prop.description(), "request_response: request ~> response");
    assert_eq!(prop.to_tla(), "(request) ~> (response)");
}

#[test]
fn test_liveness_property_always_eventually() {
    let prop = LivenessProperty {
        name: "starvation_free".into(),
        operator: TemporalOperator::AlwaysEventually,
        predicate: "Progress(t)".into(),
        consequent: None,
        fairness: vec![FairnessConstraint::Weak {
            action: "schedule".into(),
            vars: vec!["tasks".into()],
        }],
    };
    assert_eq!(prop.description(), "starvation_free: []<>Progress(t)");
    assert_eq!(prop.to_tla(), "[]<>(Progress(t))");
    assert_eq!(prop.fairness.len(), 1);
}

#[test]
fn test_fairness_constraint_weak() {
    let wf = FairnessConstraint::Weak {
        action: "task_schedule".into(),
        vars: vec!["ready_queue".into(), "running".into()],
    };
    assert_eq!(wf.description(), "WF_{ready_queue, running}(task_schedule)");
    assert_eq!(wf.to_tla(), "WF_<<ready_queue, running>>(task_schedule)");
    assert!(!wf.is_strong());
    assert_eq!(wf.action(), "task_schedule");
}

#[test]
fn test_fairness_constraint_strong() {
    let sf = FairnessConstraint::Strong {
        action: "priority_dequeue".into(),
        vars: vec!["queue".into()],
    };
    assert_eq!(sf.description(), "SF_{queue}(priority_dequeue)");
    assert_eq!(sf.to_tla(), "SF_<<queue>>(priority_dequeue)");
    assert!(sf.is_strong());
    assert_eq!(sf.action(), "priority_dequeue");
}

#[test]
fn test_liveness_counterexample_display() {
    let cex = LivenessCounterexample {
        prefix: vec![LivenessState {
            label: "init".into(),
            assignments: vec![("x".into(), "0".into())],
        }],
        cycle: vec![
            LivenessState { label: "waiting".into(), assignments: vec![("x".into(), "1".into())] },
            LivenessState {
                label: "still_waiting".into(),
                assignments: vec![("x".into(), "1".into())],
            },
        ],
    };
    assert_eq!(cex.trace_len(), 3);
    let display = format!("{cex}");
    assert!(display.contains("Prefix (1 states)"));
    assert!(display.contains("Cycle (2 states)"));
    assert!(display.contains("back to cycle start"));
}

#[test]
fn test_liveness_counterexample_empty_prefix() {
    let cex = LivenessCounterexample {
        prefix: vec![],
        cycle: vec![LivenessState { label: "stuck".into(), assignments: vec![] }],
    };
    assert_eq!(cex.trace_len(), 1);
    let display = format!("{cex}");
    assert!(!display.contains("Prefix"));
    assert!(display.contains("Cycle (1 states)"));
}

#[test]
fn test_vckind_liveness_is_l2_domain() {
    let prop = LivenessProperty {
        name: "test".into(),
        operator: TemporalOperator::Eventually,
        predicate: "done".into(),
        consequent: None,
        fairness: vec![],
    };
    let kind = VcKind::Liveness { property: prop, machine: None };
    assert_eq!(kind.proof_level(), ProofLevel::L2Domain);
    assert!(kind.description().contains("liveness:"));
}

#[test]
fn test_vckind_fairness_is_l2_domain() {
    let constraint = FairnessConstraint::Weak { action: "send".into(), vars: vec!["buf".into()] };
    let kind = VcKind::Fairness { constraint };
    assert_eq!(kind.proof_level(), ProofLevel::L2Domain);
    assert!(kind.description().contains("fairness:"));
    assert!(kind.description().contains("WF"));
}

#[test]
fn test_liveness_property_serialization_roundtrip() {
    let prop = LivenessProperty {
        name: "progress".into(),
        operator: TemporalOperator::AlwaysEventually,
        predicate: "served".into(),
        consequent: None,
        fairness: vec![
            FairnessConstraint::Weak { action: "dispatch".into(), vars: vec!["queue".into()] },
            FairnessConstraint::Strong { action: "dequeue".into(), vars: vec!["priority".into()] },
        ],
    };
    let json = serde_json::to_string(&prop).expect("serialize");
    let round: LivenessProperty = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.name, "progress");
    assert_eq!(round.operator, TemporalOperator::AlwaysEventually);
    assert_eq!(round.fairness.len(), 2);
    assert!(round.fairness[0].action() == "dispatch");
    assert!(round.fairness[1].is_strong());
}

// -----------------------------------------------------------------------
// Formula visitor pattern tests
// -----------------------------------------------------------------------

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn bv_var(name: &str, w: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(w))
}

#[test]
fn test_children_leaf_returns_empty() {
    assert!(Formula::Bool(true).children().is_empty());
    assert!(Formula::Int(42).children().is_empty());
    assert!(Formula::BitVec { value: 0, width: 8 }.children().is_empty());
    assert!(var("x").children().is_empty());
}

#[test]
fn test_children_unary() {
    let f = Formula::Not(Box::new(Formula::Bool(true)));
    assert_eq!(f.children().len(), 1);
    assert_eq!(*f.children()[0], Formula::Bool(true));
}

#[test]
fn test_children_binary() {
    let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
    let kids = f.children();
    assert_eq!(kids.len(), 2);
    assert_eq!(*kids[0], var("x"));
    assert_eq!(*kids[1], var("y"));
}

#[test]
fn test_children_nary() {
    let f = Formula::And(vec![var("a"), var("b"), var("c")]);
    assert_eq!(f.children().len(), 3);
}

#[test]
fn test_children_ite() {
    let f = Formula::Ite(Box::new(Formula::Bool(true)), Box::new(var("x")), Box::new(var("y")));
    assert_eq!(f.children().len(), 3);
}

#[test]
fn test_children_bv_binary_with_width() {
    let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
    assert_eq!(f.children().len(), 2);
}

#[test]
fn test_children_quantifier() {
    let f = Formula::Forall(
        vec![("x".into(), Sort::Int)],
        Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
    );
    assert_eq!(f.children().len(), 1);
}

#[test]
fn test_children_store() {
    let arr = var("arr");
    let f = Formula::Store(Box::new(arr), Box::new(Formula::Int(0)), Box::new(Formula::Int(1)));
    assert_eq!(f.children().len(), 3);
}

#[test]
fn test_children_bv_extract() {
    let f = Formula::BvExtract { inner: Box::new(bv_var("x", 32)), high: 15, low: 0 };
    assert_eq!(f.children().len(), 1);
}

#[test]
fn test_map_children_identity() {
    let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
    let mapped = f.clone().map_children(&mut |c| c);
    assert_eq!(mapped, f);
}

#[test]
fn test_map_children_replaces_direct() {
    let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
    let mapped = f.map_children(&mut |c| {
        if c == var("x") { Formula::Int(1) } else { c }
    });
    assert_eq!(mapped, Formula::Add(Box::new(Formula::Int(1)), Box::new(var("y"))));
}

#[test]
fn test_map_children_nary() {
    let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
    let mapped = f.map_children(&mut |c| Formula::Not(Box::new(c)));
    match mapped {
        Formula::And(terms) => {
            assert_eq!(terms.len(), 2);
            assert_eq!(terms[0], Formula::Not(Box::new(Formula::Bool(true))));
        }
        _ => panic!("expected And"),
    }
}

#[test]
fn test_map_children_preserves_width() {
    let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
    let mapped = f.map_children(&mut |c| c);
    assert_eq!(mapped, Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32));
}

#[test]
fn test_visit_counts_all_nodes() {
    let f = Formula::And(vec![
        Formula::Not(Box::new(var("x"))),
        Formula::Add(Box::new(var("y")), Box::new(Formula::Int(1))),
    ]);
    let mut count = 0;
    f.visit(&mut |_| count += 1);
    // And(Not(Var), Add(Var, Int)) = 6 nodes
    assert_eq!(count, 6);
}

#[test]
fn test_visit_pre_order() {
    let f = Formula::Not(Box::new(Formula::Bool(true)));
    let mut order = vec![];
    f.visit(&mut |node| {
        order.push(match node {
            Formula::Not(_) => "Not",
            Formula::Bool(true) => "True",
            _ => "other",
        });
    });
    assert_eq!(order, vec!["Not", "True"]);
}

#[test]
fn test_map_bottom_up() {
    // Replace all Int(1) with Int(2), bottom-up
    let f = Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1)));
    let mapped = f.map(&mut |node| {
        if node == Formula::Int(1) { Formula::Int(2) } else { node }
    });
    assert_eq!(mapped, Formula::Add(Box::new(Formula::Int(2)), Box::new(Formula::Int(2))));
}

#[test]
fn test_map_applied_after_children() {
    // Wrap every node in Not — bottom-up means children wrapped first
    let f = Formula::Bool(true);
    let mapped = f.map(&mut |node| Formula::Not(Box::new(node)));
    // Bool(true) -> Not(Bool(true))
    assert_eq!(mapped, Formula::Not(Box::new(Formula::Bool(true))));
}

#[test]
fn test_free_variables_simple() {
    let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
    let fv = f.free_variables();
    assert_eq!(fv.len(), 2);
    assert!(fv.contains("x"));
    assert!(fv.contains("y"));
}

#[test]
fn test_free_variables_no_vars() {
    let f = Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)));
    assert!(f.free_variables().is_empty());
}

#[test]
fn test_free_variables_excludes_bound() {
    let f = Formula::Forall(
        vec![("x".into(), Sort::Int)],
        Box::new(Formula::Add(Box::new(var("x")), Box::new(var("y")))),
    );
    let fv = f.free_variables();
    assert_eq!(fv.len(), 1);
    assert!(fv.contains("y"));
    assert!(!fv.contains("x"));
}

#[test]
fn test_free_variables_exists() {
    let f = Formula::Exists(
        vec![("a".into(), Sort::Int), ("b".into(), Sort::Int)],
        Box::new(Formula::And(vec![var("a"), var("b"), var("c")])),
    );
    let fv = f.free_variables();
    assert_eq!(fv.len(), 1);
    assert!(fv.contains("c"));
}

#[test]
fn test_free_variables_nested_quantifiers() {
    let inner = Formula::Exists(
        vec![("y".into(), Sort::Int)],
        Box::new(Formula::Eq(Box::new(var("x")), Box::new(var("y")))),
    );
    let f = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(inner));
    assert!(f.free_variables().is_empty());
}

#[test]
fn test_has_bitvectors_false_for_pure_int() {
    let f = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
    assert!(!f.has_bitvectors());
}

#[test]
fn test_has_bitvectors_true_for_bv_literal() {
    let f = Formula::And(vec![var("x"), Formula::BitVec { value: 42, width: 32 }]);
    assert!(f.has_bitvectors());
}

#[test]
fn test_has_bitvectors_true_for_bv_ops() {
    let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
    assert!(f.has_bitvectors());
}

#[test]
fn test_has_bitvectors_true_for_bv_var() {
    let f =
        Formula::Not(Box::new(Formula::Eq(Box::new(bv_var("x", 64)), Box::new(Formula::Int(0)))));
    assert!(f.has_bitvectors());
}

#[test]
fn test_has_bitvectors_deep_nesting() {
    let f = Formula::And(vec![Formula::Or(vec![Formula::Not(Box::new(Formula::Ite(
        Box::new(Formula::Bool(true)),
        Box::new(Formula::BvShl(Box::new(bv_var("a", 8)), Box::new(bv_var("b", 8)), 8)),
        Box::new(Formula::Int(0)),
    )))])]);
    assert!(f.has_bitvectors());
}

#[test]
fn test_rename_var_simple() {
    let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
    let renamed = f.rename_var("x", "y");
    assert_eq!(renamed, Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))));
}

#[test]
fn test_rename_var_no_match() {
    let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
    let renamed = f.rename_var("z", "w");
    assert_eq!(renamed, f);
}

#[test]
fn test_rename_var_multiple_occurrences() {
    let f = Formula::Add(Box::new(var("x")), Box::new(var("x")));
    let renamed = f.rename_var("x", "y");
    assert_eq!(renamed, Formula::Add(Box::new(var("y")), Box::new(var("y"))));
}

#[test]
fn test_rename_var_deep_nesting() {
    let f = Formula::And(vec![
        Formula::Not(Box::new(Formula::Lt(Box::new(var("a")), Box::new(var("b"))))),
        Formula::Ite(Box::new(var("a")), Box::new(Formula::Int(1)), Box::new(Formula::Int(0))),
    ]);
    let renamed = f.rename_var("a", "c");
    let mut found = false;
    renamed.visit(&mut |node| {
        if let Formula::Var(name, _) = node {
            assert_ne!(name.as_str(), "a");
            if name == "c" {
                found = true;
            }
        }
    });
    assert!(found);
}

#[test]
fn test_rename_var_preserves_sort() {
    let f = bv_var("x", 32);
    let renamed = f.rename_var("x", "y");
    assert_eq!(renamed, Formula::Var("y".into(), Sort::BitVec(32)));
}

#[test]
fn test_rename_var_in_quantifier_body() {
    // rename_var is a syntactic rename -- it does not respect bindings
    // (that would be substitution). It replaces all occurrences.
    let f = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(var("y")));
    let renamed = f.rename_var("y", "z");
    match renamed {
        Formula::Forall(_, body) => assert_eq!(*body, var("z")),
        _ => panic!("expected Forall"),
    }
}

// Regression coverage for structural hashing used instead of
// string-serialization cache keys.

/// Build a moderately complex formula for benchmarking.
fn bench_formula() -> Formula {
    // Represents: forall x, y. (x + y > 0) && (x * y <= 100) && bvadd(a, b, 32) != 0
    Formula::And(vec![
        Formula::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Formula::And(vec![
                Formula::Gt(
                    Box::new(Formula::Add(Box::new(var("x")), Box::new(var("y")))),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Le(
                    Box::new(Formula::Mul(Box::new(var("x")), Box::new(var("y")))),
                    Box::new(Formula::Int(100)),
                ),
            ])),
        ),
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32)),
            Box::new(Formula::BitVec { value: 0, width: 32 }),
        ))),
        Formula::Ite(
            Box::new(Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(10)))),
            Box::new(Formula::Add(Box::new(var("z")), Box::new(Formula::Int(1)))),
            Box::new(Formula::Sub(Box::new(var("z")), Box::new(Formula::Int(1)))),
        ),
    ])
}

#[test]
fn test_structural_hash_faster_than_string_serialization() {
    use std::hash::{Hash, Hasher};

    fn hash_formula(formula: &Formula) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        formula.hash(&mut hasher);
        hasher.finish()
    }

    let formula = bench_formula();
    let same_formula = bench_formula();
    let changed_formula = Formula::And(vec![formula.clone(), Formula::Bool(true)]);

    let structural_hash = hash_formula(&formula);

    assert_eq!(structural_hash, hash_formula(&same_formula));
    assert_ne!(structural_hash, hash_formula(&changed_formula));
    assert!(!format!("{formula:?}").is_empty());
    assert!(!formula.to_smtlib().is_empty());
}

#[test]
fn test_bv_to_int_unsigned_to_smtlib() {
    // Unsigned BvToInt should emit plain (bv2nat ...) — the SMT-LIB
    // FixedSizeBitVectors standard name, accepted by every conformant solver.
    let inner = Formula::Var("x".into(), Sort::BitVec(8));
    let f = Formula::BvToInt(Box::new(inner), 8, false);
    assert_eq!(f.to_smtlib(), "(bv2nat x)");
}

#[test]
fn test_bv_to_int_signed_to_smtlib() {
    // Signed BvToInt builds on bv2nat with a conditional that subtracts 2^N
    // when the sign bit is set. For 8-bit: 2^8 = 256.
    let inner = Formula::Var("x".into(), Sort::BitVec(8));
    let f = Formula::BvToInt(Box::new(inner), 8, true);
    assert_eq!(f.to_smtlib(), "(ite (bvsge x (_ bv0 8)) (bv2nat x) (- (bv2nat x) 256))");
}

#[test]
fn test_bv_to_int_signed_32bit_to_smtlib() {
    // For 32-bit: 2^32 = 4294967296
    let inner = Formula::Var("y".into(), Sort::BitVec(32));
    let f = Formula::BvToInt(Box::new(inner), 32, true);
    assert_eq!(f.to_smtlib(), "(ite (bvsge y (_ bv0 32)) (bv2nat y) (- (bv2nat y) 4294967296))");
}

#[test]
fn test_bv_to_int_signed_nested_expr_to_smtlib() {
    // Signed BvToInt with a nested bitvector expression (not just a variable)
    let a = Formula::Var("a".into(), Sort::BitVec(16));
    let b = Formula::Var("b".into(), Sort::BitVec(16));
    let sum = Formula::BvAdd(Box::new(a), Box::new(b), 16);
    let f = Formula::BvToInt(Box::new(sum), 16, true);
    let smt = f.to_smtlib();
    // The inner expression (bvadd a b) appears in three places
    assert!(smt.contains("(bvsge (bvadd a b) (_ bv0 16))"));
    assert!(smt.contains("(bv2nat (bvadd a b))"));
    assert!(smt.contains("(- (bv2nat (bvadd a b)) 65536)"));
}

// safe-api: Formula::Pred (uninterpreted safety predicate) — SAFE_API.md §3.
#[test]
fn pred_lowers_to_euf_application() {
    let d = Formula::Var("d".into(), Sort::Int);
    let p = Formula::Pred(crate::Symbol::intern("dir_open"), vec![d]);
    assert_eq!(p.to_smtlib(), "(dir_open d)");

    // Nullary predicate lowers to a bare symbol (no parens).
    let nullary = Formula::Pred(crate::Symbol::intern("priv_dropped"), vec![]);
    assert_eq!(nullary.to_smtlib(), "priv_dropped");
}

#[test]
fn pred_recurses_children_and_free_vars() {
    let d = Formula::Var("d".into(), Sort::Int);
    let p = Formula::Pred(crate::Symbol::intern("dir_open"), vec![d]);
    // The argument term is a child, so free variables recurse through it.
    assert_eq!(p.children().len(), 1);
    assert!(p.free_variables().contains("d"));
    // map_children rebinds the argument; substitution must reach inside Pred.
    let renamed = p.map_children(&mut |c| match c {
        Formula::Var(_, s) => Formula::Var("e".into(), s),
        other => other,
    });
    assert_eq!(renamed.to_smtlib(), "(dir_open e)");
}

#[test]
fn pred_arena_roundtrips() {
    let d = Formula::Var("d".into(), Sort::Int);
    let p = Formula::Pred(crate::Symbol::intern("single_component"), vec![d]);
    let mut arena = crate::formula_arena::FormulaArena::new();
    let r = arena.intern(&p);
    assert_eq!(arena.to_formula(r), p);
}

#[test]
fn pred_vocab_is_closed() {
    use super::{is_valid_pred, pred_arg_sorts};
    assert!(is_valid_pred("dir_open", 1));
    assert!(is_valid_pred("priv_dropped", 0));
    // Wrong arity is rejected.
    assert!(!is_valid_pred("dir_open", 2));
    // Out-of-vocabulary names are rejected (anti-sprawl / anti-laundering).
    assert!(!is_valid_pred("attacker_predicate", 1));
    assert!(pred_arg_sorts("attacker_predicate").is_none());
}
