// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use clean_kernel::Name;
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::*;

/// `cost <= limit.wrapping_{op}(held)`: the marker-authenticated wrapping
/// call TG14 reads as its exact modular image. A raw `BinaryOp(op)` is an
/// undischarged panic operation the reader refuses
/// (`raw_and_overflow_checked_budgets_are_never_admitted`).
fn budget(width: u32, signed: bool, op: BinOp) -> VerifiableFunction {
    let scalar = Ty::Int { width, signed };
    let cp = |i| Operand::Copy(Place::local(i));
    let method = match op {
        BinOp::Add => "wrapping_add",
        BinOp::Sub => "wrapping_sub",
        BinOp::Mul => "wrapping_mul",
        _ => panic!("arithmetic"),
    };
    let marker = format!(
        "{}core::num::<impl {}{width}>::{method}",
        trust_types::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX,
        if signed { "i" } else { "u" }
    );
    VerifiableFunction {
        name: "budget".into(),
        def_path: "crate::budget".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: [Ty::Bool, scalar.clone(), scalar.clone(), scalar.clone(), scalar]
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: marker,
                        args: vec![cp(2), cp(3)],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: Default::default(),
                        callee_identity: None,
                        callee_key: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(BinOp::Le, cp(1), cp(4)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn admit(session: &mut CleanIslandSession, f: VerifiableFunction) {
    // The separately tested admission precondition is deliberately explicit:
    // these tests exercise the image and kernel, not overflow-facet inference.
    let facets = trust_spec_elab::FacetTable::from_structural_facets([(
        "crate::budget",
        true,
        true,
        true,
        true,
    )]);
    assert_eq!(session.admit_program_functions(&[f], &facets).len(), 1);
}

#[test]
fn raw_and_overflow_checked_budgets_are_never_admitted() {
    // E6-TG14-PANIC-EDGE-1: with every facet forced, neither a raw
    // `BinaryOp(op)` nor rustc's overflow-checked `limit - held` (the
    // `CheckedBinaryOp` pair, its overflow `Assert`, then `.0`) mints. The
    // unsigned checked `limit - held` panics at `(0, 0, 1)`, where the
    // wrapped image would answer `true`.
    use trust_types::{AssertMessage, Projection};
    let facets = trust_spec_elab::FacetTable::from_structural_facets([(
        "crate::budget",
        true,
        true,
        true,
        true,
    )]);
    let cp = |i| Operand::Copy(Place::local(i));
    let asn = |i, rvalue| Statement::Assign {
        place: Place::local(i),
        rvalue,
        span: SourceSpan::default(),
    };
    let field = |i| Operand::Move(Place { local: 5, projections: vec![Projection::Field(i)] });
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
                let mut raw = budget(width, signed, op);
                raw.body.blocks = vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        asn(4, Rvalue::BinaryOp(op, cp(2), cp(3))),
                        asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), cp(4))),
                    ],
                    terminator: Terminator::Return,
                }];
                let mut checked = budget(width, signed, op);
                checked.body.locals.push(LocalDecl {
                    index: 5,
                    ty: Ty::Tuple(vec![Ty::Int { width, signed }, Ty::Bool]),
                    name: None,
                });
                checked.body.blocks = vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![asn(5, Rvalue::CheckedBinaryOp(op, cp(2), cp(3)))],
                        terminator: Terminator::Assert {
                            cond: field(1),
                            expected: false,
                            msg: AssertMessage::Overflow(op),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                            unwind: Default::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![
                            asn(4, Rvalue::Use(field(0))),
                            asn(0, Rvalue::BinaryOp(BinOp::Le, cp(1), cp(4))),
                        ],
                        terminator: Terminator::Return,
                    },
                ];
                for (form, f) in [("raw", raw), ("overflow-checked", checked)] {
                    let mut session = CleanIslandSession::new();
                    assert!(
                        session.admit_program_functions(&[f], &facets).is_empty(),
                        "the {form} {op:?} budget at {width}/{signed} was admitted"
                    );
                    assert!(!session.is_tainted());
                }
            }
        }
    }
}

#[test]
fn computed_subtraction_imports_and_operator_mutant_refuses() {
    for width in [8, 16, 32, 64] {
        let source = format!(
            "theorem exact_budget (cost limit held : UInt{width}) : trust_import_crate__budget cost limit held = decide (cost <= limit - held) := rfl"
        );
        let mut session = CleanIslandSession::new();
        admit(&mut session, budget(width, false, BinOp::Sub));
        let outcome = session.check_import_island(&source);
        assert!(!outcome.is_rejected(), "u{width}: {outcome:?}");
        let mut mutant = CleanIslandSession::new();
        admit(&mut mutant, budget(width, false, BinOp::Add));
        assert!(
            mutant.check_import_island(&source).is_rejected(),
            "+ must not prove - at u{width}"
        );
        assert!(!mutant.is_tainted());
        assert!(
            mutant
                .environment()
                .unwrap()
                .get_const(&clean_kernel::Name::from_string("exact_budget"))
                .is_none()
        );
    }
}

#[test]
fn refused_import_rolls_back_whole_island_and_preserves_other_citations() {
    let mut session = CleanIslandSession::new();
    let first = session.check_import_island("theorem prior : (1 : Nat) = 1 := rfl");
    assert!(!first.is_rejected(), "{first:?}");
    let failed = session.check_import_island(
        "def leaked : Nat := 7\ntheorem bad : trust_import_missing 0 = 0 := rfl",
    );
    assert!(failed.is_rejected());
    assert!(!session.is_tainted());
    assert!(
        session
            .environment()
            .unwrap()
            .get_const(&clean_kernel::Name::from_string("leaked"))
            .is_none()
    );
    let later = session.check_import_island("theorem later : (2 : Nat) = 2 := rfl");
    assert!(!later.is_rejected(), "{later:?}");
    let mut proved = 0;
    for (theorem, clause) in [("prior", "1 == 1"), ("later", "2 == 2")] {
        let verdict = session.check_citation(theorem, clause);
        assert!(
            matches!(verdict, CitationVerdict::KernelStatementMatchCertified),
            "{theorem}: {verdict:?}"
        );
        proved += 1;
    }
    assert_eq!(proved, 2);
    assert!(session.check_import_island("theorem dependent : leaked = 7 := rfl").is_rejected());
}

#[test]
fn signed_computed_subtraction_uses_modular_bits_and_signed_order() {
    for width in [8, 16, 32, 64] {
        let pivot = 1u128 << (width - 1);
        let source = format!(
            r#"
            def subbits (a b : BitVec {width}) : BitVec {width} :=
                BitVec.ofNat {width} (Nat.sub (Nat.add (@BitVec.toNat {width} a) (Nat.pow 2 {width})) (@BitVec.toNat {width} b))
            def orderkey (a : BitVec {width}) : Nat := Nat.xor (@BitVec.toNat {width} a) {pivot}
            theorem exact_signed (cost limit held : BitVec {width}) :
                trust_import_crate__budget cost limit held = decide (Nat.le (orderkey cost) (orderkey (subbits limit held))) := rfl
        "#
        );
        eprintln!("TG14 signed subtraction: i{width}");
        let mut session = CleanIslandSession::new();
        admit(&mut session, budget(width, true, BinOp::Sub));
        eprintln!("TG14 signed i{width}: imported");
        let outcome = session.check_import_island(&source);
        eprintln!("TG14 signed i{width}: theorem checked");
        assert!(!outcome.is_rejected(), "i{width}: {outcome:?}");
        let mut mutant = CleanIslandSession::new();
        admit(&mut mutant, budget(width, true, BinOp::Add));
        eprintln!("TG14 signed i{width}: mutant imported");
        // A closed input distinguishes signed subtraction from addition:
        // 0 <= (0 - 1) is false, while 0 <= (0 + 1) is true. Use a real
        // counterexample instead of forcing open Nat.mod normalization while
        // rejecting a false extensional rfl proof.
        let counterexample = format!(
            "theorem signed_control : trust_import_crate__budget (BitVec.ofNat {width} 0) (BitVec.ofNat {width} 0) (BitVec.ofNat {width} 1) = Bool.false := rfl"
        );
        assert!(!session.check_import_island(&counterexample).is_rejected());
        assert!(mutant.check_import_island(&counterexample).is_rejected());
    }
}

#[test]
fn deferred_dependency_cycle_is_an_error_without_losing_prior_facts() {
    let mut session = CleanIslandSession::new();
    assert!(!session.check_import_island("theorem prior : (1 : Nat) = 1 := rfl").is_rejected());
    let cycle = session.check_import_island("def left : Nat := right\ndef right : Nat := left");
    assert!(cycle.is_rejected(), "a deferred cycle must remain a hard error: {cycle:?}");
    assert!(!session.is_tainted());
    assert!(
        session
            .environment()
            .unwrap()
            .get_const(&clean_kernel::Name::from_string("left"))
            .is_none()
    );
    assert!(matches!(
        session.check_citation("prior", "1 == 1"),
        CitationVerdict::KernelStatementMatchCertified
    ));
}

#[test]
fn refused_import_cannot_be_generalized_or_publish_partial_declarations() {
    let mut session = CleanIslandSession::new();
    let bare = session.check_import_island(
        "theorem counterfeit : trust_import_missing = trust_import_missing := rfl",
    );
    assert!(bare.is_rejected(), "missing imports cannot become implicit theorem parameters");
    assert!(
        bare.errors.iter().any(|error| error.message.contains("no checked E6 program admission"))
    );
    assert!(!session.is_tainted());
    admit(&mut session, budget(8, false, BinOp::Sub));
    let qualified = session.check_import_island("theorem counterfeit_qualified : Ghost.trust_import_crate__budget = Ghost.trust_import_crate__budget := rfl");
    assert!(qualified.is_rejected());
    assert!(
        session
            .environment()
            .unwrap()
            .get_const(&clean_kernel::Name::from_string("counterfeit_qualified"))
            .is_none()
    );
    assert!(!session.is_tainted());
    let root = session.check_import_island(
        "theorem root_control : _root_.trust_import_crate__budget 0 0 0 = Bool.true := rfl",
    );
    assert!(!root.is_rejected(), "an explicit root-qualified real import remains valid: {root:?}");

    let bad=session.check_import_island("def leaked : Nat := 7\ntheorem wrong : trust_import_crate__budget 0 0 0 = Bool.false := rfl");
    assert!(bad.is_rejected());
    assert!(!session.is_tainted());
    assert!(
        session
            .environment()
            .unwrap()
            .get_const(&clean_kernel::Name::from_string("leaked"))
            .is_none()
    );
    assert!(
        session
            .environment()
            .unwrap()
            .get_const(&clean_kernel::Name::from_string("wrong"))
            .is_none()
    );
}

fn checked_budget(width: u32, signed: bool, op: BinOp) -> VerifiableFunction {
    use trust_types::{ConstValue, Projection, VariantDef};
    let mut f = budget(width, signed, op);
    let scalar = Ty::Int { width, signed };
    let option = Ty::adt_enum_with_disc_safety(
        "core::option::Option",
        vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), scalar)] },
        ],
        true,
    );
    f.body.locals[4].ty = option;
    f.body.locals.push(LocalDecl { index: 5, ty: Ty::u64(), name: None });
    let cp = |i| Operand::Copy(Place::local(i));
    let asn = |i, rvalue| Statement::Assign {
        place: Place::local(i),
        rvalue,
        span: SourceSpan::default(),
    };
    let method = match op {
        BinOp::Add => "checked_add",
        BinOp::Sub => "checked_sub",
        BinOp::Mul => "checked_mul",
        _ => panic!("arithmetic"),
    };
    let marker = format!(
        "{}core::num::<impl {}{width}>::{method}",
        trust_types::TRUST_RUSTC_CHECKED_PRIMITIVE_METHOD_PATH_PREFIX,
        if signed { "i" } else { "u" }
    );
    f.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: marker,
                args: vec![cp(2), cp(3)],
                dest: Place::local(4),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: Default::default(),
                callee_identity: None,
                callee_key: None,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![asn(5, Rvalue::Discriminant(Place::local(4)))],
            terminator: Terminator::SwitchInt {
                discr: cp(5),
                targets: vec![(0, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![asn(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(false))))],
            terminator: Terminator::Return,
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![asn(
                0,
                Rvalue::BinaryOp(
                    BinOp::Le,
                    cp(1),
                    Operand::Copy(Place {
                        local: 4,
                        projections: vec![Projection::Downcast(1), Projection::Field(0)],
                    }),
                ),
            )],
            terminator: Terminator::Return,
        },
    ];
    f
}

#[test]
fn arithmetic_kernel_matches_rust_at_width_and_sign_boundaries() {
    use clean_kernel::{Expr, Name, TypeChecker};
    for width in [8, 16, 32, 64] {
        let modulus = 1u128 << width;
        let max = modulus - 1;
        let pivot = modulus / 2;
        for signed in [false, true] {
            for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
                for checked in [false, true] {
                    let mut session = CleanIslandSession::new();
                    let f = if checked {
                        checked_budget(width, signed, op)
                    } else {
                        budget(width, signed, op)
                    };
                    if checked {
                        assert!(
                            trust_types::facet_inference::infer_facets(&[f.clone()])[&f.def_path]
                                .all()
                        );
                    }
                    admit(&mut session, f);
                    let env = session.environment().unwrap();
                    let tc = TypeChecker::new(env);
                    let c = |name: &str| Expr::const_(Name::from_string(name), vec![]);
                    let literal = |bits: u128| {
                        if signed {
                            Expr::apps(
                                c("BitVec.ofNat"),
                                [Expr::nat_lit(width as u64), Expr::nat_lit(bits as u64)],
                            )
                        } else {
                            Expr::app(c(&format!("UInt{width}.ofNat")), Expr::nat_lit(bits as u64))
                        }
                    };
                    for (cost, l, r) in [
                        (0, 0, 1),
                        (0, max, 1),
                        (pivot, pivot, pivot),
                        (max, max, max),
                        (pivot, 0, pivot),
                        (1, 1, 0),
                        (0, pivot - 1, 1),
                        (0, pivot, max),
                    ] {
                        let expected = if signed {
                            let val = |bits: u128| {
                                if bits >= pivot {
                                    bits as i128 - modulus as i128
                                } else {
                                    bits as i128
                                }
                            };
                            let (cost, l, r) = (val(cost), val(l), val(r));
                            let exact = match op {
                                BinOp::Add => l + r,
                                BinOp::Sub => l - r,
                                BinOp::Mul => l * r,
                                _ => unreachable!(),
                            };
                            if checked {
                                (-(pivot as i128)..pivot as i128).contains(&exact) && cost <= exact
                            } else {
                                let bits = exact.rem_euclid(modulus as i128);
                                let wrapped = if bits >= pivot as i128 {
                                    bits - modulus as i128
                                } else {
                                    bits
                                };
                                cost <= wrapped
                            }
                        } else {
                            let exact = match op {
                                BinOp::Add => Some(l + r),
                                BinOp::Sub => l.checked_sub(r),
                                BinOp::Mul => Some(l * r),
                                _ => unreachable!(),
                            };
                            if checked {
                                exact.is_some_and(|value| value <= max && cost <= value)
                            } else {
                                let wrapped = match op {
                                    BinOp::Sub => l.wrapping_sub(r) & max,
                                    _ => exact.unwrap() & max,
                                };
                                cost <= wrapped
                            }
                        };
                        let actual = Expr::apps(
                            c("trust_import_crate__budget"),
                            [literal(cost), literal(l), literal(r)],
                        );
                        let wanted = c(if expected { "Bool.true" } else { "Bool.false" });
                        assert!(
                            tc.is_def_eq(&actual, &wanted),
                            "{width}/{signed}/{op:?}/checked={checked}: cost={cost},l={l},r={r}, expected={expected}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn actual_checked_sub_mir_imports_and_its_theorem_checks() {
    // Captured from the failed native run-make at 9cf0dda8e, unchanged. In
    // particular, the tag local is signed i64 and bb2 is the exhaustive
    // switch's Unreachable default; no synthetic MIR omits that edge.
    let f: VerifiableFunction =
        serde_json::from_str(include_str!("../../tests/fixtures/tg14/checked-u8.json")).unwrap();
    assert_eq!(f.def_path, "checked::checked_u8");
    assert!(
        trust_types::e6_expr::tree::checked_option_impossible_defaults(&f).contains(&BlockId(2))
    );
    let inferred = trust_types::facet_inference::infer_facets(&[f.clone()]);
    assert!(inferred[&f.def_path].all(), "{inferred:?}");
    let facets = trust_spec_elab::FacetTable::from_structural_facets([(
        "checked::checked_u8",
        true,
        true,
        true,
        true,
    )]);
    let mut session = CleanIslandSession::new();
    assert_eq!(session.admit_program_functions(&[f], &facets).len(), 1);
    let proof=session.check_import_island("theorem actual_exact (cost limit held : UInt8) : trust_import_checked__checked_u8 cost limit held = Bool.and (Bool.not (Nat.blt (UInt8.toNat limit) (UInt8.toNat held))) (decide (cost <= limit - held)) := rfl");
    assert!(!proof.is_rejected(), "{proof:?}");
}

#[test]
fn arithmetic_fact_hits_until_its_import_changes_and_refusals_store_nothing() {
    use std::sync::Arc;
    let home = crate::clean_fact::test_scratch("tg14-arithmetic-facts");
    let facts = Arc::new(crate::clean_fact::FactContext::for_tests(&home, "tg14", false));
    let source = "theorem exact_budget (cost limit held : UInt8) : trust_import_crate__budget cost limit held = decide (cost <= limit - held) := rfl";
    let compile = |op| {
        let mut session = CleanIslandSession::new();
        session.enable_facts(Arc::clone(&facts));
        admit(&mut session, budget(8, false, op));
        let outcome = session.check_import_island(source);
        (session, outcome)
    };
    let (_, cold) = compile(BinOp::Sub);
    assert!(!cold.is_rejected(), "{cold:?}");
    assert_eq!(facts.written(), 1);
    let (warm, good) = compile(BinOp::Sub);
    assert!(!good.is_rejected());
    assert_eq!(warm.keyed.elaborations, 0, "unchanged arithmetic theorem is a stored fact");
    for _ in 0..2 {
        let (mutant, bad) = compile(BinOp::Add);
        assert!(bad.is_rejected(), "changed imported body must invalidate the old fact");
        assert!(!mutant.is_tainted());
        assert_eq!(mutant.keyed.elaborations, 1, "refusals must not become cached facts");
        assert_eq!(facts.written(), 1, "a refused import writes no fact");
        assert!(mutant.env().get_const(&Name::from_string("exact_budget")).is_none());
    }
    let (restored, good) = compile(BinOp::Sub);
    assert!(!good.is_rejected());
    assert_eq!(restored.keyed.elaborations, 0, "refusal preserves the original valid fact");
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn refused_fact_transaction_preserves_three_independent_citations() {
    use std::sync::Arc;
    let home = crate::clean_fact::test_scratch("tg14-isolated-facts");
    let facts = Arc::new(crate::clean_fact::FactContext::for_tests(&home, "tg14", false));
    let sources = [
        "theorem prior : (1 : Nat) = 1 := rfl",
        "theorem middle : (2 : Nat) = 2 := rfl",
        "theorem later : (3 : Nat) = 3 := rfl",
    ];
    for refused in [false, true] {
        let mut session = CleanIslandSession::new();
        session.enable_facts(Arc::clone(&facts));
        admit(&mut session, budget(8, false, BinOp::Sub));
        for (index, source) in sources.iter().enumerate() {
            if refused && index == 2 {
                let before = facts.written();
                let bad = session.check_import_island("def leaked : Nat := 7\ntheorem wrong : trust_import_crate__budget 0 0 0 = Bool.false := rfl");
                assert!(bad.is_rejected());
                assert!(!session.is_tainted());
                assert_eq!(facts.written(), before);
                assert!(session.env().get_const(&Name::from_string("leaked")).is_none());
                let missing = session.check_import_island(
                    "theorem missing : trust_import_absent = trust_import_absent := rfl",
                );
                assert!(missing.is_rejected());
                assert_eq!(facts.written(), before);
            }
            let outcome = session.check_import_island(source);
            assert!(!outcome.is_rejected(), "{outcome:?}");
        }
        let mut proved = 0;
        for (name, clause) in [("prior", "1 == 1"), ("middle", "2 == 2"), ("later", "3 == 3")] {
            assert!(matches!(
                session.check_citation(name, clause),
                CitationVerdict::KernelStatementMatchCertified
            ));
            proved += 1;
        }
        assert_eq!(proved, 3);
        assert_eq!(facts.written(), 3, "a refusal cannot poison reuse of the following fact");
    }
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn a_disproved_fact_is_not_isolated_as_an_ordinary_import_refusal() {
    use std::sync::Arc;

    use crate::clean_fact::{StoreRead, encode};
    let home = crate::clean_fact::test_scratch("tg14-integrity-failure");
    let facts = Arc::new(crate::clean_fact::FactContext::for_tests(&home, "tg14", false));
    let source = "theorem prior : (1 : Nat) = 1 := rfl";
    let new_session = || {
        let mut session = CleanIslandSession::new();
        session.enable_facts(Arc::clone(&facts));
        session
    };
    assert!(!new_session().check_import_island(source).is_rejected());
    let key = facts.store().keys()[0];
    let StoreRead::Present { bytes, .. } = facts.store().get(&key) else { panic!("stored fact") };
    let mut fact = keyed_env::StoredFact::decode(&bytes).unwrap();
    let mut outcomes: (Vec<CleanIslandOutcome>, Vec<crate::clean_island_batch::CleanIslandCycle>) =
        crate::clean_fact::decode(&fact.outcome).unwrap();
    outcomes.0[0].registered.push("forged".into());
    fact.outcome = encode(&outcomes).unwrap();
    facts.store().put(&key, &encode(&fact).unwrap()).unwrap();
    let mut session = new_session();
    assert!(session.check_import_island(source).registered.contains(&"forged".into()));
    let rejected = session.check_import_island("theorem later : (2 : Nat) = 2 := rfl");
    assert!(rejected.is_rejected());
    assert!(session.is_tainted(), "replay integrity failure must invalidate earlier hits");
    assert!(!matches!(
        session.check_citation("prior", "1 == 1"),
        CitationVerdict::KernelStatementMatchCertified
    ));
    assert!(!matches!(facts.store().get(&key), StoreRead::Present { .. }), "quarantined");
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn stored_arithmetic_facts_cover_every_carrier_operation_and_checked_model() {
    use std::sync::Arc;
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
                for checked in [false, true] {
                    let tag = format!("tg14-cache-{width}-{signed}-{op:?}-{checked}");
                    let home = crate::clean_fact::test_scratch(&tag);
                    let facts =
                        Arc::new(crate::clean_fact::FactContext::for_tests(&home, "tg14", false));
                    let zero = if signed {
                        format!("(BitVec.ofNat {width} 0)")
                    } else {
                        format!("(UInt{width}.ofNat 0)")
                    };
                    let source = format!(
                        "theorem at_zero : trust_import_crate__budget {zero} {zero} {zero} = Bool.true := rfl"
                    );
                    for warm in [false, true] {
                        let mut session = CleanIslandSession::new();
                        session.enable_facts(Arc::clone(&facts));
                        let function = if checked {
                            checked_budget(width, signed, op)
                        } else {
                            budget(width, signed, op)
                        };
                        admit(&mut session, function);
                        let outcome = session.check_import_island(&source);
                        assert!(!outcome.is_rejected(), "{tag}/warm={warm}: {outcome:?}");
                        assert_eq!(facts.written(), 1, "{tag}");
                        if warm {
                            assert_eq!(
                                session.keyed.elaborations, 0,
                                "{tag}: unchanged fact must skip elaboration"
                            );
                            assert_eq!(
                                session.keyed.rebuilds, 0,
                                "{tag}: unchanged fact must skip replay"
                            );
                        }
                    }
                    let _ = std::fs::remove_dir_all(home);
                }
            }
        }
    }
}

#[test]
fn recovered_batch_preserves_forward_references_and_reuses_all_survivors() {
    use std::sync::Arc;
    let home = crate::clean_fact::test_scratch("tg14-forward-recovery");
    let facts = Arc::new(crate::clean_fact::FactContext::for_tests(&home, "tg14", false));
    for (index, bad) in [
        "def leaked : Nat := 7\ntheorem bad : trust_import_missing = trust_import_missing := rfl",
        "def leaked : Nat := 7\ntheorem bad : trust_import_missing = trust_import_missing := rfl",
        "def leaked : Nat := 7\ntheorem bad : trust_import_crate__budget 0 0 0 = Bool.false := rfl",
    ]
    .iter()
    .enumerate()
    {
        let mut session = CleanIslandSession::new();
        session.enable_facts(Arc::clone(&facts));
        admit(&mut session, budget(8, false, BinOp::Sub));
        let sources = [
            "def observed : Bool := trust_import_crate__budget 0 0 0\ntheorem forward : later = (1 : Nat) := rfl",
            *bad,
            "def later : Nat := 1",
            "theorem middle : (2 : Nat) = 2 := rfl",
            "theorem last : (3 : Nat) = 3 := rfl",
        ];
        let batch = session.check_import_islands(&sources);
        assert!(batch.is_rejected());
        assert_eq!(batch.refused_islands, [1]);
        assert!(!session.is_tainted());
        assert!(session.env().get_const(&Name::from_string("leaked")).is_none());
        for (name, clause) in [("forward", "1 == 1"), ("middle", "2 == 2"), ("last", "3 == 3")] {
            assert!(
                matches!(
                    session.check_citation(name, clause),
                    CitationVerdict::KernelStatementMatchCertified
                ),
                "{name}: {batch:?}"
            );
        }
        assert_eq!(facts.written(), 1, "only the accepted surviving batch is stored");
        if index == 1 {
            assert_eq!(session.keyed.elaborations, 0, "an unchanged recovery imports its fact");
            assert_eq!(session.keyed.rebuilds, 0);
        }
    }
    let _ = std::fs::remove_dir_all(home);
}

#[test]
fn a_declaration_into_the_import_namespace_is_a_policy_refusal_not_a_missing_admission() {
    // The deferred path must not read a name the island DECLARES as a
    // reference to a missing E6 admission: that would isolate the unit and
    // leave the session untainted, while the pre-walk batch refuses the same
    // source for naming the reserved namespace and taints.
    assert_eq!(
        island_kernel_import_declarations(
            "def trust_import_k__spec (a : UInt64) : UInt64 := a\n\
             theorem t : trust_import_k__spec 1 = trust_import_k__spec 1 := rfl"
        ),
        ["trust_import_k__spec"],
    );
    assert!(
        island_kernel_import_declarations(
            "theorem t : trust_import_k__f = trust_import_k__f := rfl"
        )
        .is_empty(),
        "a reference is not a declaration"
    );
    let mut session = CleanIslandSession::new();
    let batch = session.check_import_islands(&[
        "theorem prior : (1 : Nat) = 1 := rfl",
        "def trust_import_lookalike__spec (a b : UInt64) : UInt64 := a + b\n\
         theorem lookalike_self : forall (a b : UInt64),\n    \
         trust_import_lookalike__spec a b = trust_import_lookalike__spec a b := fun a b => rfl",
    ]);
    let errors = &batch.outcomes[1].errors;
    assert!(
        errors.iter().any(|e| e.message.contains(KERNEL_IMPORT_DECLARATION_REFUSAL)),
        "the reserved namespace must be named: {errors:?}"
    );
    assert!(
        !errors.iter().any(|e| e.message.contains("has no checked E6 program admission")),
        "a declared name is not a missing admission: {errors:?}"
    );
    assert!(session.is_tainted(), "a reserved-namespace declaration keeps the session tainted");
}

#[test]
fn recovery_rechecks_successes_against_the_complete_surviving_namespace() {
    let mut session = CleanIslandSession::new();
    let batch = session.check_import_islands(&[
        "namespace Imported\ndef pick : Nat := 1\nend Imported",
        "open Imported\nnamespace M\ndef early : Nat := pick\nend M",
        "theorem bad : trust_import_missing = trust_import_missing := rfl",
        "def M.pick : Nat := 2",
        "theorem selects_later : M.early = 2 := rfl",
    ]);
    assert_eq!(batch.refused_islands, [2]);
    assert!(!session.is_tainted());
    assert!(
        matches!(
            session.check_citation("selects_later", "2 == 2"),
            CitationVerdict::KernelStatementMatchCertified
        ),
        "{batch:?}"
    );
}

#[test]
fn cross_island_cycles_are_refused_without_losing_independent_proofs_or_source_inventory() {
    let sources = [
        "theorem prior : (1 : Nat) = 1 := rfl",
        "def cyc_a : Nat := cyc_b",
        "def cyc_b : Nat := cyc_a",
        "theorem later : (2 : Nat) = 2 := rfl",
    ];
    let mut session = CleanIslandSession::new();
    let (batch, census) = session.check_import_islands_with_census(&sources);
    assert!(batch.is_rejected());
    assert!(!batch.cycles.is_empty());
    assert_eq!(batch.refused_islands, [1, 2]);
    assert!(!session.is_tainted());
    for (name, clause) in [("prior", "1 == 1"), ("later", "2 == 2")] {
        assert!(matches!(
            session.check_citation(name, clause),
            CitationVerdict::KernelStatementMatchCertified
        ));
    }
    assert_eq!(census.report["inputs"].as_array().unwrap().len(), sources.len());
    assert_eq!(census.report["denominator_status"], "denominator_unverified");
    assert_eq!(census.report["source_declaration_metadata"], "unavailable-from-import-wrapper");
    assert_eq!(census.report["session_tainted"], false);
}

#[test]
fn a_global_recovery_failure_remains_tainted_and_visible_on_an_excluded_unit() {
    use std::sync::Arc;

    use crate::clean_fact::{StoreRead, encode};
    let home = crate::clean_fact::test_scratch("tg14-global-recovery-failure");
    let facts = Arc::new(crate::clean_fact::FactContext::for_tests(&home, "tg14", false));
    // TG6 stores no rejection (`TG6-FACTS-1` (9)), so the forged global
    // failure is planted on an accepted batch's fact: a hit must still taint
    // the session although the batch itself would be accepted.
    let accepted = "theorem true_claim : (0 : Nat) = 0 := rfl";
    let new_session = || {
        let mut session = CleanIslandSession::new();
        session.enable_facts(Arc::clone(&facts));
        session
    };
    assert!(!new_session().check_all(&["", accepted]).is_rejected());
    let key = facts.store().keys()[0];
    let StoreRead::Present { bytes, .. } = facts.store().get(&key) else { panic!("stored") };
    let mut fact = keyed_env::StoredFact::decode(&bytes).unwrap();
    let mut outcomes: (Vec<CleanIslandOutcome>, Vec<crate::clean_island_batch::CleanIslandCycle>) =
        crate::clean_fact::decode(&fact.outcome).unwrap();
    outcomes.0[0].errors.push(CleanIslandDiagnostic {
        start: 0,
        end: 0,
        message: format!(
            "{} test whole-environment refusal",
            crate::clean_island_batch::UNRECOVERABLE_BATCH_PREFIX
        ),
    });
    outcomes.0[1].errors.clear();
    fact.outcome = encode(&outcomes).unwrap();
    facts.store().put(&key, &encode(&fact).unwrap()).unwrap();
    let mut session = new_session();
    let batch = session.check_import_islands(&[
        "theorem absent : trust_import_missing = trust_import_missing := rfl",
        accepted,
    ]);
    assert!(session.is_tainted());
    assert!(
        batch.outcomes[0]
            .errors
            .iter()
            .any(|error| error.message.contains("no checked E6 program admission"))
    );
    assert!(
        batch.outcomes[0].errors.iter().any(|error| error
            .message
            .starts_with(crate::clean_island_batch::UNRECOVERABLE_BATCH_PREFIX)),
        "a preflight refusal must not hide a global integrity diagnostic"
    );
    let _ = std::fs::remove_dir_all(home);
}
