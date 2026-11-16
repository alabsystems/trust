// Unit pins for counterexample grounding. The real-MIR cover — the deployed
// backend pair on this tree's own stage1 extraction — is
// `tests/counterexample_grounding_realmir.rs`; these pin the arithmetic and the
// fail-closed edges a fixture cannot isolate.

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Counterexample, CounterexampleValue,
    LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::*;

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn local(index: usize, name: Option<&str>, ty: Ty) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(str::to_string) }
}

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: span() }
}

/// `fn f(a: i64, b: i64) -> i64 { let lim = (-1i32) as u32 as i64; ... a * b ... }`,
/// reduced to what grounding reads: the two casts that define `lim` in the entry
/// block, and an `Assert` so the dominance condition has something to dominate.
fn castu_func() -> VerifiableFunction {
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                // _4 = (-1i32) as u32
                assign(4, Rvalue::Cast(Operand::Constant(ConstValue::Int(-1)), u32_ty())),
                // lim = _4 as i64
                assign(3, Rvalue::Cast(Operand::Copy(Place::local(4)), i64_ty())),
                // _5 = CheckedMul(a, b)
                assign(
                    5,
                    Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                ),
            ],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Move(Place { local: 5, projections: vec![Projection::Field(1)] }),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Mul),
                target: BlockId(1),
                span: span(),
            },
        },
        BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "castu_unminable".to_string(),
        def_path: "p::castu_unminable".to_string(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                local(0, None, i64_ty()),
                local(1, Some("a"), i64_ty()),
                local(2, Some("b"), i64_ty()),
                local(3, Some("lim"), i64_ty()),
                local(4, None, u32_ty()),
                local(5, None, Ty::Tuple(vec![i64_ty(), Ty::Bool])),
            ],
            blocks,
            arg_count: 2,
            return_ty: i64_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn cex(pairs: &[(&str, CounterexampleValue)]) -> Counterexample {
    Counterexample::new(
        pairs.iter().map(|(n, v)| ((*n).to_string(), v.clone())).collect::<Vec<_>>(),
    )
}

// ---------------------------------------------------------------------------
// The machine cast — the one arm this module computes that the miner refuses.
// ---------------------------------------------------------------------------

/// Rust's own `as`, on the table that matters. A wrong answer here would
/// MISLABEL a real witness, so the oracle is the language, not a restatement.
#[test]
fn machine_cast_matches_rust_as() {
    assert_eq!(machine_cast_int(-1, 32, false), Some(i128::from((-1i32) as u32)));
    assert_eq!(
        machine_cast_int(4_294_967_295, 64, true),
        Some(i128::from(4_294_967_295u32 as i64))
    );
    assert_eq!(machine_cast_int(1i128 << 63, 64, true), Some(i128::from((1u64 << 63) as i64)));
    assert_eq!(machine_cast_int(255, 8, true), Some(i128::from(255u8 as i8)));
    assert_eq!(machine_cast_int(-1, 8, false), Some(i128::from((-1i8) as u8)));
    assert_eq!(machine_cast_int(300, 8, false), Some(i128::from(300u32 as u8)));
    assert_eq!(machine_cast_int(-129, 8, true), Some(i128::from((-129i32) as i8)));
    assert_eq!(machine_cast_int(i128::MIN, 128, true), Some(i128::MIN));
    // 128-bit UNSIGNED declines rather than guess: a u128 bit pattern does not
    // fit the i128 this module carries values in.
    assert_eq!(machine_cast_int(1, 128, false), None);
    assert_eq!(machine_cast_int(1, 0, true), None);
    assert_eq!(machine_cast_int(1, 129, true), None);
}

/// A model names a BITVECTOR by its unsigned bit pattern, and at 128 bits that
/// pattern does not fit `i128`: `i128::MIN` is spelled
/// `170141183460469231731687303715884105728`. Narrowing before reinterpreting
/// DROPS such a value, and a dropped value is a missing check — measured: it
/// cost `unfolded_neg_bound_realmir`'s 128-bit negation twin its repaired
/// witness, so this is a pin on a regression that actually happened.
#[test]
fn a_model_bitvector_is_read_as_a_bit_pattern_at_every_width() {
    let i128_ty = Ty::Int { width: 128, signed: true };
    let i64 = i64_ty();
    assert_eq!(
        model_int(&CounterexampleValue::Uint(1u128 << 127), Some(&i128_ty)),
        Some(i128::MIN),
        "the 128-bit sign bit IS i128::MIN"
    );
    assert_eq!(
        model_int(&CounterexampleValue::Uint(u128::from(u64::MAX)), Some(&i64)),
        Some(-1),
        "all-ones at 64 bits IS -1i64"
    );
    assert_eq!(
        model_int(&CounterexampleValue::Uint(1u128 << 63), Some(&i64)),
        Some(i128::from(i64::MIN))
    );
    assert_eq!(
        model_int(&CounterexampleValue::Uint(255), Some(&u32_ty())),
        Some(255),
        "an unsigned type reads its pattern as itself"
    );
    assert_eq!(model_int(&CounterexampleValue::Int(-1), Some(&i64)), Some(-1));
    assert_eq!(model_int(&CounterexampleValue::Bool(true), None), Some(1));
}

/// The DIVIDING LINE between this module and `const_expr`, stated as a
/// measurement rather than as prose.
///
/// AMENDED 2026-09-21. It used to run the other way: the miner DECLINED
/// `(-1i32) as u32` and this module resolved it, and the test said that if the
/// two ever agreed one of them would be wrong. That was the wrong reading of
/// why the miner declined. A reinterpreting `as` between integer types is
/// exactly computable, so `lim == 4294967295` is a TRUE hypothesis and always
/// was; the miner declined it only because its `Cast` arm did not model the
/// reinterpretation. `const_expr::v2_const_expr_cast_int` now does, so on THIS
/// shape the two folds agree — and that agreement is the fix, because a mined
/// bound is what gives the row a bound to be witnessed against at all.
///
/// The line has not disappeared, it has moved to where it always belonged: the
/// miner is exact-or-nothing about the DESTINATION LOCAL's value, and this
/// module computes what the machine does for a local a MODEL names. The two
/// shapes below are where they still separate — a `u128` bit pattern the miner
/// carries and this module declines, and the widths neither admits.
#[test]
fn grounding_and_the_miner_agree_on_the_cast_that_used_to_be_unminable() {
    let func = castu_func();
    let lim = Operand::Copy(Place::local(3));
    assert_eq!(
        crate::const_expr::v2_const_expr_operand_int(
            &func,
            &lim,
            crate::const_expr::V2_CONST_EXPR_FUEL
        ),
        Some(4_294_967_295),
        "the miner now models the reinterpretation: `(-1i32) as u32 as i64` IS 4294967295, \
         and a bound it can state is a bound the row can be witnessed against"
    );
    assert_eq!(
        machine_const_operand_int(&func, &lim, crate::const_expr::V2_CONST_EXPR_FUEL),
        Some(4_294_967_295),
        "grounding asks what the machine computes, and gets the same answer"
    );
    // WHERE THEY STILL SEPARATE. This module declines EVERY 128-bit unsigned
    // destination (its values are read back from models as bit patterns, so it
    // will not narrow one); the miner carries a non-negative `u128` value it can
    // hold in an `i128`. Neither admits a width Rust does not have.
    assert_eq!(machine_cast_int(7, 128, false), None);
    assert_eq!(
        crate::const_expr::v2_const_expr_cast_int(7, &Ty::Int { width: 128, signed: false }),
        Some(7)
    );
    assert_eq!(machine_cast_int(1, 129, true), None);
    assert_eq!(
        crate::const_expr::v2_const_expr_cast_int(1, &Ty::Int { width: 129, signed: true }),
        None
    );
}

// ---------------------------------------------------------------------------
// The two checks
// ---------------------------------------------------------------------------

/// THE REPORT. `lim` is 4294967295 by the function's own entry-block
/// definition; a model naming `lim = 1` is not an execution of it.
#[test]
fn a_defined_local_contradicted_by_the_model_is_ungrounded() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(0)),
        ("b", CounterexampleValue::Int(0)),
        ("lim", CounterexampleValue::Int(1)),
    ]);
    let WitnessGrounding::Ungrounded { reasons } = ground_counterexample(&func, &model) else {
        panic!("`lim = 1` contradicts `let lim = (-1i32) as u32 as i64`");
    };
    assert_eq!(reasons.len(), 1, "{reasons:?}");
    assert!(reasons[0].contains("`lim` = 1"), "{reasons:?}");
    assert!(reasons[0].contains("4294967295"), "{reasons:?}");
}

/// The model agreeing with the definition is left alone — the check must not
/// pass by refusing every witness.
#[test]
fn a_defined_local_the_model_gets_right_is_grounded() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(4_294_967_294)),
        ("b", CounterexampleValue::Int(4_294_967_294)),
        ("lim", CounterexampleValue::Int(4_294_967_295)),
    ]);
    // And this one replays: 4294967294 * 4294967294 really does overflow i64,
    // so the REPLAY — not merely the absence of a contradiction — grounds it.
    assert_eq!(ground_counterexample(&func, &model), WitnessGrounding::Replays { block: 0 });
}

/// The SECOND check, which needs no definition at all: the fresh bitvector
/// variable standing for `a` and the model's own `a` must be the same value.
/// A model names a bitvector by its UNSIGNED bit pattern, so the comparison is
/// at `a`'s width — `18446744073709551615` IS `-1i64`, not a huge positive.
#[test]
fn a_bitvector_operand_disagreeing_with_its_source_name_is_ungrounded() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(0)),
        ("__trust_ovf_bv_lhs_a", CounterexampleValue::Uint(u128::from(u64::MAX))),
    ]);
    let WitnessGrounding::Ungrounded { reasons } = ground_counterexample(&func, &model) else {
        panic!("`__trust_ovf_bv_lhs_a = -1` beside `a = 0` is one value with two answers");
    };
    assert_eq!(reasons.len(), 1, "{reasons:?}");
    assert!(reasons[0].contains("__trust_ovf_bv_lhs_a` = -1"), "{reasons:?}");
    assert!(reasons[0].contains("`a` = 0"), "{reasons:?}");
}

/// And the same pair AGREEING is grounded — the bit-pattern reading is what
/// makes that true, so this is also the anti-vacuity pin for `model_int`.
#[test]
fn a_bitvector_operand_agreeing_with_its_source_name_is_grounded() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(-1)),
        ("b", CounterexampleValue::Int(i128::from(i64::MIN))),
        ("__trust_ovf_bv_lhs_a", CounterexampleValue::Uint(u128::from(u64::MAX))),
    ]);
    // `-1 * i64::MIN` overflows, so this one also REPLAYS to the panic.
    assert_eq!(ground_counterexample(&func, &model), WitnessGrounding::Replays { block: 0 });
}

/// FAIL CLOSED TOWARD KEEPING THE WITNESS: a local whose definition is NOT in a
/// block dominating the function's asserts is uninitialized on the paths that
/// skip it, so the model may name anything for it and a mismatch proves nothing.
#[test]
fn a_conditionally_defined_local_is_never_called_a_contradiction() {
    let mut func = castu_func();
    // Move `lim`'s two defining statements into a block that does NOT dominate
    // the assert block, leaving everything else identical.
    let moved: Vec<Statement> = func.body.blocks[0].stmts.drain(0..2).collect();
    func.body.blocks[1].stmts = moved;
    let model = cex(&[("lim", CounterexampleValue::Int(1))]);
    assert!(
        ground_counterexample(&func, &model).is_grounded(),
        "a definition that may not have run cannot contradict the model"
    );
}

/// A name no local owns — and a bitvector operand whose `{base}` no local owns —
/// are not grounded against anything.
#[test]
fn a_name_this_function_does_not_own_is_left_alone() {
    let func = castu_func();
    let model = cex(&[
        ("__precond_0", CounterexampleValue::Int(7)),
        ("__trust_ovf_bv_lhs_nosuchlocal", CounterexampleValue::Int(7)),
    ]);
    // Undecided, not Ungrounded: no parameter is bound, so there is nothing to
    // replay and nothing to hold against the model.
    assert!(ground_counterexample(&func, &model).is_grounded());
}

#[test]
fn the_bv_operand_name_split_is_exact() {
    assert_eq!(split_bv_operand_name("__trust_ovf_bv_lhs_a"), Some(("lhs", "a")));
    assert_eq!(split_bv_operand_name("__trust_ovf_bv_rhs__15"), Some(("rhs", "_15")));
    assert_eq!(split_bv_operand_name("__trust_ovf_bv_neg_x"), Some(("neg", "x")));
    assert_eq!(split_bv_operand_name("__trust_ovf_bv_amt__6"), Some(("amt", "_6")));
    // Not a role, and not the prefix.
    assert_eq!(split_bv_operand_name("__trust_ovf_bv_zzz_a"), None);
    assert_eq!(split_bv_operand_name("a"), None);
}

// ---------------------------------------------------------------------------
// Delivery
// ---------------------------------------------------------------------------

/// An ungrounded row delivers the LABEL and the contradiction, never the
/// impossible assignment — and the reason names its fix (v7/D3).
#[test]
fn an_ungrounded_witness_is_delivered_as_a_label_not_as_an_assignment() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(0)),
        ("b", CounterexampleValue::Int(0)),
        ("lim", CounterexampleValue::Int(1)),
        ("__trust_ovf_bv_lhs_a", CounterexampleValue::Uint(u128::from(u64::MAX))),
    ]);
    let delivered = deliver_counterexample(&func, &model);
    assert_eq!(delivered.assignments.len(), 1);
    assert_eq!(delivered.assignments[0].0, UNGROUNDED_LABEL);
    let rendered = delivered.to_string();
    for needle in ["lim", "4294967295", "not an execution", "REFUTATION stands", "FIX:"] {
        assert!(rendered.contains(needle), "the label must say `{needle}`: {rendered}");
    }
    // And the values the program refutes must not survive anywhere as an
    // assignment a reader could take for an input.
    assert!(
        !delivered.assignments.iter().any(|(name, _)| name == "lim" || name == "a"),
        "an impossible assignment must not be delivered: {delivered:?}"
    );
}

/// `castu_func` with a GUARD whose bound does not fold: `fn f(a, b, lim) { if a > -lim
/// { a * b } }` — `_6 = Neg(copy lim)` is computed from an INPUT, so no closed constant
/// exists, the guard mines no fact and the row's operands carry no bound.
fn unminable_guard_func() -> VerifiableFunction {
    let mut func = castu_func();
    func.body.arg_count = 3;
    func.body.locals.push(local(6, None, i64_ty()));
    func.body.locals.push(local(7, None, Ty::Bool));
    // bb0: _6 = Neg(copy lim); _7 = Gt(copy a, copy _6); switchInt(_7) [0: bb1] -> bb2
    // bb2: castu_func's multiply and its assert -> bb1
    let mut multiply = func.body.blocks[0].clone();
    multiply.id = BlockId(2);
    multiply.stmts.retain(|s| matches!(s, Statement::Assign { place, .. } if place.local == 5));
    func.body.blocks[0] = BasicBlock {
        id: BlockId(0),
        stmts: vec![
            assign(6, Rvalue::UnaryOp(trust_types::UnOp::Neg, Operand::Copy(Place::local(3)))),
            assign(
                7,
                Rvalue::BinaryOp(
                    BinOp::Gt,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(6)),
                ),
            ),
        ],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(7)),
            targets: vec![(0, BlockId(1))],
            otherwise: BlockId(2),
            exhaustive_enum_unreachable: false,
            span: span(),
        },
    };
    func.body.blocks.push(multiply);
    func
}

/// Trust (2026-10-01, review of cf9ce551b45): the respelling advice is given only where
/// a guard bound really was left unmined, and then it names that bound; where every
/// bound folds, the label says the refutation stands and names the operand instead.
#[test]
fn the_fix_advice_names_the_unmined_bound_and_only_then_respelling() {
    let model = cex(&[
        ("a", CounterexampleValue::Int(0)),
        ("b", CounterexampleValue::Int(0)),
        ("__trust_ovf_bv_lhs_a", CounterexampleValue::Uint(u128::from(u64::MAX))),
    ]);

    let unmined = unminable_guard_func();
    assert_eq!(crate::generate::unmined_guard_bounds(&unmined), vec!["_6".to_string()]);
    let rendered = deliver_counterexample(&unmined, &model).to_string();
    for needle in ["spell the bound", "`_6`", "FIX:", "REFUTATION stands"] {
        assert!(rendered.contains(needle), "an unmined bound's label says `{needle}`: {rendered}");
    }

    // No guard at all, so nothing was left unmined: the label must not send the reader
    // after a spelling.
    let mined = castu_func();
    assert!(crate::generate::unmined_guard_bounds(&mined).is_empty());
    let rendered = deliver_counterexample(&mined, &model).to_string();
    assert!(!rendered.contains("spell the bound"), "no bound to respell: {rendered}");
    for needle in ["the lhs operand `a`", "stands on its own", "FIX:"] {
        assert!(rendered.contains(needle), "the label says `{needle}`: {rendered}");
    }
}

/// A grounded row keeps its model, with the encoding's fresh bitvector variable
/// PROJECTED onto the source name it stands for — a witness names the program's
/// variables, not the encoding's.
#[test]
fn a_grounded_witness_projects_its_bitvector_operands_onto_the_source_names() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(-1)),
        ("b", CounterexampleValue::Int(i128::from(i64::MIN))),
        ("lim", CounterexampleValue::Int(4_294_967_295)),
        ("__trust_ovf_bv_rhs_b", CounterexampleValue::Uint(1u128 << 63)),
    ]);
    let delivered = deliver_counterexample(&func, &model);
    assert!(
        delivered.assignments.contains(&("a".to_string(), CounterexampleValue::Int(-1))),
        "the source binding survives: {delivered:?}"
    );
    assert!(
        !delivered.assignments.iter().any(|(name, _)| name.starts_with(BV_OPERAND_PREFIX)),
        "and the encoding's own name must not be delivered: {delivered:?}"
    );
    assert!(
        delivered
            .assignments
            .contains(&("lim".to_string(), CounterexampleValue::Int(4_294_967_295)))
    );
}

/// When the model already binds the source name (consistently — grounding has
/// established that), the bitvector twin is redundant and is dropped rather than
/// printed twice.
#[test]
fn a_projected_operand_does_not_duplicate_a_source_binding_the_model_already_has() {
    let func = castu_func();
    let model = cex(&[
        ("a", CounterexampleValue::Int(-1)),
        ("b", CounterexampleValue::Int(i128::from(i64::MIN))),
        ("__trust_ovf_bv_lhs_a", CounterexampleValue::Uint(u128::from(u64::MAX))),
    ]);
    let delivered = deliver_counterexample(&func, &model);
    assert_eq!(
        delivered.assignments,
        vec![
            ("a".to_string(), CounterexampleValue::Int(-1)),
            ("b".to_string(), CounterexampleValue::Int(i128::from(i64::MIN))),
        ],
        "one binding for one program value: {delivered:?}"
    );
}

/// Grounding touches the WITNESS and never the VERDICT — the whole point of
/// choosing (b) over making the row `Unknown`.
#[test]
fn grounding_never_moves_a_verdict() {
    let func = castu_func();
    let vc = trust_types::VerificationCondition {
        kind: trust_types::VcKind::ArithmeticOverflow {
            op: trust_types::BinOp::Mul,
            operand_tys: (i64_ty(), i64_ty()),
        },
        function: "castu_unminable".into(),
        location: span(),
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    };
    let failed = trust_types::VerificationResult::Failed {
        solver: "ay-in-process".into(),
        time_ms: 1,
        counterexample: Some(cex(&[("lim", CounterexampleValue::Int(1))])),
    };
    let proved = trust_types::VerificationResult::Proved {
        solver: "interval".into(),
        time_ms: 1,
        strength: trust_types::ProofStrength::smt_unsat(),
        proof_certificate: None,
        native_proof_envelope: None,
        solver_warnings: None,
    };
    let before = format!("{proved:?}");
    let mut results = vec![(vc.clone(), failed), (vc, proved)];
    ground_delivered_counterexamples(&func, &mut results);
    let trust_types::VerificationResult::Failed { solver, time_ms, counterexample } = &results[0].1
    else {
        panic!("the refutation must survive grounding");
    };
    assert_eq!((solver.as_str(), *time_ms), ("ay-in-process", 1));
    assert_eq!(counterexample.as_ref().unwrap().assignments[0].0, UNGROUNDED_LABEL);
    assert_eq!(format!("{:?}", results[1].1), before, "a non-Failed row is byte-identical");
}

fn i32_ty() -> Ty {
    Ty::Int { width: 32, signed: true }
}

/// r07's body exactly as rustc lowers it (`tests/two-language-programs/
/// r07_rust_contract_refuted_strict/lib.rs`, `fn double(x: i32) -> i32 { x * 2 }`):
///
/// ```text
/// bb0: _2 = MulWithOverflow(copy _1, const 2_i32);
///      assert(!move (_2.1: bool), …overflow) -> bb1
/// bb1: _0 = move (_2.0: i32);
///      return;
/// ```
fn r07_double_func() -> VerifiableFunction {
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                2,
                Rvalue::CheckedBinaryOp(
                    BinOp::Mul,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(2)),
                ),
            )],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Move(Place { local: 2, projections: vec![Projection::Field(1)] }),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Mul),
                target: BlockId(1),
                span: span(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                0,
                Rvalue::Use(Operand::Move(Place {
                    local: 2,
                    projections: vec![Projection::Field(0)],
                })),
            )],
            terminator: Terminator::Return,
        },
    ];
    VerifiableFunction {
        name: "double".to_string(),
        def_path: "lib::double".to_string(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                local(0, None, i32_ty()),
                local(1, Some("x"), i32_ty()),
                local(2, None, Ty::Tuple(vec![i32_ty(), Ty::Bool])),
            ],
            blocks,
            arg_count: 1,
            return_ty: i32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `DECISION_QUEUE.md` D92 (D11 before the 2026-10-14 merge) option (b′), measured rather than argued: replaying r07's
/// counterexample `x = 1` through its own MIR reaches `Return` with `_0 = 2`, so
/// `ensures result == x * 3` is FALSE on an execution the function really performs.
/// This pins only that the replay can SEE the return value. It deliberately does not
/// wire that into any verdict — admitting a postcondition refutation this way is the
/// open decision.
#[test]
fn replay_carries_the_return_value_a_postcondition_check_needs() {
    let func = r07_double_func();
    let mut params = trust_types::fx::FxHashMap::default();
    params.insert(1, Value::Int(1));
    let replayed = replay(&func, &params);
    assert_eq!(replayed, Replay::Completes { ret: Some(Value::Int(2)) });

    let Replay::Completes { ret: Some(Value::Int(ret)) } = replayed else {
        unreachable!("asserted just above");
    };
    let x = 1i128;
    assert_ne!(ret, x * 3, "r07's `ensures result == x * 3` must be violated on x = 1");
}

/// CONTROL: a replay that runs to `Return` without ever writing `_0` reports
/// `ret: None`, never a fabricated value. `castu_func` has no `_0` assignment;
/// `a = 0, b = 0` does not overflow, so it completes.
#[test]
fn replay_reports_no_return_value_when_the_return_place_is_never_written() {
    let func = castu_func();
    let mut params = trust_types::fx::FxHashMap::default();
    params.insert(1, Value::Int(0));
    params.insert(2, Value::Int(0));
    assert_eq!(replay(&func, &params), Replay::Completes { ret: None });
}
