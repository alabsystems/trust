// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 18 — the PHASE-3 (sum-measure) emitter mutation battery.**
//!
//! `gcd_phase3_probes` p5 admits the two-argument `gcd`'s emission end to end.
//! An admit with no refused sibling is not a measurement, and this file is the
//! siblings: each row takes the MATERIALIZER's own emitted body for
//!
//! ```text
//! def gcdB (a b : Nat) : Nat :=
//!   if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a
//! termination_by a + 2*b
//! ```
//!
//! changes exactly ONE thing about it, and requires a refusal.
//!
//! The emitted body, dumped from the materializer (this is what every row below
//! mutates):
//!
//! ```text
//! bb0: _3 = &_2; is_zero(move _3) -> _4, bb1        -- the guard, on `b`
//! bb1: switchInt(_4) [0 -> bb3] otherwise bb2
//! bb2: _0 = move _1; goto bb9                       -- the zero arm, `a`
//! bb3: _5 = &_1; _6 = &_2; sub -> _7                -- a - b
//! bb4: _8 = &_2; _9 = &_1; sub -> _10               -- b - a
//! bb5: _11 = &_7; _12 = &_10; add -> _13            -- |a - b|
//! bb6: _14 = &_1; _15 = &_2; sub -> _16             -- a - b
//! bb7: _17 = &_1; _18 = &_16; sub -> _19            -- min a b
//! bb8: gcdB(move _13, move _19) -> _0, bb9
//! bb9: return
//! ```
//!
//! # THE FOUR ROWS THAT ONLY EXIST AT PHASE 3
//!
//! | row | what it changes | why it is only possible here |
//! |---|---|---|
//! | (a) | the self-call's two operands EXCHANGED | phase 2's first operand is the predecessor, structurally pinned; phase 3 has two ordinary values |
//! | (b) | the guard on the WRONG parameter | phase 2's guard is on the recursion variable, which the spine names; phase 3's is DISCOVERED |
//! | (c) | a wrong THREADED index inside one leg | needs a body that reads two parameters in one argument |
//! | (d) | the `|a-b|` / `min a b` legs' own operands transposed | needs non-commutative `-` inside a self-call argument |
//!
//! # EACH ROW IS PUT TO TWO LAYERS
//!
//! `admit_lowering` catches a mutation STRUCTURALLY (the emitted body reads back
//! as a different tree than the plan). That alone would not show the KERNEL
//! separates the two functions, so each semantic row is additionally reflected
//! with the recognizer removed and put straight to
//! `check_faithful_wf_functional` — the `control_17` discipline, at phase 3.
//!
//! # NOTHING HERE MAY BE REPAIRED BY EDITING A SIDE-B PRODUCER
//!
//! A row that stops refusing is a capability regression, not a test to update.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Name};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
    TemplateUnwind, body_template,
};
use trust_clean_origin::table::ladder_row;
use trust_clean_origin::{
    CleanOriginPlan, EmitRefusal, FaithfulnessMethod, WfLowering, admit_lowering,
    plan_clean_origin_body,
};
use trust_types::admissible_body::{
    PrimitiveCallee, RecBodyExpr, WfRecBody, recognize_wf_sum_measure_rec,
};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════════════════════════════════════════════════════════
// harness
// ═══════════════════════════════════════════════════════════════════════════

const GCDB: &str = "def gcdB (a b : Nat) : Nat := \
                    if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a\n\
                    termination_by a + 2*b";

const SELF_PATH: &str = "control18::gcdB";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";
const BIGNUM_MUL: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::mul";

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|outcome| outcome.errors.iter().map(|error| error.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|cycle| cycle.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn gcdb_env() -> Environment {
    island(GCDB).expect("the ratified two-argument `gcd` must elaborate at this pin")
}

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn extracted_callee_path(callee: PrimitiveCallee) -> String {
    match callee {
        PrimitiveCallee::NatSub => BIGNUM_SUB.to_owned(),
        PrimitiveCallee::NatAdd => BIGNUM_ADD.to_owned(),
        PrimitiveCallee::NatMul => BIGNUM_MUL.to_owned(),
        other => other.canonical_path(),
    }
}

fn render_operand(operand: TemplateOperand) -> Operand {
    match operand {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        TemplateOperand::ResultScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::U64Scalar(value) => {
            Operand::Constant(ConstValue::Uint(u128::from(value), 64))
        }
        TemplateOperand::UIntScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
    }
}

fn render(template: &BodyTemplate) -> VerifiableFunction {
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result | TemplateTy::Param { .. } => nat_adt(),
        TemplateTy::Bool => Ty::Bool,
        TemplateTy::RustCalleeResult { .. } => {
            panic!("W5: this probe plans no Rust-call chain; control_23 is that lane's measurement")
        }
        TemplateTy::ResultRef => Ty::Ref { mutable: false, inner: Box::new(nat_adt()) },
    };
    let locals = template
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| LocalDecl { index, ty: local_ty(local.ty), name: None })
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
                .map(|stmt| Statement::Assign {
                    place: Place::local(stmt.place),
                    rvalue: match stmt.rvalue {
                        TemplateRvalue::Use(operand) => Rvalue::Use(render_operand(operand)),
                        TemplateRvalue::SharedRef(of) => {
                            Rvalue::Ref { mutable: false, place: Place::local(of) }
                        }
                        _ => panic!("this lane emits only Use and SharedRef statements"),
                    },
                    span: SourceSpan::default(),
                })
                .collect(),
            terminator: match &block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                TemplateTerminator::Goto(target) => Terminator::Goto(BlockId(*target)),
                TemplateTerminator::SwitchIntZero { discr, zero, otherwise } => {
                    Terminator::SwitchInt {
                        discr: render_operand(*discr),
                        targets: vec![(0, BlockId(*zero))],
                        otherwise: BlockId(*otherwise),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    }
                }
                TemplateTerminator::Call { callee, args, dest, target, unwind } => {
                    Terminator::Call {
                        func: match callee {
                            TemplateCallee::Primitive(identity) => extracted_callee_path(*identity),
                            TemplateCallee::RustFn { .. } => panic!("W5: this probe plans no Rust-call chain; control_23 is that lane's measurement"),
                            TemplateCallee::SelfDef => SELF_PATH.to_owned(),
                        },
                        args: args.iter().map(|arg| render_operand(*arg)).collect(),
                        dest: Place::local(*dest),
                        target: Some(BlockId(*target)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: match unwind {
                            TemplateUnwind::Unreachable => UnwindEdge::Unreachable,
                            TemplateUnwind::Continue => UnwindEdge::Continue,
                        },
                        callee_identity: None,
                        callee_key: None,
                    }
                }
            },
        })
        .collect();
    VerifiableFunction {
        name: "gcdB".into(),
        def_path: SELF_PATH.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: nat_adt(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn plan_of(env: &Environment) -> CleanOriginPlan {
    plan_clean_origin_body(env, "gcdB").expect("`gcdB` must plan")
}

/// The MATERIALIZER's own body for the plan — never a hand-written one, so a
/// mutation is measured against the bytes the compiler would really emit.
fn emitted(env: &Environment) -> VerifiableFunction {
    let plan = plan_of(env);
    let row = ladder_row(plan.shape()).expect("its shape selects a ladder row");
    render(&body_template(row, &plan).expect("the materializer realizes it"))
}

fn mv(local: usize) -> Operand {
    Operand::Move(Place::local(local))
}

/// Replace one block's `Call` argument list.
fn with_args(mut body: VerifiableFunction, block: usize, args: Vec<Operand>) -> VerifiableFunction {
    if let Terminator::Call { args: slot, .. } = &mut body.body.blocks[block].terminator {
        *slot = args;
    } else {
        panic!("bb{block} is not a call");
    }
    body
}

/// Replace one block's `Call` callee.
fn with_callee(mut body: VerifiableFunction, block: usize, callee: &str) -> VerifiableFunction {
    if let Terminator::Call { func, .. } = &mut body.body.blocks[block].terminator {
        *func = callee.into();
    } else {
        panic!("bb{block} is not a call");
    }
    body
}

/// Re-target one block's `n`-th shared borrow: `_r = &_from` becomes
/// `_r = &_to`. This is how a body comes to read the WRONG PARAMETER while
/// staying perfectly well-formed MIR.
fn with_borrow(
    mut body: VerifiableFunction,
    block: usize,
    nth: usize,
    to: usize,
) -> VerifiableFunction {
    let mut seen = 0usize;
    for statement in &mut body.body.blocks[block].stmts {
        if let Statement::Assign { rvalue: Rvalue::Ref { place, .. }, .. } = statement {
            if seen == nth {
                *place = Place::local(to);
                return body;
            }
            seen += 1;
        }
    }
    panic!("bb{block} has no borrow #{nth}");
}

/// The KERNEL half, with the MIR recognizer removed: reflect a (possibly
/// mutated) READING straight into side B and put it to the gate. What this adds
/// over `admit_lowering` is that the refusal is the kernel's, not the structural
/// comparison's — so a row that passes here has shown the two FUNCTIONS differ,
/// not merely the two trees.
fn gate_side_b(env: &Environment, body: &WfRecBody) -> Result<(), String> {
    let reflected = trust_clean_origin::reflect_wf::reflect_wf_functional(
        env,
        "gcdB",
        body,
        WfLowering::OnMeasureValue,
    )
    .map_err(|detail| format!("reflection refused: {detail}"))?;
    trust_clean_origin::gate::check_faithful_wf_functional(
        env,
        "gcdB",
        &reflected,
        plan_of(env).result_carrier(),
    )
    .map(|_| ())
    .map_err(|refusal| format!("gate refused: {refusal:?}"))
}

/// `|a - b|` and `min a b`, as the reading the emitted body produces.
fn abs_diff() -> RecBodyExpr {
    RecBodyExpr::Add(
        Box::new(RecBodyExpr::Sub(
            Box::new(RecBodyExpr::Param(0)),
            Box::new(RecBodyExpr::Decreasing),
        )),
        Box::new(RecBodyExpr::Sub(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Param(0)),
        )),
    )
}

fn min_ab() -> RecBodyExpr {
    RecBodyExpr::Sub(
        Box::new(RecBodyExpr::Param(0)),
        Box::new(RecBodyExpr::Sub(
            Box::new(RecBodyExpr::Param(0)),
            Box::new(RecBodyExpr::Decreasing),
        )),
    )
}

fn honest_reading() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::Param(0),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![abs_diff(), min_ab()],
        measure_index: 1,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// THE ADMIT — the anchor every row below is a sibling of
// ═══════════════════════════════════════════════════════════════════════════

/// The unmutated emission ADMITS, and its reading is the one the rows mutate.
#[test]
fn control_18_the_unmutated_emission_admits() {
    let env = gcdb_env();
    let plan = plan_of(&env);
    let extracted = emitted(&env);

    assert_eq!(
        recognize_wf_sum_measure_rec(&extracted),
        Some(honest_reading()),
        "the emitted body must read back as the reading this file's mutations are stated against"
    );
    let faithful = admit_lowering(&env, &plan, &extracted).expect("the honest emission admits");
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);
    assert!(
        gate_side_b(&env, &honest_reading()).is_ok(),
        "…and so does the same reading reflected"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (a) THE SELF-CALL'S OPERANDS, EXCHANGED
// ═══════════════════════════════════════════════════════════════════════════

/// `gcdB(|a-b|, min a b)` emitted as `gcdB(min a b, |a-b|)`.
///
/// **This row cannot exist at phase 2.** There the self-call's first operand is
/// the emitted predecessor and is pinned structurally by
/// `check_wf_fragment`'s `Pred` belt; a swap would be caught before any kernel
/// question arose. Phase 3 has two ordinary values in those positions, so the
/// only thing that separates the two bodies is what they COMPUTE.
#[test]
fn control_18_a_swapped_self_call_operands_are_refused_at_both_layers() {
    let env = gcdb_env();
    let plan = plan_of(&env);

    let swapped = with_args(emitted(&env), 8, vec![mv(19), mv(13)]);
    let refusal = admit_lowering(&env, &plan, &swapped)
        .expect_err("exchanging the self-call's two operands must never emit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");

    // …AND THE KERNEL SEPARATES THEM. Without this the row would only show that
    // two trees differ.
    let detail =
        gate_side_b(&env, &WfRecBody { rec_args: vec![min_ab(), abs_diff()], ..honest_reading() })
            .expect_err("the kernel must refuse the exchanged legs");
    assert!(
        detail.contains("FunctionalDisagreement") || detail.contains("DecreaseSlotBorrowRefused"),
        "the swap must die at the defeq or at side A's borrowed decrease proof: {detail}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (b) THE GUARD ON THE WRONG PARAMETER
// ═══════════════════════════════════════════════════════════════════════════

/// The zero test decides `a == 0` where side A guards `0 < b`.
///
/// **This row is phase 3's alone.** At phase 2 the guarded parameter IS the
/// recursion variable, named by the `WellFounded.fix` spine itself, so the
/// reader knows which parameter to expect before it looks. At phase 3 the
/// recursion runs on the measure's VALUE and the guard is DISCOVERED from the
/// term — which is exactly the step that could silently pick the wrong one.
#[test]
fn control_18_b_a_guard_on_the_wrong_parameter_is_refused() {
    let env = gcdb_env();
    let plan = plan_of(&env);

    // bb0's only borrow is the one `is_zero` consumes: point it at `_1` (`a`).
    let wrong_guard = with_borrow(emitted(&env), 0, 0, 1);
    let refusal = admit_lowering(&env, &plan, &wrong_guard)
        .expect_err("a zero test on the wrong parameter must never emit");
    assert!(refusal.is_compiler_defect(), "{refusal:?}");

    // The KERNEL half: a reading whose guard sits on parameter 0 denotes a
    // different function, and side A's decrease proof does not reach it.
    // (`Decreasing` names the guarded parameter, so moving the guard renames
    // every leaf: the legs below are the SAME emitted terms re-read at
    // `measure_index: 0`.)
    // The KERNEL half. `Decreasing` names the GUARDED parameter, so moving the
    // guard renames every leaf: the reading below is the SAME emitted terms
    // (`|a-b|`, `min a b`, zero arm `a`) re-spelled at `measure_index: 0`. It is
    // a perfectly well-formed reading — the reflector renders it — and the gate
    // must refuse it, because side A's `dite` guards `b`.
    let detail = gate_side_b(
        &env,
        &WfRecBody {
            zero_value: RecBodyExpr::Decreasing,
            nonzero_value: RecBodyExpr::Rec,
            rec_args: vec![
                RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Decreasing),
                        Box::new(RecBodyExpr::Param(1)),
                    )),
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Param(1)),
                        Box::new(RecBodyExpr::Decreasing),
                    )),
                ),
                RecBodyExpr::Sub(
                    Box::new(RecBodyExpr::Decreasing),
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Decreasing),
                        Box::new(RecBodyExpr::Param(1)),
                    )),
                ),
            ],
            measure_index: 0,
        },
    )
    .expect_err("a guard on the other parameter must be refused at the kernel too");
    assert!(
        detail.starts_with("gate refused"),
        "this row must die at the GATE, not at the reflection — a producer refusal would only \
         show that side B's own spelling rules caught it: {detail}"
    );
    eprintln!("ROW 18(b) kernel | {}", detail.chars().take(160).collect::<String>());
}

// ═══════════════════════════════════════════════════════════════════════════
// (c) A WRONG THREADED INDEX
// ═══════════════════════════════════════════════════════════════════════════

/// `min a b = a - (a - b)` emitted as `b - (a - b)`.
///
/// One borrow re-targeted from `_1` to `_2` inside bb7 — a body that reads the
/// WRONG PARAMETER in a threaded position while remaining well-formed MIR at the
/// right arity. This is `control_16`'s wrong-threaded-index row, at the lowering
/// where the parameter binders sit at different indices.
#[test]
fn control_18_c_a_wrong_threaded_index_is_refused_at_both_layers() {
    let env = gcdb_env();
    let plan = plan_of(&env);

    let wrong = with_borrow(emitted(&env), 7, 0, 2);
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("reading `b` where the definition reads `a` must never emit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );

    let detail = gate_side_b(
        &env,
        &WfRecBody {
            rec_args: vec![
                abs_diff(),
                RecBodyExpr::Sub(
                    Box::new(RecBodyExpr::Decreasing),
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Param(0)),
                        Box::new(RecBodyExpr::Decreasing),
                    )),
                ),
            ],
            ..honest_reading()
        },
    )
    .expect_err("the kernel must refuse the wrong threaded parameter");
    eprintln!("ROW 18(c) kernel | {}", detail.chars().take(160).collect::<String>());
}

// ═══════════════════════════════════════════════════════════════════════════
// (d) THE LEGS' OWN OPERANDS TRANSPOSED
// ═══════════════════════════════════════════════════════════════════════════

/// `min a b = a - (a - b)` emitted as `(a - b) - a`, and `|a-b|` built the other
/// way round.
///
/// Truncated `-` is NOT commutative, so a transposed operand pair is a different
/// value — but both spellings are well-typed `Nat`s over the same two
/// parameters, so nothing but the kernel separates them. `(a-b)-a` is in fact
/// `0` for every input, which is why it is the sharpest row here: a body that
/// returned it would terminate, would type-check, and would be wrong.
#[test]
fn control_18_d_transposed_operands_inside_a_leg_are_refused_at_both_layers() {
    let env = gcdb_env();
    let plan = plan_of(&env);

    // bb7 computes `_17 - _18` where `_17 = &_1` and `_18 = &_16` (`a - b`).
    // Exchanging its two operands emits `(a - b) - a`.
    let transposed = with_args(
        with_borrow(with_borrow(emitted(&env), 7, 0, 16), 7, 1, 1),
        7,
        vec![mv(17), mv(18)],
    );
    let refusal = admit_lowering(&env, &plan, &transposed)
        .expect_err("transposing a truncated subtraction's operands must never emit");
    assert!(refusal.is_compiler_defect(), "{refusal:?}");

    let detail = gate_side_b(
        &env,
        &WfRecBody {
            rec_args: vec![
                abs_diff(),
                RecBodyExpr::Sub(
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Param(0)),
                        Box::new(RecBodyExpr::Decreasing),
                    )),
                    Box::new(RecBodyExpr::Param(0)),
                ),
            ],
            ..honest_reading()
        },
    )
    .expect_err("the kernel must refuse `(a-b)-a` where side A says `a-(a-b)`");
    eprintln!("ROW 18(d) kernel | {}", detail.chars().take(160).collect::<String>());

    // …and the `|a-b|` leg's two summands exchanged, which at `Nat` is a
    // DIFFERENT term (`+` is commutative propositionally, never definitionally
    // at open arguments) — so this row measures the defeq and not a syntax
    // check that would also reject a correct body.
    let detail = gate_side_b(
        &env,
        &WfRecBody {
            rec_args: vec![
                RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Decreasing),
                        Box::new(RecBodyExpr::Param(0)),
                    )),
                    Box::new(RecBodyExpr::Sub(
                        Box::new(RecBodyExpr::Param(0)),
                        Box::new(RecBodyExpr::Decreasing),
                    )),
                ),
                min_ab(),
            ],
            ..honest_reading()
        },
    )
    .expect_err("`(b-a)+(a-b)` is not `(a-b)+(b-a)` definitionally");
    eprintln!("ROW 18(d2) kernel | {}", detail.chars().take(160).collect::<String>());
}

// ═══════════════════════════════════════════════════════════════════════════
// (e) THE WRONG OPERATOR
// ═══════════════════════════════════════════════════════════════════════════

/// `add` and `mul` where the definition says `sub`, and `mul` where it says
/// `add`. The `nat.sub`/`nat.add`/`nat.mul` rows' emitter-side twins.
#[test]
fn control_18_e_a_wrong_operator_is_refused() {
    let env = gcdb_env();
    let plan = plan_of(&env);
    for (block, callee, what) in [
        (3, BIGNUM_ADD, "add for sub"),
        (3, BIGNUM_MUL, "mul for sub"),
        (5, BIGNUM_MUL, "mul for add"),
        (7, BIGNUM_ADD, "add for sub"),
    ] {
        let refusal = admit_lowering(&env, &plan, &with_callee(emitted(&env), block, callee))
            .expect_err("a wrong bignum callee must never emit");
        assert!(
            matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
            "{what} at bb{block}: expected the structural catch, got {refusal:?}"
        );
        assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (f) THE WRONG TELESCOPE
// ═══════════════════════════════════════════════════════════════════════════

/// Reflecting a phase-3 body at PHASE 2's telescope is refused.
///
/// This is the row that says the `lowering` parameter of
/// `reflect_wf_functional` is checked and not merely carried: side B rendered at
/// the wrong telescope binds three binders where side A binds five, and the
/// gate's `peel_functional` refuses on the count rather than reading the body at
/// whatever layout it happens to have.
#[test]
fn control_18_f_the_phase2_telescope_against_a_phase3_side_a_is_refused() {
    let env = gcdb_env();
    let reflected = trust_clean_origin::reflect_wf::reflect_wf_functional(
        &env,
        "gcdB",
        &honest_reading(),
        WfLowering::OnParameter,
    )
    .expect("the phase-2 rendering is a term; it is simply the wrong one");
    let refusal = trust_clean_origin::gate::check_faithful_wf_functional(
        &env,
        "gcdB",
        &reflected,
        plan_of(&env).result_carrier(),
    )
    .err()
    .expect("a phase-2 telescope must not admit against a phase-3 declaration");
    let rendered = format!("{refusal:?}");
    assert!(
        rendered.contains("binder")
            || rendered.contains("recursive slot")
            || rendered.contains("author the measure"),
        "the refusal must be about the telescope: {rendered}"
    );
}
