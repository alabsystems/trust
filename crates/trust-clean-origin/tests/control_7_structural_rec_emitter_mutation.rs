// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 7 (structural recursion) — the R1 mutation battery for the
//! per-defining-equation lane (§6e AS AMENDED).**
//!
//! The fast-lane end-to-end: side A is the measured island output for the
//! equation-form `tozero` (`recursion_boundary_probes` r3 spelling), side B
//! is the emitted-MIR contract hand-built exactly as
//! `compiler/rustc_mir_transform/src/clean_origin_mir.rs`'s
//! `build_structural_rec_body` emits it, routed through the REAL producers:
//! `plan_clean_origin_body` → `admit_lowering` →
//! `recognize_structural_rec` → `reflect_rec::reflect_structural_rec` →
//! `check_faithful_equations`.
//!
//! Every mutation the task named is here, each refused AT THE LAYER THE
//! PROBES MEASURED (`r1_equation_probes` s2–s8):
//!
//! * **wrong-case value** — structural (`LoweringShapeMismatch`) AND,
//!   smuggled past the structural check, kernel
//!   (`EquationDisagreement { case: "Nat.zero" }`, probe s3);
//! * **swapped cases** — the recognizer's contract refuses
//!   (`LoweringUnrecognised`; the self-call has no zero-arm reading);
//! * **off-by-one recursive argument** — structural AND, smuggled straight
//!   past the recognizer by constructing the reflection with
//!   `rec_arg: Decreasing`, refused at the KERNEL layer
//!   (`RecursionStructureDisagreement`, probe s4's divergence catch — the
//!   control that proves the catch is not merely structural, because s2
//!   proves the constant-citing spelling would have ADMITTED this exact
//!   mutant);
//! * **equation-set completeness** — fewer/more/mis-paired reflected cases
//!   than the KERNEL's minor premises refused
//!   (`EquationSetMismatch`, counted from `get_inductive`/`get_recursor`,
//!   probe s5 — never from the emission);
//! * **strict-subset families** — each refusal NAMES the failing equation
//!   (probes e1/e3/s3's wrong-value families, at the amended judgment's
//!   layer).
//!
//! Plus the honest boundary rows this increment must state rather than
//! blur: fib (`.cov` pair-threading measured green at the kernel, probe e4,
//! emitter arm pending the pair carrier) and the gate's refusal of
//! non-recursor side A.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, ReflectedCase, admit_lowering,
    check_faithful_equations, plan_clean_origin_body, reflect_structural_rec,
};
use trust_types::admissible_body::{RecBodyExpr, StructuralRecBody, recognize_structural_rec};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A (r3 spelling) ─────────────────────────

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_rec_body(step: Expr) -> Expr {
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]),
        [Expr::lam(BinderInfo::Default, nat(), nat()), cnst("Nat.zero"), step, Expr::bvar(0)],
    );
    Expr::lam(BinderInfo::Default, nat(), rec_app)
}

fn tozero_step() -> Expr {
    Expr::lam(BinderInfo::Default, nat(), Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)))
}

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|refusal| panic!("`{name}` must kernel-check as written: {refusal:?}"));
}

fn env_with_tozero() -> Environment {
    let mut env = Environment::with_prelude();
    define(&mut env, "tozero", Expr::arrow(nat(), nat()), nat_rec_body(tozero_step()));
    env
}

// ──────────────── side B: the emitted-MIR contract, hand-built ──────────────

fn nat_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::BignumNat, name: None }
}

fn nat_ref_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Ref { mutable: false, inner: Box::new(Ty::BignumNat) }, name: None }
}

fn call(callee: &str, args: Vec<Operand>, dest: Place, target: BlockId) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Unreachable,
        // Trust: added with the call-identity authentication field (9f00605c17);
        // these fixtures build a call from a bare name, which carries no
        // authenticated identity, and `None` is what every other test-side
        // constructor uses for that.
        callee_identity: None,
        callee_key: None,
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// The exact contract MIR `build_structural_rec_body` emits for tozero:
///
/// ```text
/// bb0: _2 = &_1;  is_zero(move _2) -> _3, bb1
/// bb1: switchInt(_3) [(0, bb3)] otherwise bb2
/// bb2: from_u64(0) -> _0, bb6                      // zero arm
/// bb3: from_u64(1) -> _4, bb4                      // succ arm
/// bb4: _5 = &_1; _6 = &_4; sub(move _5, move _6) -> _7, bb5
/// bb5: tozero(move _7) -> _0, bb6
/// bb6: return
/// ```
fn emitted_tozero_contract() -> VerifiableFunction {
    let locals = vec![
        nat_local(0),
        nat_local(1),
        nat_ref_local(2),
        LocalDecl { index: 3, ty: Ty::Bool, name: None },
        nat_local(4),
        nat_ref_local(5),
        nat_ref_local(6),
        nat_local(7),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(2),
                Rvalue::Ref { mutable: false, place: Place::local(1) },
            )],
            terminator: call(
                "trust_bignum::Nat::is_zero",
                vec![Operand::Move(Place::local(2))],
                Place::local(3),
                BlockId(1),
            ),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: Vec::new(),
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(0, 64))],
                Place::local(0),
                BlockId(6),
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                Place::local(4),
                BlockId(4),
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(Place::local(5), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(Place::local(6), Rvalue::Ref { mutable: false, place: Place::local(4) }),
            ],
            terminator: call(
                "trust_bignum::Nat::sub",
                vec![Operand::Move(Place::local(5)), Operand::Move(Place::local(6))],
                Place::local(7),
                BlockId(5),
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: call(
                "probe::tozero",
                vec![Operand::Move(Place::local(7))],
                Place::local(0),
                BlockId(6),
            ),
        },
        BasicBlock { id: BlockId(6), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "tozero".into(),
        def_path: "probe::tozero".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::BignumNat,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ══════════ side B, AS THE EXTRACTOR ACTUALLY RENDERS THE EMISSION ═════════
//
// `emitted_tozero_contract` above is the contract PICTURE — the shape written
// down in `recognize_structural_rec`'s doc and in `build_structural_rec_body`'s.
// It is not, byte for byte, what `trust_mir_extract::extract_function` hands the
// recognizer for the emitted body, and the difference is what the R1 fixture
// refused on (measured 2026-08-21, `tests/ui/trust/clean_origin_structural_rec.rs`
// → `LoweringUnrecognised`). This builder is the MEASURED one. Three things it
// gets right that the picture rounds off:
//
//  1. **The runtime callee strings.** `Nat::is_zero`/`Nat::from_u64` are defined
//     in trust-bignum's ROOT module, next to `Nat`, so rustc's inherent-impl
//     printer renders them `trust_bignum::Nat::is_zero`. `Nat::add`/`Nat::sub`/
//     `Nat::saturating_sub` are defined in `mod arith`, which is NOT the
//     module `Nat` lives in, so the same printer renders them
//     `trust_bignum::arith::<impl trust_bignum::Nat>::sub`. Measured by
//     extracting a hand-written Rust `n.sub(&Nat::from_u64(1))` with
//     `-Ztrust-dump=mir-only:<dir>`; both spellings appear in one dumped body.
//  2. **The local numbering.** The zero arm's `from_u64` destination temp is
//     allocated BEFORE `lower_arm` re-points the call at `_0`, so it stays
//     declared and dead; same for the self-call's temp. The succ arm therefore
//     starts at `_5`, not `_4`, and the body declares ten locals, two of them
//     dead. (`ArmLowerer::lower_arm` names this: "the temp allocated for it
//     stays declared but unused".)
//  3. **The carrier spelling.** The extractor renders an ADT by path
//     (`Ty::Adt { name: "trust_bignum::Nat" }`); it knows nothing of
//     `Ty::BignumNat`, which is the CARRIER DECISION's own spelling.
//
// ```text
// _0,_1,_4,_5,_8,_9: Nat   _2,_6,_7: &Nat   _3: bool      (_4,_9 dead)
// bb0: _2 = &_1;  is_zero(move _2) -> _3, bb1
// bb1: switchInt(move _3) [(0, bb3)] otherwise bb2
// bb2: from_u64(const 0u64) -> _0, bb6                     // zero arm
// bb3: from_u64(const 1u64) -> _5, bb4                     // succ arm…
// bb4: _6 = &_1; _7 = &_5; sub(move _6, move _7) -> _8, bb5
// bb5: clean_origin_structural_rec::tozero(move _8) -> _0, bb6
// bb6: return
// ```
fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn nat_adt_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: nat_adt(), name: None }
}

fn nat_adt_ref_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }, name: None }
}

/// Every call the emitter builds carries `UnwindAction::Continue` (the bignum
/// ops and the self-call can allocate and can exhaust the stack), which the
/// extractor renders `UnwindEdge::Continue`.
fn unwinding_call(callee: &str, args: Vec<Operand>, dest: Place, target: BlockId) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
        callee_key: None,
    }
}

/// The def path the emitted self-call carries: `Operand::function_handle` for
/// the def's OWN `DefId`, which the extractor renders with the same
/// `safe_def_path_str` it uses for the enclosing function's `def_path` — so the
/// two are equal by construction, which is exactly what the recognizer's
/// `callee == &func.def_path` test reads.
const FIXTURE_SELF_PATH: &str = "clean_origin_structural_rec::tozero";

/// The trust-bignum predecessor, under the def path it ACTUALLY has.
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";

fn emitted_tozero_as_extracted() -> VerifiableFunction {
    let locals = vec![
        nat_adt_local(0),
        nat_adt_local(1),
        nat_adt_ref_local(2),
        LocalDecl { index: 3, ty: Ty::Bool, name: None },
        // dead: the zero arm's from_u64 temp, re-pointed at `_0`.
        nat_adt_local(4),
        nat_adt_local(5),
        nat_adt_ref_local(6),
        nat_adt_ref_local(7),
        nat_adt_local(8),
        // dead: the self-call's temp, re-pointed at `_0`.
        nat_adt_local(9),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(2),
                Rvalue::Ref { mutable: false, place: Place::local(1) },
            )],
            terminator: unwinding_call(
                "trust_bignum::Nat::is_zero",
                vec![Operand::Move(Place::local(2))],
                Place::local(3),
                BlockId(1),
            ),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: Vec::new(),
            terminator: unwinding_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(0, 64))],
                Place::local(0),
                BlockId(6),
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: unwinding_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                Place::local(5),
                BlockId(4),
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(Place::local(6), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(Place::local(7), Rvalue::Ref { mutable: false, place: Place::local(5) }),
            ],
            terminator: unwinding_call(
                BIGNUM_SUB,
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                Place::local(8),
                BlockId(5),
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: unwinding_call(
                FIXTURE_SELF_PATH,
                vec![Operand::Move(Place::local(8))],
                Place::local(0),
                BlockId(6),
            ),
        },
        BasicBlock { id: BlockId(6), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "tozero".into(),
        def_path: FIXTURE_SELF_PATH.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
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

/// **THE AGREEMENT TEST.** The body the emitter really produces, read by the
/// recognizer that really reads it, through the real route. This is the
/// crate-level stand-in for `tests/ui/trust/clean_origin_structural_rec.rs`,
/// which cannot run until the compiler is rebuilt.
#[test]
fn control_7_the_extracted_emission_is_recognized_and_admits() {
    let extracted = emitted_tozero_as_extracted();

    // Side B's own reading, first and separately: the recognizer must produce
    // the planned trio from the MEASURED body, not merely from the picture.
    assert_eq!(
        recognize_structural_rec(&extracted),
        Some(StructuralRecBody {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        }),
        "the emitted-and-extracted body must read back as the planned recursion"
    );

    // …then the whole route, ending at the per-defining-equation kernel gate.
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("tozero plans (r3 flip)");
    let faithful = admit_lowering(&env, &plan, &extracted)
        .expect("the real emission must pass the per-defining-equation gate");
    assert_eq!(faithful.name(), "tozero");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
}

/// The measured body is only evidence if its mutations still refuse. The
/// mutation battery below runs on the contract picture; re-run the two that
/// bear on what this builder changed — the callee strings — on the measured
/// body, so a table that accepted "anything ending in `::sub`" would be caught.
#[test]
fn control_7_the_extracted_emission_still_refuses_forged_callees() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");

    // A user function whose def path merely LOOKS like the runtime's
    // module-qualified predecessor.
    let mut impostor = emitted_tozero_as_extracted();
    if let Terminator::Call { func: callee, .. } = &mut impostor.body.blocks[4].terminator {
        *callee = "my_crate::arith::<impl my_crate::Nat>::sub".into();
    }
    assert!(
        matches!(
            admit_lowering(&env, &plan, &impostor),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "a foreign `sub` must never read as the predecessor"
    );

    // The predecessor's SIBLING in the same impl block — `mul` is in exactly
    // the same module and renders with exactly the same `<impl …>` prefix, so
    // this is the mutation a prefix-matching table would let through.
    let mut wrong_op = emitted_tozero_as_extracted();
    if let Terminator::Call { func: callee, .. } = &mut wrong_op.body.blocks[4].terminator {
        *callee = "trust_bignum::arith::<impl trust_bignum::Nat>::mul".into();
    }
    assert!(
        matches!(
            admit_lowering(&env, &plan, &wrong_op),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "`mul` is not the predecessor, module-qualified or not"
    );

    // And the self-call still has to be the SELF call.
    let mut other_callee = emitted_tozero_as_extracted();
    if let Terminator::Call { func: callee, .. } = &mut other_callee.body.blocks[5].terminator {
        *callee = "clean_origin_structural_rec::other".into();
    }
    assert!(
        matches!(
            admit_lowering(&env, &plan, &other_callee),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "a non-self callee has no `Rec` reading"
    );
}

// ═════════════════════ THE ADMIT (paired with every refusal) ═══════════════

#[test]
fn control_7_the_contract_emission_admits_end_to_end() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("tozero plans (r3 flip)");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::StructuralNatRec {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        }
    );
    let faithful = admit_lowering(&env, &plan, &emitted_tozero_contract())
        .expect("the contract emission must pass the per-defining-equation gate");
    assert_eq!(faithful.name(), "tozero");
    assert_eq!(
        faithful.admitted_at(),
        &Ty::BignumNat,
        "admitted at the RESULT carrier — the bignum Nat"
    );
}

// ═════════════════════ MUTATION 1 — wrong-case value ═══════════════════════

#[test]
fn control_7_wrong_case_value_refused_at_both_layers() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");

    // STRUCTURAL layer: the emitted zero arm materialises 1 where the plan
    // says 0 — recognized shape disagrees with the plan.
    let mut mutant = emitted_tozero_contract();
    if let Terminator::Call { args, .. } = &mut mutant.body.blocks[2].terminator {
        *args = vec![Operand::Constant(ConstValue::Uint(1, 64))];
    }
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("a wrong base value must not pass the structural agreement");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");

    // KERNEL layer, measured separately (the structural catch is never a
    // substitute): feed the gate the mismatched trio directly. The refusal
    // must NAME the zero case (probe s3's wrong-base pin).
    let reflected = reflect_structural_rec(
        &env,
        "tozero",
        &StructuralRecBody {
            base: RecBodyExpr::NatConst(1),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
    )
    .expect("the wrong-value trio kernel-checks as terms (it is just wrong)");
    let gate_refusal = check_faithful_equations(&env, "tozero", &reflected, plan.result_carrier())
        .expect_err("the kernel must refuse the wrong zero case");
    match &gate_refusal {
        GateRefusal::EquationDisagreement { case, .. } => {
            assert_eq!(case, "Nat.zero", "the refusal must name the failing equation");
        }
        other => panic!("expected EquationDisagreement, got {other:?}"),
    }
}

// ═════════════════════ MUTATION 2 — swapped cases ══════════════════════════

#[test]
fn control_7_swapped_cases_refused() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");

    // Swap the SwitchInt targets — the polarity-inversion bug the
    // `-Ztrust-clean-origin-mutate-emitter` knob injects end-to-end (the
    // knob's SwitchInt swap hits this body's zero-test the same way it hits
    // the select diamonds). The self-call then sits in the arm the contract
    // reserves for the base case, which has no reading: `None` from the
    // recognizer, `LoweringUnrecognised` from the route.
    let mut mutant = emitted_tozero_contract();
    if let Terminator::SwitchInt { targets, otherwise, .. } = &mut mutant.body.blocks[1].terminator
    {
        let zero_target = targets[0].1;
        targets[0].1 = *otherwise;
        *otherwise = zero_target;
    }
    let refusal = admit_lowering(&env, &plan, &mutant).expect_err("swapped cases must not admit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "expected the recognizer to refuse the swapped-arm body, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect());
}

// ═════════════ MUTATION 3 — off-by-one recursive argument ══════════════════

#[test]
fn control_7_off_by_one_rec_arg_refused_at_both_layers() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");

    // STRUCTURAL layer: the emitted self-call passes the parameter itself
    // (`move _1`) instead of the predecessor temp — a DIVERGING binary. The
    // recognizer's belt (rec_arg must read as `Pred`) refuses.
    let mut mutant = emitted_tozero_contract();
    if let Terminator::Call { args, .. } = &mut mutant.body.blocks[5].terminator {
        *args = vec![Operand::Move(Place::local(1))];
    }
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("the off-by-one self-call must not pass recognition");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "expected the structural belt, got {refusal:?}"
    );

    // KERNEL layer — THE control that proves the catch is not merely
    // structural. Smuggle the off-by-one straight past the recognizer by
    // constructing the reflection with `rec_arg: Decreasing` (which renders
    // `fun k => Nat.succ k`). Probe s2 measures that the constant-citing
    // spelling ADMITS exactly this mutant; the amended judgment's identity
    // check refuses it at the kernel (probe s4).
    let reflected = reflect_structural_rec(
        &env,
        "tozero",
        &StructuralRecBody {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Decreasing,
        },
    )
    .expect("the wrong-argument trio kernel-checks as terms");
    let gate_refusal = check_faithful_equations(&env, "tozero", &reflected, plan.result_carrier())
        .expect_err("the kernel identity check must refuse `succ k` for `k`");
    assert!(
        matches!(gate_refusal, GateRefusal::RecursionStructureDisagreement { .. }),
        "expected the divergence catch, got {gate_refusal:?}"
    );
}

// ═══════════ MUTATION 4 — equation-set completeness (kernel count) ═════════

#[test]
fn control_7_equation_set_completeness_against_kernel_minor_count() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");
    let good = reflect_structural_rec(
        &env,
        "tozero",
        &StructuralRecBody {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
    )
    .expect("the correct trio reflects");

    // FEWER cases than the kernel's minor premises: drop the succ case.
    let mut fewer = good.clone();
    fewer.cases.truncate(1);
    let refusal = check_faithful_equations(&env, "tozero", &fewer, plan.result_carrier())
        .expect_err("a dropped case must refuse");
    assert!(
        matches!(refusal, GateRefusal::EquationSetMismatch { .. }),
        "expected the completeness refusal, got {refusal:?}"
    );

    // MORE cases: invent a third.
    let mut more = good.clone();
    more.cases.push(ReflectedCase {
        constructor: "Nat.succ".to_owned(),
        value: good.cases[1].value.clone(),
    });
    let refusal = check_faithful_equations(&env, "tozero", &more, plan.result_carrier())
        .expect_err("an invented case must refuse");
    assert!(matches!(refusal, GateRefusal::EquationSetMismatch { .. }), "got {refusal:?}");

    // MIS-PAIRED order: the count is right but the constructor pairing is
    // not — the pairing is indexed by the KERNEL's rule order (probe s5).
    let mut mispaired = good.clone();
    mispaired.cases.swap(0, 1);
    let refusal = check_faithful_equations(&env, "tozero", &mispaired, plan.result_carrier())
        .expect_err("a mis-paired case set must refuse");
    assert!(matches!(refusal, GateRefusal::EquationSetMismatch { .. }), "got {refusal:?}");
}

// ═══════════ MUTATION 5 — strict-subset families, named per case ═══════════

#[test]
fn control_7_subset_families_refused_naming_the_failing_equation() {
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");
    let carrier = plan.result_carrier();
    let good = reflect_structural_rec(
        &env,
        "tozero",
        &StructuralRecBody {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
    )
    .expect("the correct trio reflects");

    // (base ✓, step ✗): the identity family's step `fun k ih => succ ih` —
    // hand-built, since the vocabulary itself (rightly) cannot spell it.
    let mut wrong_step = good.clone();
    wrong_step.cases[1].value = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    );
    match check_faithful_equations(&env, "tozero", &wrong_step, carrier)
        .expect_err("the subset family must refuse on its violated equation")
    {
        GateRefusal::EquationDisagreement { case, .. } => assert_eq!(case, "Nat.succ"),
        other => panic!("expected EquationDisagreement at Nat.succ, got {other:?}"),
    }

    // (base ✗, step ✓): already pinned in mutation 1's kernel half — the
    // refusal names Nat.zero. (base ✓, step ✓, rec_arg ✗): mutation 3's
    // kernel half — RecursionStructureDisagreement. Together the three
    // refusals cover every strict-subset direction of the trio.
}

// ═══════════ the gate refuses non-recursor side A (its own parse) ══════════

#[test]
fn control_7_gate_refuses_non_recursor_side_a() {
    let mut env = env_with_tozero();
    // A kernel-checked NON-recursive definition…
    define(
        &mut env,
        "ident",
        Expr::arrow(nat(), nat()),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
    );
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan (for the carrier)");
    let reflected = reflect_structural_rec(
        &env,
        "ident",
        &StructuralRecBody {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
    )
    .expect("the trio reflects (terms are fine; side A is not a recursor)");
    let refusal = check_faithful_equations(&env, "ident", &reflected, plan.result_carrier())
        .expect_err("the per-equation judgment must refuse a non-recursor side A");
    assert!(
        matches!(refusal, GateRefusal::NotStructuralRecursor { .. }),
        "expected NotStructuralRecursor, got {refusal:?}"
    );
    assert!(
        refusal.note().contains("Please report it"),
        "a mis-routed declaration is internal, not a user error"
    );
}

// ═══════════ honest boundary rows: fib and its .cov auxiliary ══════════════

/// fib's user equations are MEASURED green at the kernel against the
/// `.cov`-backed constant (probe e4) — but the EMITTER arm waits on the pair
/// result carrier (`Prod Nat Nat` has no `trust-clean-carrier` mapping yet),
/// so this increment states the boundary instead of blurring it:
///
/// * `fib` (the wrapper `fun n => Prod.fst (fib.cov n)`) plans
///   `NotEmittable` — its body is a projection of a call, not a recursor
///   spine;
/// * `fib.cov` refuses at the CARRIER (`NoTotalCarrier`): `Prod Nat Nat` has
///   no total Rust carrier in this toolchain today.
///
/// If either pin flips, the pair carrier landed: route fib through a
/// sibling-call shape IN THAT CHANGE, with its own controls — never by
/// weakening this one.
#[test]
fn control_7_fib_boundary_stated_not_blurred() {
    let mut env = Environment::with_prelude();
    // The measured `.cov` mirror (r1_equation_probes' install_fib shape).
    let prod_nat = Expr::apps(
        Expr::const_(Name::from_string("Prod"), vec![Level::zero(), Level::zero()]),
        [nat(), nat()],
    );
    let pmk = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Prod.mk"), vec![Level::zero(), Level::zero()]),
            [nat(), nat(), a, b],
        )
    };
    let pfst = |p: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Prod.fst"), vec![Level::zero(), Level::zero()]),
            [nat(), nat(), p],
        )
    };
    let psnd = |p: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Prod.snd"), vec![Level::zero(), Level::zero()]),
            [nat(), nat(), p],
        )
    };
    let add = |a: Expr, b: Expr| Expr::apps(cnst("Nat.add"), [a, b]);
    let ih = || Expr::bvar(0);
    let step = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            prod_nat.clone(),
            pmk(psnd(ih()), add(psnd(ih()), pfst(ih()))),
        ),
    );
    let cov_val = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]),
            [
                Expr::lam(BinderInfo::Default, nat(), prod_nat.clone()),
                pmk(cnst("Nat.zero"), Expr::app(cnst("Nat.succ"), cnst("Nat.zero"))),
                step,
                Expr::bvar(0),
            ],
        ),
    );
    define(&mut env, "fib.cov", Expr::arrow(nat(), prod_nat), cov_val);
    define(
        &mut env,
        "fib",
        Expr::arrow(nat(), nat()),
        Expr::lam(BinderInfo::Default, nat(), pfst(Expr::app(cnst("fib.cov"), Expr::bvar(0)))),
    );

    let fib_refusal = plan_clean_origin_body(&env, "fib")
        .expect_err("fib's wrapper body (Prod.fst of a call) is outside the R1 fragment");
    assert!(matches!(fib_refusal, EmitRefusal::NotEmittable { .. }), "got {fib_refusal:?}");
    assert!(!fib_refusal.is_compiler_defect(), "an honest capability boundary");

    let cov_refusal = plan_clean_origin_body(&env, "fib.cov")
        .expect_err("fib.cov's pair result has no total carrier in this toolchain");
    assert!(
        matches!(cov_refusal, EmitRefusal::NoTotalCarrier { .. }),
        "the .cov boundary is the CARRIER, not the recursion: got {cov_refusal:?}"
    );
}
