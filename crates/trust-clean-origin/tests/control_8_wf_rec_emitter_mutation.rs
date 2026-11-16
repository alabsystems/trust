// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 8 (well-founded recursion) — the R2 mutation battery for the
//! F-LAYER lane** (§6e MEASUREMENT NOTE + §6e ESCAPE CLOSED,
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`).
//!
//! The fast-lane end-to-end: side A is the raw-kernel mirror of the island's
//! measured `countdownSum` lowering (`recursion_boundary_probes.rs`'s
//! `countdownSum` row; spine spelling pinned by `r2_wf_equation_probes` w1),
//! side B is the emitted-MIR contract hand-built exactly as
//! `compiler/rustc_mir_transform/src/clean_origin_mir.rs`'s
//! `build_wf_rec_body` emits it, routed through the REAL producers:
//! `plan_clean_origin_body` → `admit_lowering` → `recognize_wf_nat_rec` →
//! `reflect_wf::reflect_wf_functional` → `check_faithful_wf_functional`.
//!
//! This is `control_7`'s structure at R2's judgment, and the mutations are the
//! ones R2's own probes measured — NOT R1's, because R2's judgment is not
//! R1's:
//!
//! * **wrong branch value** — structural (`LoweringShapeMismatch`) AND,
//!   smuggled past the structural check, kernel
//!   (`FunctionalDisagreement`, probe w6/c6 — a wrong VALUE is a DEFEQ
//!   verdict);
//! * **diverging recursive argument** — structural (the recognizer's own belt
//!   refuses a self-call argument that is not the predecessor) AND, smuggled
//!   straight past the recognizer by constructing the reflection with
//!   `rec_arg: Decreasing`, refused at the KERNEL layer as
//!   `DecreaseSlotBorrowRefused` — a TYPING verdict, because side A's proof of
//!   `Nat.lt (n-1) n` does not fit a call at `n` (probe w7/d1, c6). Note the
//!   polarity difference from R1: there the off-by-one is caught by a separate
//!   recursive-argument identity component, here it is caught by the kernel's
//!   own typing rule at the borrowed slot;
//! * **emitter-authored decrease proof** — refused by the borrow even when the
//!   proof is CORRECT (probe c5), because "correct" is exactly what the gate
//!   would otherwise take on trust;
//! * **axiom-bearing closure** — a declaration whose termination rests on an
//!   assumed decrease is refused as `AssumptionBearingRecursion` naming the
//!   axiom (probes c1/c2), and the mutation is measured at the WHOLE ROUTE
//!   here rather than only at the gate;
//! * **swapped arms** — the recognizer's contract refuses
//!   (`LoweringUnrecognised`; the self-call has no zero-arm reading), the
//!   `-Ztrust-clean-origin-mutate-emitter` SwitchInt swap's fast-lane mirror.
//!
//! Plus the two spellings of side A (eta-expanded and eta-contracted), because
//! the §6e MEASUREMENT NOTE records a design that parsed neither, and the
//! honest boundary rows this increment must state rather than blur.
//!
//! # HONESTY RULE, inherited
//!
//! Every ADMIT is paired with a refused mutation at the same layer, and the
//! side-B producers are FROZEN against this file: if a verdict here is not the
//! one the lane wants, the fix is never an edit to `reflect_wf.rs` or to
//! `recognize_wf_nat_rec`.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::admission::{
    DigestMintRefusal, ExportDigestRefusal, VerdictDigest, mint_encoded_digest_for_export,
};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, FaithfulnessMethod, GateRefusal, NonExportableNotice,
    NonExportableReason, ReflectedWfFunctional, admit_lowering, check_faithful_wf_functional,
    plan_clean_origin_body, reflect_wf_functional,
};
use trust_symbols::{
    AxiomClosure, CicKernelRecheck, KernelAuthority as _, KernelStatus, TermDigest,
};
use trust_types::admissible_body::{RecBodyExpr, WfRecBody, recognize_wf_nat_rec};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────── side A (the island's WF lowering) ─────────────────

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

fn nat_num(k: u64) -> Expr {
    let mut e = cnst("Nat.zero");
    for _ in 0..k {
        e = Expr::app(cnst("Nat.succ"), e);
    }
    e
}

fn succ(x: Expr) -> Expr {
    Expr::app(cnst("Nat.succ"), x)
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.add"), [a, b])
}

fn sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.sub"), [a, b])
}

fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.lt"), [a, b])
}

/// `(y : Nat) → Nat.lt y X → Nat`, with `X` seen from under `y`.
fn rec_ty(x_under_y: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), Expr::arrow(nat_lt(Expr::bvar(0), x_under_y), nat()))
}

/// The ETA-EXPANDED spelling probe w1 pins:
/// `fun (n : Nat) => @WellFounded.fix.{1,1} Nat (fun _ => Nat) Nat.lt Nat.lt_wf F n`.
fn wf_body(f: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), fix_spine(f, Some(Expr::bvar(0))))
}

/// The ETA-CONTRACTED spelling the §6e MEASUREMENT NOTE records — five
/// arguments, no outer lambda.
fn wf_body_eta_contracted(f: Expr) -> Expr {
    fix_spine(f, None)
}

fn fix_spine(f: Expr, major: Option<Expr>) -> Expr {
    let mut args = vec![
        nat(),
        Expr::lam(BinderInfo::Default, nat(), nat()),
        cnst("Nat.lt"),
        cnst("Nat.lt_wf"),
        f,
    ];
    args.extend(major);
    Expr::apps(Expr::const_(Name::from_string("WellFounded.fix"), vec![lvl1(), lvl1()]), args)
}

/// `@Nat.le.refl 1 : Nat.lt 0 1` — the side condition `Nat.sub_lt` needs.
fn one_pos() -> Expr {
    Expr::app(cnst("Nat.le.refl"), nat_num(1))
}

/// The `countdownSum` functional, ISLAND shape. `then_call` lives in the scope
/// `[x = bvar 2, rec = bvar 1, h = bvar 0]`; `else_value` in `[x, rec, _]`.
fn cds_f(then_call: Expr, else_value: Expr) -> Expr {
    let c_at = |x: Expr| nat_lt(cnst("Nat.zero"), x);
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            rec_ty(Expr::bvar(1)),
            Expr::apps(
                Expr::const_(Name::from_string("dite"), vec![lvl1()]),
                [
                    nat(),
                    c_at(Expr::bvar(1)),
                    Expr::apps(cnst("Nat.decLt"), [cnst("Nat.zero"), Expr::bvar(1)]),
                    Expr::lam(BinderInfo::Default, c_at(Expr::bvar(1)), then_call),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::app(cnst("Not"), c_at(Expr::bvar(1))),
                        else_value,
                    ),
                ],
            ),
        ),
    )
}

/// `x + rec (x - 1) (Nat.sub_lt x 1 h 0<1)` — the honest, kernel-backed step.
fn cds_then_honest() -> Expr {
    add(
        Expr::bvar(2),
        Expr::apps(
            Expr::bvar(1),
            [
                sub(Expr::bvar(2), nat_num(1)),
                Expr::apps(
                    cnst("Nat.sub_lt"),
                    [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                ),
            ],
        ),
    )
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

fn env_with_cds() -> Environment {
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "countdownSum",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(cds_then_honest(), cnst("Nat.zero"))),
    );
    env
}

/// The planned trio for `countdownSum`, in the vocabulary both sides use.
fn planned_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: RecBodyExpr::NatConst(0),
        nonzero_value: RecBodyExpr::Add(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Rec),
        ),
        rec_args: vec![RecBodyExpr::Pred],
        measure_index: 0,
        lowering: trust_clean_origin::WfLowering::OnParameter,
    }
}

fn recognised_body() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::NatConst(0),
        nonzero_value: RecBodyExpr::Add(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Rec),
        ),
        rec_args: vec![RecBodyExpr::Pred],
        measure_index: 0,
    }
}

// ══════════ side B, AS THE EXTRACTOR RENDERS THE EMISSION ═════════════════
//
// Traced block by block through `ArmLowerer` for
// `zero_value = NatConst(0)`, `nonzero_value = Add(Decreasing, Rec)`,
// `rec_arg = Pred` — thirteen locals (two dead) and eight blocks:
//
// ```text
// _0,_1,_4,_5,_8,_9,_12: Nat   _2,_6,_7,_10,_11: &Nat   _3: bool  (_4,_12 dead)
// bb0: _2 = &_1;  is_zero(move _2) -> _3, bb1
// bb1: switchInt(move _3) [(0, bb3)] otherwise bb2
// bb2: from_u64(const 0u64) -> _0, bb7                        // zero arm
// bb3: from_u64(const 1u64) -> _5, bb4                        // nonzero arm…
// bb4: _6 = &_1; _7 = &_5; sub(move _6, move _7) -> _8, bb5
// bb5: countdownSum(move _8) -> _9, bb6
// bb6: _10 = &_1; _11 = &_9; add(move _10, move _11) -> _0, bb7
// bb7: return
// ```
//
// The three roundings `control_7` records apply identically here, because the
// emitter is the same one: the arm temps that `lower_arm` re-points at `_0`
// stay DECLARED and dead (`_4` for the zero arm's `from_u64`, `_12` for the
// root `add`); the runtime callee paths depend on WHICH MODULE the `impl`
// block is typed in (`is_zero`/`from_u64` render co-located,
// `sub`/`add` render module-qualified out of `mod arith`); and the extractor
// renders an ADT by path (`Ty::Adt { name: "trust_bignum::Nat" }`), never the
// carrier decision's own `Ty::BignumNat`.

const FIXTURE_SELF_PATH: &str = "clean_origin_wf_rec::countdownSum";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn nat_adt_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: nat_adt(), name: None }
}

fn nat_adt_ref_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }, name: None }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// Every call the emitter builds carries `UnwindAction::Continue` (the bignum
/// ops and the self-call can allocate and can exhaust the stack), which the
/// extractor renders `UnwindEdge::Continue`.
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
        unwind: UnwindEdge::Continue,
        callee_identity: None,
        callee_key: None,
    }
}

fn emitted_countdown_sum() -> VerifiableFunction {
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
        nat_adt_local(9),
        nat_adt_ref_local(10),
        nat_adt_ref_local(11),
        // dead: the root `add`'s temp, re-pointed at `_0`.
        nat_adt_local(12),
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
                BlockId(7),
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: call(
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
            terminator: call(
                BIGNUM_SUB,
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                Place::local(8),
                BlockId(5),
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: call(
                FIXTURE_SELF_PATH,
                vec![Operand::Move(Place::local(8))],
                Place::local(9),
                BlockId(6),
            ),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![
                assign(Place::local(10), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(Place::local(11), Rvalue::Ref { mutable: false, place: Place::local(9) }),
            ],
            terminator: call(
                BIGNUM_ADD,
                vec![Operand::Move(Place::local(10)), Operand::Move(Place::local(11))],
                Place::local(0),
                BlockId(7),
            ),
        },
        BasicBlock { id: BlockId(7), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "countdownSum".into(),
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

fn nat_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_for(&nat()).expect("I6: Nat carries at trust_bignum::Nat")
}

// ═══════════════════ THE PLAN — both side-A spellings ══════════════════════

/// **The eta-contraction row.** The §6e MEASUREMENT NOTE records that a design
/// assuming R1's shape "parses nothing" against the island's spine, so the
/// plan lane reads BOTH spellings and this probe asserts it — with the
/// eta-contracted declaration built as a real kernel definition, not as a term
/// nobody typed.
#[test]
fn control_8_both_side_a_spellings_plan_to_the_same_shape() {
    let mut env = env_with_cds();
    define(
        &mut env,
        "countdownSumEta",
        Expr::arrow(nat(), nat()),
        wf_body_eta_contracted(cds_f(cds_then_honest(), cnst("Nat.zero"))),
    );

    for name in ["countdownSum", "countdownSumEta"] {
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|refusal| panic!("`{name}` must plan: {}", refusal.note()));
        assert_eq!(
            plan.shape(),
            &planned_shape(),
            "both spellings of the fix spine must read to the SAME functional; a parser \
             written against one reads NOTHING of the other, which is the recorded defect \
             ({name})"
        );
        assert_eq!(plan.return_ty(), &Ty::BignumNat);
    }
}

/// A `WellFounded.fix` def whose functional never USES its recursive slot is
/// not a recursion this lane gates, and the refusal says so — the
/// `recursion_boundary_probes` r4 `wfz` shape, still refused after R2.
#[test]
fn control_8_a_fix_that_never_recurses_is_not_this_lane() {
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "wfz",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(cnst("Nat.zero"), cnst("Nat.zero"))),
    );
    let refusal =
        plan_clean_origin_body(&env, "wfz").expect_err("a fix with no self-call is not R2's lane");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is a capability refusal");
    assert!(
        refusal.note().contains("never uses its recursive slot"),
        "the refusal must name the boundary: {}",
        refusal.note()
    );
}

// ═════════════════════ THE ADMIT (paired with every refusal) ═══════════════

#[test]
fn control_8_the_emission_is_recognized_and_admits_end_to_end() {
    let extracted = emitted_countdown_sum();

    // Side B's own reading, first and separately: the recognizer must produce
    // the planned trio from the emitted body, not merely from the picture.
    assert_eq!(
        recognize_wf_nat_rec(&extracted),
        Some(recognised_body()),
        "the emitted-and-extracted body must read back as the planned recursion"
    );

    // …then the whole route, ending at the F-layer kernel gate.
    let env = env_with_cds();
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("countdownSum plans");
    assert_eq!(plan.shape(), &planned_shape());
    let faithful =
        admit_lowering(&env, &plan, &extracted).expect("the emission must pass the F-layer gate");
    assert_eq!(faithful.name(), "countdownSum");
    assert_eq!(
        faithful.admitted_at(),
        &Ty::BignumNat,
        "admitted at the RESULT carrier — the bignum Nat"
    );
    assert_eq!(
        faithful.method(),
        FaithfulnessMethod::WellFoundedFunctionalDefeq,
        "and the verdict must record WHICH judgment produced it — never whole-term defeq"
    );
}

/// The measured body is only evidence if its mutations still refuse. Re-run
/// the callee-string rows on it: a table that accepted "anything ending in
/// `::sub`" would be caught here.
#[test]
fn control_8_the_emission_still_refuses_forged_callees() {
    let env = env_with_cds();
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plan");

    for (block, forged) in [
        // A user function whose def path merely LOOKS like the runtime's.
        (4usize, "my_crate::arith::<impl my_crate::Nat>::sub"),
        // The predecessor's SIBLING in exactly the same impl block — the
        // mutation a prefix-matching table would let through. §R6 made `mul`
        // itself an AUTHENTICATED operation, so the sibling that carries this
        // row is now `div`: same module, same `<impl …>` prefix, still no row.
        (4, "trust_bignum::arith::<impl trust_bignum::Nat>::div"),
        // And the self-call still has to be the SELF call.
        (5, "clean_origin_wf_rec::other"),
        (6, "trust_bignum::arith::<impl trust_bignum::Nat>::div"),
    ] {
        let mut mutant = emitted_countdown_sum();
        if let Terminator::Call { func: callee, .. } = &mut mutant.body.blocks[block].terminator {
            *callee = forged.into();
        }
        assert!(
            matches!(
                admit_lowering(&env, &plan, &mutant),
                Err(EmitRefusal::LoweringUnrecognised { .. })
            ),
            "`{forged}` must not read as the operation it impersonates"
        );
    }

    // §R6 — `add` → `mul` at the ROOT is still refused, but its refusal CLASS
    // moved and saying so is the point of keeping it. `mul` now READS (it is
    // the `nat.mul` row), so the body is no longer unrecognisable: it is
    // recognised as a DIFFERENT recursion than the one planned, and the
    // structural agreement catches it by direct equality. A stronger refusal,
    // not a weaker one — it names both shapes instead of saying "not
    // recognised" — and the countdownSum emission still cannot become a
    // product.
    let mut mul_for_add = emitted_countdown_sum();
    if let Terminator::Call { func: callee, .. } = &mut mul_for_add.body.blocks[6].terminator {
        *callee = "trust_bignum::arith::<impl trust_bignum::Nat>::mul".into();
    }
    let refusal = admit_lowering(&env, &plan, &mul_for_add)
        .expect_err("`mul` where the definition says `add` must never emit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural agreement to separate the two operations, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");
}

// ═════════════════ MUTATION 1 — wrong branch value ═════════════════════════

#[test]
fn control_8_wrong_branch_value_refused_at_both_layers() {
    let env = env_with_cds();
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plan");

    // STRUCTURAL layer: the emitted zero arm materialises 1 where the plan
    // says 0.
    let mut mutant = emitted_countdown_sum();
    if let Terminator::Call { args, .. } = &mut mutant.body.blocks[2].terminator {
        *args = vec![Operand::Constant(ConstValue::Uint(1, 64))];
    }
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("a wrong zero-branch value must not pass the structural agreement");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");

    // KERNEL layer, measured separately — the structural catch is never a
    // substitute. Feed the gate the mismatched reading directly, through the
    // REAL reflection producer, and require a DEFEQ verdict (probe w6/c6:
    // a wrong VALUE is `FunctionalDisagreement`, distinct from the borrow's
    // typing refusal).
    for wrong in [
        WfRecBody { zero_value: RecBodyExpr::NatConst(1), ..recognised_body() },
        // a wrong nonzero branch: `(n + 1) + f(n - 1)` — probe w6's
        // wrong-addend row, reached through the emitted vocabulary.
        WfRecBody {
            nonzero_value: RecBodyExpr::Add(
                Box::new(RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Decreasing),
                    Box::new(RecBodyExpr::NatConst(1)),
                )),
                Box::new(RecBodyExpr::Rec),
            ),
            ..recognised_body()
        },
        // swapped addends: `f(n - 1) + n`. Kernel-typed, genuinely different.
        WfRecBody {
            nonzero_value: RecBodyExpr::Add(
                Box::new(RecBodyExpr::Rec),
                Box::new(RecBodyExpr::Decreasing),
            ),
            ..recognised_body()
        },
    ] {
        let reflected = reflect_wf_functional(
            &env,
            "countdownSum",
            &wrong,
            trust_clean_origin::WfLowering::OnParameter,
        )
        .expect("the wrong-value functional reflects as a term (it is just wrong)");
        let gate_refusal =
            check_faithful_wf_functional(&env, "countdownSum", &reflected, &nat_carrier())
                .expect_err("the kernel must refuse a wrong branch value");
        assert!(
            matches!(gate_refusal, GateRefusal::FunctionalDisagreement { .. }),
            "a wrong VALUE is a defeq verdict, got {gate_refusal:?}"
        );
    }
}

// ═══════════ MUTATION 2 — diverging recursive argument ═════════════════════

/// R1's off-by-one, at R2's judgment. The catch has MOVED — it is the kernel's
/// own typing rule at the borrowed decrease slot, not a separate
/// recursive-argument identity component (probe w7: the identity DISSOLVES
/// into typing for a well-founded spine) — and this control pins that it is
/// still a catch, at both layers.
#[test]
fn control_8_diverging_recursive_argument_refused_at_both_layers() {
    let env = env_with_cds();
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plan");

    // STRUCTURAL layer: the emitted self-call passes the parameter itself
    // (`move _1`) instead of the predecessor temp — a DIVERGING binary. The
    // recognizer's belt (the self-call argument must read as the predecessor)
    // refuses.
    let mut mutant = emitted_countdown_sum();
    if let Terminator::Call { args, .. } = &mut mutant.body.blocks[5].terminator {
        *args = vec![Operand::Move(Place::local(1))];
    }
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("a self-call on the parameter itself must not admit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "expected the recognizer's belt, got {refusal:?}"
    );

    // KERNEL layer, with the recognizer removed: construct the reflection
    // directly at a non-decreasing argument. Side A's borrowed proof is of
    // `Nat.lt (n - 1) n` and cannot fill a slot at `n`, so the kernel refuses
    // — a TYPING verdict, reported as `DecreaseSlotBorrowRefused`.
    let diverging = WfRecBody { rec_args: vec![RecBodyExpr::Decreasing], ..recognised_body() };
    let reflected = reflect_wf_functional(
        &env,
        "countdownSum",
        &diverging,
        trust_clean_origin::WfLowering::OnParameter,
    )
    .expect("the diverging reading reflects as a term");
    let gate_refusal =
        check_faithful_wf_functional(&env, "countdownSum", &reflected, &nat_carrier())
            .expect_err("a non-decreasing emitted recursion cannot take side A's proof");
    assert!(
        matches!(gate_refusal, GateRefusal::DecreaseSlotBorrowRefused { .. }),
        "the divergence catch must be reported as a TYPING refusal, got {gate_refusal:?}"
    );
    assert!(
        gate_refusal.note().contains("MIR contains none"),
        "the note must say why side B has no proof of its own:\n{}",
        gate_refusal.note()
    );
}

// ═══════════ MUTATION 3 — an emitter-AUTHORED decrease proof ═══════════════

/// The producer cannot write one — every slot goes through the sentinel by
/// construction — so this mutation is injected at the gate's own boundary, the
/// only place a `ReflectedWfFunctional` can be spelled by hand. Probe c5's
/// row, restated on the emitted functional: even a CORRECT authored proof is
/// refused, because "correct" is what the gate would take on trust.
#[test]
fn control_8_an_emitter_authored_decrease_proof_is_refused() {
    let env = env_with_cds();

    // Byte-for-byte the honest functional, with side A's own proof written
    // into the slot instead of the sentinel.
    let authored = ReflectedWfFunctional { functional: cds_f(cds_then_honest(), cnst("Nat.zero")) };
    let refusal = check_faithful_wf_functional(&env, "countdownSum", &authored, &nat_carrier())
        .expect_err("side B may not author a decrease proof, correct or not");
    assert!(matches!(refusal, GateRefusal::DecreaseSlotBorrowRefused { .. }), "got {refusal:?}");
    assert!(
        refusal.note().contains("definitionally equal"),
        "the note must say why borrowing costs no checking power (probe w7/d2):\n{}",
        refusal.note()
    );

    // …and the REAL producer never writes one: the same body, reflected, is
    // admitted. That pairing is what makes the refusal above a statement about
    // authorship rather than about the term.
    let reflected = reflect_wf_functional(
        &env,
        "countdownSum",
        &recognised_body(),
        trust_clean_origin::WfLowering::OnParameter,
    )
    .expect("reflects");
    check_faithful_wf_functional(&env, "countdownSum", &reflected, &nat_carrier())
        .expect("the producer's own rendering, with the sentinel, admits");
}

// ═══════════ MUTATION 4 — an axiom-bearing closure, END TO END ═════════════

/// Probe c2 measured this at the gate. Here it is measured through the WHOLE
/// ROUTE — plan, emission, recognizer, reflection, gate — because the escape
/// the §6e ESCAPE CLOSED block names is only closed if it is closed on the
/// path the compiler actually takes.
///
/// **The mutation is deliberately NOT a mistranslation.** The emitted body is
/// byte-identical to the honest one and the recursion is at `n - 1`; what
/// changes is that the DECREASE PROOF is an `axiom` instead of the prelude's
/// `Nat.sub_lt`. That is the exact class the escape lives in, and it is the
/// class the plan lane is deliberately BLIND to: `read_wf_value` reads the
/// self-call's argument and reads PAST its proof (probe w7/d2 — two
/// functionals differing only in the slot's proof are defeq, so the proof
/// contributes nothing the comparison reads). The plan's blindness is only
/// safe because the gate audits the closure, and this control is what says so.
#[test]
fn control_8_an_assumed_decrease_is_refused_through_the_whole_route() {
    let mut env = Environment::with_prelude();
    // `axiom bogus : ∀ x, Nat.lt (Nat.sub x 1) x` — the right TYPE for the
    // slot, so the functional kernel-checks and the declaration ADMITS.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("control8_bogus_lt"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat(),
            nat_lt(sub(Expr::bvar(0), nat_num(1)), Expr::bvar(0)),
        ),
    })
    .expect("an axiom may be declared");
    define(
        &mut env,
        "countdownSum",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
            add(
                Expr::bvar(2),
                Expr::apps(
                    Expr::bvar(1),
                    [
                        sub(Expr::bvar(2), nat_num(1)),
                        Expr::app(cnst("control8_bogus_lt"), Expr::bvar(2)),
                    ],
                ),
            ),
            cnst("Nat.zero"),
        )),
    );

    // It PLANS — the plan lane reads shape and termination-evidence FORM, and
    // this declaration has both. That is the point: the plan is not the guard,
    // and a lane that refused here would be refusing for the wrong reason.
    let plan = plan_clean_origin_body(&env, "countdownSum")
        .expect("the axiom-bearing declaration is still a well-founded spine, so it plans");
    assert_eq!(
        plan.shape(),
        &planned_shape(),
        "and it plans the SAME shape as the honest declaration — the assumption is \
         invisible to every structural reading, which is why the closure audit exists"
    );

    // The gate refuses, naming the axiom, with options (v7/D3).
    let refusal = admit_lowering(&env, &plan, &emitted_countdown_sum()).expect_err(
        "a recursive Clean-origin body whose termination rests on an assumed decrease must \
         not be emitted, however faithfully the lowering mirrors it",
    );
    let EmitRefusal::Gate(GateRefusal::AssumptionBearingRecursion { assumptions, .. }) = &refusal
    else {
        panic!("expected an assumption-bearing gate refusal, got {refusal:?}");
    };
    assert!(
        assumptions.iter().any(|name| name == "control8_bogus_lt"),
        "the refusal must NAME the axiom: {assumptions:?}"
    );
    assert!(
        !refusal.is_compiler_defect(),
        "the declaration rests on an assumption the AUTHOR stated — telling them to file a \
         compiler bug about their own `axiom` would send them to fix something they did not \
         break"
    );
    let note = refusal.note();
    assert!(note.contains("terminat"), "the note must carry the termination reasoning:\n{note}");
    assert!(note.contains("options:"), "the note must carry options:\n{note}");

    // ANTI-VACUITY: the identical route with the prelude's own `Nat.sub_lt` in
    // the slot ADMITS, so the refusal is about the assumption and not about
    // the shape.
    let honest = env_with_cds();
    let honest_plan = plan_clean_origin_body(&honest, "countdownSum").expect("plan");
    admit_lowering(&honest, &honest_plan, &emitted_countdown_sum())
        .expect("the same emission against a kernel-backed decrease admits");
}

/// The OTHER half of the escape, and where it is caught on the compiler path:
/// a genuinely DIVERGING declaration — `f (n + 1)` backed by
/// `axiom bogus : ∀ x, Nat.lt (succ x) x`, the exact term probe c1 measured
/// kernel-checking and ADMITTING — never reaches the gate at all, because
/// `n + 1` is not in the emittable self-call argument vocabulary.
///
/// Recorded as a SEPARATE row rather than folded into the one above, because
/// the two are caught by different things and a reader must not conclude that
/// the plan lane is the guard: probe c2 measures the same term refused AT THE
/// GATE, which is what covers the case where a future widening lets such an
/// argument through.
#[test]
fn control_8_a_diverging_argument_never_reaches_the_gate() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("control8_diverging_lt"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat(), nat_lt(succ(Expr::bvar(0)), Expr::bvar(0))),
    })
    .expect("an axiom may be declared");
    define(
        &mut env,
        "diverging",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
            add(
                Expr::bvar(2),
                Expr::apps(
                    Expr::bvar(1),
                    [succ(Expr::bvar(2)), Expr::app(cnst("control8_diverging_lt"), Expr::bvar(2))],
                ),
            ),
            cnst("Nat.zero"),
        )),
    );
    let refusal = plan_clean_origin_body(&env, "diverging")
        .expect_err("`f (n + 1)` is not an emittable self-call argument");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(
        refusal.note().contains("self-call argument"),
        "the refusal must name the position:\n{}",
        refusal.note()
    );
}

// ═════════════════════ MUTATION 5 — swapped arms ═══════════════════════════

#[test]
fn control_8_swapped_arms_refused() {
    let env = env_with_cds();
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plan");

    // Swap the SwitchInt targets — the polarity inversion the
    // `-Ztrust-clean-origin-mutate-emitter` knob injects end-to-end. The
    // self-call then sits in the arm the contract reserves for the zero case,
    // which has no reading.
    let mut mutant = emitted_countdown_sum();
    if let Terminator::SwitchInt { targets, otherwise, .. } = &mut mutant.body.blocks[1].terminator
    {
        let zero_target = targets[0].1;
        targets[0].1 = *otherwise;
        *otherwise = zero_target;
    }
    let refusal = admit_lowering(&env, &plan, &mutant).expect_err("swapped arms must not admit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "expected the recognizer to refuse the swapped-arm body, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect());
}

// ═════════ the gate refuses a non-fix side A (its own parse) ═══════════════

/// The F-layer gate re-reads side A itself and refuses a structural spine —
/// the mirror of `control_7`'s non-recursor row. A routing defect must not be
/// absorbed by whichever gate it lands in.
#[test]
fn control_8_gate_refuses_a_structural_side_a() {
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "tozero",
        Expr::arrow(nat(), nat()),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::apps(
                Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
                [
                    Expr::lam(BinderInfo::Default, nat(), nat()),
                    cnst("Nat.zero"),
                    Expr::lam(
                        BinderInfo::Default,
                        nat(),
                        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
                    ),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let reflected =
        ReflectedWfFunctional { functional: cds_f(cds_then_honest(), cnst("Nat.zero")) };
    let refusal = check_faithful_wf_functional(&env, "tozero", &reflected, &nat_carrier())
        .expect_err("the F-layer gate must refuse a `Nat.rec` side A");
    assert!(matches!(refusal, GateRefusal::NotWellFoundedRecursor { .. }), "got {refusal:?}");
    assert!(
        refusal.note().contains("Nat.rec"),
        "the refusal must name the head it found:\n{}",
        refusal.note()
    );
}

// ═══════════ honest boundary rows: stated, not blurred ═════════════════════

/// The measured boundaries of the R2 fragment, each with the refusal that
/// states it. If any of these flips, the increment that flips it lands its own
/// controls — never by weakening this one.
#[test]
fn control_8_fragment_boundaries_stated_not_blurred() {
    // (a) a decrease by TWO. The kernel admits such a definition (probe c6
    //     builds `cds_two_back` and gates it), but the EMITTED contract's
    //     predecessor is `Nat::sub(&n, &1)`, so the plan refuses rather than
    //     emitting a body that decreases by one for a definition that
    //     decreases by two.
    let mut env = Environment::with_prelude();
    let two_pos = Expr::apps(cnst("Nat.le.step"), [nat_num(1), nat_num(1), one_pos()]);
    define(
        &mut env,
        "twoBack",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
            add(
                Expr::bvar(2),
                Expr::apps(
                    Expr::bvar(1),
                    [
                        sub(Expr::bvar(2), nat_num(2)),
                        Expr::apps(
                            cnst("Nat.sub_lt"),
                            [Expr::bvar(2), nat_num(2), Expr::bvar(0), two_pos],
                        ),
                    ],
                ),
            ),
            cnst("Nat.zero"),
        )),
    );
    let refusal = plan_clean_origin_body(&env, "twoBack")
        .expect_err("a decrease by two is outside the emitted contract");
    assert!(
        refusal.note().contains("exactly \none") || refusal.note().contains("exactly one"),
        "the refusal must name the boundary:\n{}",
        refusal.note()
    );
    assert!(!refusal.is_compiler_defect());

    // (b) a `Nat.pred` spelling of the SAME decrease is INSIDE the fragment —
    //     the boundary is the value, not the syntax (probe w6 (b′)).
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "predSpelling",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
            add(
                Expr::bvar(2),
                Expr::apps(
                    Expr::bvar(1),
                    [
                        Expr::app(cnst("Nat.pred"), Expr::bvar(2)),
                        Expr::apps(
                            cnst("Nat.sub_lt"),
                            [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                        ),
                    ],
                ),
            ),
            cnst("Nat.zero"),
        )),
    );
    let plan = plan_clean_origin_body(&env, "predSpelling")
        .expect("the `Nat.pred` spelling of `n - 1` is the same recursion");
    assert_eq!(plan.shape(), &planned_shape());
    // …and it admits against the SAME emitted body, because the kernel
    // identifies the two spellings.
    let mut extracted = emitted_countdown_sum();
    extracted.name = "predSpelling".into();
    extracted.def_path = "clean_origin_wf_rec::predSpelling".into();
    if let Terminator::Call { func: callee, .. } = &mut extracted.body.blocks[5].terminator {
        *callee = "clean_origin_wf_rec::predSpelling".into();
    }
    admit_lowering(&env, &plan, &extracted)
        .expect("the emitted `Nat::sub(&n, &1)` body is faithful to the `Nat.pred` spelling");
}

// ═══════ THE EXPORT SEAM — a library may DEFINE this def; no verdict leaves ═══════
//
// 2026-09-16. `mint_encoded_digest_for_export` refuses a WF verdict
// (`UnencodableFaithfulness` — no wire tag, deliberately), and the compiler
// used to make that refusal FATAL for the exporting crate. Measured
// consequence (wf1 probes 36b/36d/18b/18c): a crate that merely CONTAINED a
// well-founded def could not be built as a library. The seam's refusal now
// converts — for that ONE variant — into a `NonExportableNotice`, the row the
// compiler exports in the certificate's place. These two tests pin both halves
// through the REAL seam over this file's measured emission: the honest body
// yields a notice that is not evidence, and a mistranslated body yields NO
// notice, so the fatal stays where it was.

/// A kernel-checked status with an audited-EMPTY closure — the honest status
/// of `countdownSum`, which rests on nothing.
fn certified_status() -> KernelStatus {
    CicKernelRecheck::held_by_kernel_recheck()
        .kernel_checked(TermDigest::of_bytes(b"control-8-export-seam"), AxiomClosure::audited([]))
}

#[test]
fn control_8_the_export_seam_yields_a_notice_and_never_a_certificate() {
    let env = env_with_cds();
    let refusal = mint_encoded_digest_for_export(
        &env,
        "countdownSum",
        &certified_status(),
        &emitted_countdown_sum(),
    )
    .expect_err(
        "A WELL-FOUNDED VERDICT CROSSED THE EXPORT SEAM: the wire has no tag for \
         `WellFoundedFunctionalDefeq`, so bytes here mean it was relabelled as something else",
    );
    assert!(
        matches!(
            refusal,
            ExportDigestRefusal::Mint(DigestMintRefusal::UnencodableFaithfulness {
                method: FaithfulnessMethod::WellFoundedFunctionalDefeq,
                ..
            })
        ),
        "the seam must get all the way to the wire spelling and refuse THERE — i.e. after \
         re-earning a fresh Faithful against the serialized body; got {refusal:?}"
    );
    assert!(
        !refusal.is_compiler_defect(),
        "a known format boundary is not the pipeline disagreeing with itself — labelling it \
         `internal: … please report` is the misdirection probe 36b recorded"
    );

    let notice = refusal
        .non_exportable_notice()
        .expect("the ONE refusal that converts into a non-exportable row");
    assert_eq!(notice.decl(), "countdownSum");
    assert_eq!(
        notice.reason(),
        &NonExportableReason::UnspellableFaithfulness {
            evidence_form: "WellFoundedFunctionalDefeq".to_owned()
        },
        "the evidence form travels as diagnostic TEXT, never as a tag"
    );

    // The row is NOT a certificate: the digest decoder refuses it on the magic,
    // so an importer that has never heard of notices fails closed …
    let row = notice.encode();
    assert!(
        VerdictDigest::decode(&row).is_err(),
        "A NOTICE DECODED AS A VERDICT DIGEST — the importer would proceed to readmission"
    );
    // … and one that has recognises it, and can only refuse.
    assert_eq!(NonExportableNotice::recognize(&row), Some(Ok(notice)));
}

/// THE CLOSE NEGATIVE TWIN. Same declaration, same status, same seam — but the
/// serialized body's zero arm materialises 1 where the definition says 0. That
/// is a wrong binary, not a format boundary, and it must NOT be launderable
/// into "non-exportable": no notice, still a compiler defect, still fatal at
/// the compiler's export provider.
#[test]
fn control_8_a_mistranslated_body_gets_no_notice_at_the_export_seam() {
    let env = env_with_cds();
    let mut mutant = emitted_countdown_sum();
    if let Terminator::Call { args, .. } = &mut mutant.body.blocks[2].terminator {
        *args = vec![Operand::Constant(ConstValue::Uint(1, 64))];
    }
    let refusal =
        mint_encoded_digest_for_export(&env, "countdownSum", &certified_status(), &mutant)
            .expect_err("the seam re-gates the body being serialized; a wrong one must refuse");
    assert!(
        matches!(refusal, ExportDigestRefusal::Emit(EmitRefusal::LoweringShapeMismatch { .. })),
        "expected the structural catch through the seam, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect());
    assert!(
        refusal.non_exportable_notice().is_none(),
        "A WRONG BODY WAS OFFERED A NON-EXPORTABLE ROW: the defining crate would then build \
         and RUN the mistranslation locally with the export seam's re-gate silenced"
    );

    // And a status that is not a kernel verdict gets none either — the notice
    // is for a def that passed everything EXCEPT the wire spelling.
    let refusal = mint_encoded_digest_for_export(
        &env,
        "countdownSum",
        &KernelStatus::Parsed,
        &emitted_countdown_sum(),
    )
    .expect_err("a parse is not a kernel verdict");
    assert!(
        matches!(refusal, ExportDigestRefusal::Mint(DigestMintRefusal::NotKernelChecked { .. })),
        "got {refusal:?}"
    );
    assert!(refusal.non_exportable_notice().is_none());
}
