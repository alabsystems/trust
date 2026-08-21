// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 3 — THE EMITTER MUTATION FIXTURE.**
//!
//! `tests/control_2_frozen_r_mutation.rs` established that the gate catches a
//! one-construct mistranslation *when side B is handed to it directly*. It
//! stated its own limit honestly:
//!
//! > Side B is constructed directly here rather than produced by a Clean->MIR
//! > lowering, **because no such lowering exists**. […] When the lowering
//! > lands, it feeds side B and this control becomes an end-to-end one with no
//! > change to the gate.
//!
//! **The lowering has landed** (`crate::emit`), so this is that control. It is
//! control 2's harness pointed at the real route:
//!
//! ```text
//! emitted body (as read back out of MIR by trust_mir_extract)
//!   -> trust_types::recognize_admissible_body
//!   -> trust_spec_elab::admit_projection_function   (side B)
//!   -> check_faithful                                (against side A)
//! ```
//!
//! and the mutation is injected into **the emitted body**, not into side B, so
//! what is measured is that a mistranslating emitter cannot get past the gate.
//!
//! # WHY THE `VerifiableFunction`S HERE ARE HAND-BUILT, AND WHY THAT IS SOUND
//!
//! `trust_mir_extract::extract_function` needs a `TyCtxt`, so it cannot run on
//! this lane. The bodies below are therefore written in the shape the extractor
//! produces for `fn fst(x: u64, y: u64) -> u64 { x }` — one block, `_0 = move
//! _1`, `return` — which is exactly `tests/e6-fragment-probe/probes/
//! d01_projection_u64.rs`'s measured MIR.
//!
//! That hand-construction is a limit on what this file measures and NOT a hole
//! in the gate, because the *decision procedure under test is the same object*
//! the compiler calls: `admit_lowering` takes the extractor's output type.
//! Whether the compiler's emitter really produces this MIR is measured on the
//! compiler lane, by `tests/ui/trust/clean_origin_*.rs`. What is measured HERE
//! is that if it produced a *different* body, `admit_lowering` would refuse —
//! and that is the property that makes the compiler lane's green meaningful.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` and `trust_spec_elab::admit_*_function` were
//! written for the E6 Rust->Clean direction and are frozen against this lane in
//! exactly the way `crates/trust-clean/src/reflect.rs` is. If a mutated body
//! ever passes, the defect is in the emitter or the gate — never in this
//! fixture. Do not weaken an assertion and do not delete a case.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_clean_origin::{
    admit_lowering, plan_clean_origin_body, CleanOriginShape, EmitRefusal, GateRefusal,
};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

/// `UInt64`, the Clean fixed-width type that carries exactly.
fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

/// An environment holding
/// `def fst_isl (x : UInt64) (y : UInt64) : UInt64 := x`,
/// inserted through the FULL kernel check.
///
/// This is `d01_projection_u64.rs`'s island, verbatim — the probe corpus's
/// measured baseline for the one shape the kernel admits under defeq against a
/// reflected lowering.
fn env_with_fst() -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith().expect("UInt8/16/32/64 must initialize");

    // `fun (x : UInt64) (y : UInt64) => x`. Under two binders the SOURCE
    // parameter 0 is de Bruijn index 1.
    let body = Expr::lam(
        BinderInfo::Default,
        uint64(),
        Expr::lam(BinderInfo::Default, uint64(), Expr::bvar(1)),
    );

    env.add_decl(Declaration::Definition {
        name: Name::from_string("fst_isl"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        value: body,
        is_reducible: true,
    })
    .expect("`fst_isl` is a well-typed UInt64 -> UInt64 -> UInt64 definition");

    env
}

/// The body `fn fst(x: u64, y: u64) -> u64 { x }` lowers to, in the shape
/// `trust_mir_extract::extract_function` reports it: one block,
/// `_0 = move _{param+1}`, `return`.
///
/// `param` is the parameter the emitted code actually returns — the knob the
/// mutation turns.
fn emitted_projection(param: usize) -> VerifiableFunction {
    VerifiableFunction {
        name: "fst_isl".into(),
        def_path: "crate::m::fst_isl".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: (0..3).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(param + 1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

#[test]
fn half_0_the_plan_reads_the_clean_def_as_a_projection_of_parameter_0() {
    let env = env_with_fst();
    let plan = plan_clean_origin_body(&env, "fst_isl")
        .expect("a kernel-checked UInt64 projection must be plannable");

    assert_eq!(plan.name(), "fst_isl");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::Projection { projected: 0 },
        "`fun x y => x` is SOURCE parameter 0. Under two binders that is de Bruijn 1, and \
         reporting `projected: 1` here would mean the compiler had inverted de Bruijn \
         indices — the exact mistake half_2 exists to catch downstream"
    );
    assert_eq!(plan.signature().arity(), 2);
    assert_eq!(plan.param_tys(), vec![Ty::u64(), Ty::u64()]);
    assert_eq!(plan.return_ty(), &Ty::u64());
}

#[test]
fn half_1_the_gate_admits_the_faithful_emission() {
    let env = env_with_fst();
    let plan = plan_clean_origin_body(&env, "fst_isl").expect("plannable");

    let admitted = admit_lowering(&env, &plan, &emitted_projection(0))
        .expect("`_0 = move _1` IS `fun x y => x`; the gate must admit it");

    assert_eq!(admitted.name(), "fst_isl");
    assert_eq!(
        admitted.admitted_at(),
        &Ty::u64(),
        "the agreement must be admitted AT THE CARRIER TYPE (`u64`), never at the Clean \
         type — I4 exists because those two can disagree while defeq is satisfied"
    );
}

#[test]
fn half_2_the_gate_catches_an_emitter_that_projects_the_wrong_parameter() {
    let env = env_with_fst();
    let plan = plan_clean_origin_body(&env, "fst_isl").expect("plannable");

    // ONE construct changed: `_0 = move _1` becomes `_0 = move _2`. Same block
    // count, same terminator, same arity, same types, still a perfectly valid
    // `fn(u64, u64) -> u64`. It computes `snd` for a definition that says
    // `fst`. This is what a de Bruijn inversion in the emitter looks like from
    // the outside, and it is the mistranslation this lane can actually make.
    let refusal = admit_lowering(&env, &plan, &emitted_projection(1)).expect_err(
        "THE GATE IS DECORATION IF THIS PASSES. A body that returns `y` was accepted for a \
         definition that says `x`, which is a WRONG BINARY — the one outcome on this lane \
         that is worse than a failed build. Do NOT make this test pass by editing \
         `trust_types::admissible_body` or `trust_spec_elab::admit_*_function`: those are \
         side B's producers and they are frozen against this lane.",
    );

    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect, not a \
        user error; {refusal:?}");
    assert_eq!(refusal.name(), "fst_isl");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the planned/emitted shape disagreement; got {refusal:?}"
    );
}

#[test]
fn half_3_the_kernel_comparison_alone_catches_it_too() {
    // half_2's refusal is the STRUCTURAL catch, which fires first because the
    // plan and the recognizer disagree. That is a fine defence but it is not
    // the gate, and a control that only exercised it would prove nothing about
    // whether the KERNEL can tell the two bodies apart.
    //
    // So put the same mutation to `check_faithful` directly, by reflecting the
    // WRONG body through the same E6 producers the emitter route uses and
    // comparing it against side A. If the kernel identifies `fun x y => x` with
    // `fun x y => y`, everything above is theatre.
    let env = env_with_fst();

    let mut scratch = env.clone();
    trust_spec_elab::admit_projection_function(
        &mut scratch,
        "wrong_lowering",
        &[
            trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
            trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
        ],
        1, // the WRONG parameter
    )
    .expect("the reflected `snd` is well-typed; the kernel accepts it as a definition");

    let side_b = scratch
        .get_const(&Name::from_string("wrong_lowering"))
        .and_then(|c| c.value.clone())
        .expect("a minted projection definition carries a value");

    let carrier = trust_clean_carrier::carrier_at(&uint64(), &Ty::u64())
        .expect("UInt64 -> u64 is the exact-width carrier");

    let refusal = trust_clean_origin::check_faithful(&env, "fst_isl", &side_b, &carrier)
        .expect_err(
            "THE PREMISE OF THIS LANE FAILED: the kernel identified `fun x y => x` with \
             `fun x y => y`. If this ever passes, definitional equality is not deciding \
             the question and no structural check above it can be trusted to.",
        );

    assert!(
        matches!(refusal, GateRefusal::Disagreement { .. }),
        "expected a kernel disagreement; got {refusal:?}"
    );
}

#[test]
fn half_4_an_emitted_body_that_is_not_a_projection_at_all_is_refused() {
    // The emitter producing a body the recognizer cannot read is a different
    // failure from producing the wrong projection, and it must also refuse
    // rather than emit something unchecked. `_0 = move _1` replaced by a
    // constant: still one block, still returning, still type-correct.
    let env = env_with_fst();
    let plan = plan_clean_origin_body(&env, "fst_isl").expect("plannable");

    let mut wrong = emitted_projection(0);
    wrong.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(7, 64))),
        span: SourceSpan::default(),
    }];

    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a constant body is not `fun x y => x` and must never be emitted for it");

    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected a shape mismatch; got {refusal:?}"
    );
}

#[test]
fn half_5_an_emitted_body_whose_arity_disagrees_with_the_signature_is_refused() {
    let env = env_with_fst();
    let plan = plan_clean_origin_body(&env, "fst_isl").expect("plannable");

    // Same statement, but the body claims ONE parameter. `Projection { param: 0 }`
    // still recognises, so the structural shape agrees — the arity is the only
    // disagreement, and it must be enough to refuse: a call site would pass two
    // arguments to a one-parameter body.
    let mut wrong = emitted_projection(0);
    wrong.body.arg_count = 1;

    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("an arity disagreement between the signature and the emitted body \
                     must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected a shape mismatch; got {refusal:?}"
    );
}

#[test]
fn half_5b_an_emitted_body_at_the_WRONG_CARRIER_WIDTH_is_refused() {
    // THE MISTRANSLATION THE TYPE MAPPING MAKES POSSIBLE, and the reason the
    // round trip reads the emitted body's own local types instead of the plan's.
    //
    // `clean_origin_mir::carrier_to_rustc_ty` turns the I4 carrier into the
    // rustc type the emitted locals get. If it mapped `UInt64` to `u32`, the
    // emitted body would be a perfectly valid `fn(u32, u32) -> u32` projection —
    // one block, right parameter, right shape — that TRUNCATES every value the
    // declaration talks about. No structural check can see that; only the
    // carrier can.
    //
    // The loop that catches it: carrier -> rustc `Ty` -> (extractor) ->
    // `trust_types::Ty` -> `Domain` -> side B at `UInt32`, compared against side
    // A at `UInt64`. If this test ever passes, that loop has been broken open
    // somewhere and a width mistake reaches the binary.
    let env = env_with_fst();
    let plan = plan_clean_origin_body(&env, "fst_isl").expect("plannable");

    let mut wrong = emitted_projection(0);
    wrong.body.return_ty = Ty::Int { width: 32, signed: false };
    for local in &mut wrong.body.locals {
        local.ty = Ty::Int { width: 32, signed: false };
    }

    let refusal = admit_lowering(&env, &plan, &wrong).expect_err(
        "a body emitted at u32 for a UInt64 declaration TRUNCATES, and definitional \
         equality at the wrong carrier is not agreement",
    );
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::Gate(GateRefusal::Disagreement { .. })),
        "the width mistake must be caught by the KERNEL comparison — no structural check \
         above it can see a truncation; got {refusal:?}"
    );
}

#[test]
fn half_5c_a_mixed_width_projection_plans_and_admits_at_the_RIGHT_positions() {
    // The positive control on `half_5b`, and on `param_tys()`. A same-width
    // signature cannot distinguish "the carriers were read positionally" from
    // "one carrier was read and repeated", so a projection over DIFFERENT
    // widths is what pins the positions.
    //
    // `def snd32_64 (x : UInt32) (y : UInt64) : UInt64 := y` — the emitted body
    // must be `fn(u32, u64) -> u64 { _0 = move _2 }`.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    let u32_ty = Expr::const_(Name::from_string("UInt32"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("snd32_64"),
        level_params: vec![],
        type_: Expr::arrow(u32_ty.clone(), Expr::arrow(uint64(), uint64())),
        // `fun (x : UInt32) (y : UInt64) => y`: source parameter 1 is de Bruijn 0.
        value: Expr::lam(
            BinderInfo::Default,
            u32_ty,
            Expr::lam(BinderInfo::Default, uint64(), Expr::bvar(0)),
        ),
        is_reducible: true,
    })
    .expect("`snd32_64` is well-typed");

    let plan = plan_clean_origin_body(&env, "snd32_64").expect("plannable");
    assert_eq!(plan.shape(), &CleanOriginShape::Projection { projected: 1 });
    assert_eq!(
        plan.param_tys(),
        vec![Ty::Int { width: 32, signed: false }, Ty::u64()],
        "the argument carriers must be read POSITIONALLY; a repeated carrier would make \
         this `[u64, u64]` and the emitted first parameter would be the wrong width"
    );
    assert_eq!(plan.return_ty(), &Ty::u64());

    // The body the emitter must produce for that plan.
    let mut emitted = emitted_projection(1);
    emitted.name = "snd32_64".into();
    emitted.body.locals[1].ty = Ty::Int { width: 32, signed: false };

    let admitted = admit_lowering(&env, &plan, &emitted)
        .expect("`_0 = move _2` over (u32, u64) IS `fun x y => y`");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
}

#[test]
fn half_6_a_body_less_declaration_cannot_be_planned() {
    // An axiom asserts a type without exhibiting a value. There is nothing to
    // emit and nothing to be faithful to, so the refusal must happen at PLAN
    // time — before any MIR is constructed — not at gate time.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("assumed"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), uint64()),
    })
    .expect("an axiom of function type is admissible");

    let refusal = plan_clean_origin_body(&env, "assumed")
        .expect_err("an axiom has no body and must never acquire an emitted one");
    assert!(
        matches!(refusal, EmitRefusal::NotEmittable { .. }),
        "expected NotEmittable; got {refusal:?}"
    );
    assert!(!refusal.is_compiler_defect(), "an axiom is a user-facing capability boundary");
    assert!(
        refusal.note().contains("options:"),
        "ruling v7/D3: a refusal must carry the fix, with options"
    );
}

#[test]
fn half_7_arithmetic_now_PLANS_and_the_boundary_moved_to_division() {
    // `def double (a : UInt64) : UInt64 := UInt64.add a a` — control 2's
    // definition. Until 2026-08-19 this half pinned it as OUTSIDE the
    // emittable fragment; `CleanOriginShape::WrappingBinOp` landed, so the pin
    // flips in the same commit as the variant (this file's own rule): the
    // planner must now read it as the single-op shape, with the SAME
    // parameter on both sides.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    let a = Expr::bvar(0);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("double"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), uint64()),
        value: Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("UInt64.add"), vec![]), a.clone()),
                a,
            ),
        ),
        is_reducible: true,
    })
    .expect("`double` is admissible");

    let plan = plan_clean_origin_body(&env, "double")
        .expect("a single wrapping op over one parameter is inside the fragment now");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: trust_types::admissible_body::ArithBinOp::Add,
            left: trust_types::admissible_body::ArithOperand::Param(0),
            right: trust_types::admissible_body::ArithOperand::Param(0),
        },
        "`fun a => UInt64.add a a` is `a + a` — the same source parameter twice"
    );

    // Until 2026-08-20 the fragment-boundary pin sat on the NESTED shape —
    // `def nested (a b : UInt64) : UInt64 := (a + b) * a`. `CleanOriginShape::
    // Composed` landed, so that pin FLIPS in the same commit as the variant
    // (this file's own rule): the planner must now read the nesting as the
    // composed tree.
    let b = |i: u32| Expr::bvar(i);
    let op = |name: &str, lhs: Expr, rhs: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(&format!("UInt64.{name}")), vec![]), lhs),
            rhs,
        )
    };
    env.add_decl(Declaration::Definition {
        name: Name::from_string("nested"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        value: Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                op("mul", op("add", b(1), b(0)), b(1)),
            ),
        ),
        is_reducible: true,
    })
    .expect("`nested` is admissible");
    {
        use trust_types::admissible_body::{ArithBinOp, ArithExpr, ArithOperand};
        let plan = plan_clean_origin_body(&env, "nested")
            .expect("a nested wrapping tree is inside the fragment now (Composed, 2026-08-20)");
        assert_eq!(
            plan.shape(),
            &CleanOriginShape::Composed {
                expr: ArithExpr::Bin {
                    op: ArithBinOp::Mul,
                    left: Box::new(ArithExpr::Bin {
                        op: ArithBinOp::Add,
                        left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                        right: Box::new(ArithExpr::Operand(ArithOperand::Param(1))),
                    }),
                    right: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                },
            },
            "`fun a b => (a + b) * a` is the composed tree, de-Bruijn-inverted"
        );
    }

    // The fragment-boundary pin MOVES to DIVISION — a nested shape that stays
    // refused. No `UInt64.div` exists in the kernel prelude at all
    // (`init_uint_arith` registers add/sub/mul only), so the division that CAN
    // be spelled is at the bignum carrier: `def ndiv (a b : Nat) : Nat :=
    // Nat.mul (Nat.div a b) a`. Perfectly kernel-checked Clean; refused
    // because the wrapping-arithmetic fragment — single op OR composed —
    // exists only at the unsigned machine widths, and `Nat` is not one. The
    // honest answer is a refusal that names the boundary and the ways around
    // it (v7/D3), never a silent emission.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_op = |name: &str, lhs: Expr, rhs: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(&format!("Nat.{name}")), vec![]), lhs),
            rhs,
        )
    };
    env.add_decl(Declaration::Definition {
        name: Name::from_string("ndiv"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat,
                nat_op("mul", nat_op("div", b(1), b(0)), b(1)),
            ),
        ),
        is_reducible: true,
    })
    .expect("`ndiv` is admissible — Nat.div is a genuine structural definition");

    let refusal = plan_clean_origin_body(&env, "ndiv")
        .expect_err("division is outside the emittable fragment (MEASURED, 2026-08-20)");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(
        note.contains("cite `ndiv` from a contract"),
        "the refusal must offer proof position, which needs no carrier: {note}"
    );
    assert!(
        note.contains("emittable directly"),
        "the refusal must state the nested-composition capability that DID land, so the \
         user is not told to decompose a tree the compiler now takes whole: {note}"
    );
    assert!(
        note.contains("split it into single-op"),
        "the decomposition option must survive for what remains outside: {note}"
    );
}

#[test]
fn half_8_a_nullary_constant_is_refused_with_the_measured_reason() {
    // The corpus measurement this whole slice rests on: `ConstantUint` is the
    // shape that LOOKS simplest and is the one the kernel refuses under defeq
    // against its reflected lowering (f04, f06-f09). Planning must refuse it up
    // front rather than emitting a body that the gate would then reject, so the
    // user gets a capability message instead of an internal-error one.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("six"),
        level_params: vec![],
        type_: uint64(),
        value: Expr::app(
            Expr::const_(Name::from_string("UInt64.ofNat"), vec![]),
            Expr::nat_lit(6),
        ),
        is_reducible: true,
    })
    .expect("`six` is admissible");

    let refusal = plan_clean_origin_body(&env, "six")
        .expect_err("a nullary constant is outside the measured callable fragment");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    assert!(
        refusal.note().contains("options:"),
        "v7/D3 applies to a fragment boundary as much as to a proof failure"
    );
}

#[test]
fn half_8b_a_Nat_projection_plans_at_the_EXACT_bignum_carrier_never_a_width() {
    // THE MISCOMPILE I4 EXISTS TO MAKE UNREACHABLE, checked at the emitter.
    //
    // `fun (x y : Nat) => x` is a perfectly good projection, and the danger
    // was always the CARRIER: a shape-only planner would happily emit
    // `fn(u64, u64) -> u64 { x }`, a binary that wraps every argument above
    // 2^64-1 while the declaration talks about unbounded naturals — and
    // kernel definitional equality does NOT catch it (I4's
    // `control_b_defeq_insufficiency` executes the proof that
    // `UInt64.toNat (UInt64.ofNat (2^64))` is defeq to `0`).
    //
    // Until 2026-08-19 this half pinned the fail-closed answer: `Nat` had no
    // total carrier, so planning refused `NoTotalCarrier`. The fix this
    // half's own comment named — "per v7/D2 the fix is a bignum carrier in
    // the compiler" — has now LANDED (I6, `trust_bignum::Nat`,
    // `Ty::BignumNat`), so the pin flips in the same commit family: the plan
    // is GRANTED, and what this half now guards is the value of the grant —
    // every position must be the EXACT unbounded carrier, and a fixed-width
    // type appearing anywhere in a `Nat` plan is the miscompile coming back.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("fst_nat"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(BinderInfo::Default, nat, Expr::bvar(1)),
        ),
        is_reducible: true,
    })
    .expect("`fst_nat` is a well-typed Nat projection");

    let plan = plan_clean_origin_body(&env, "fst_nat")
        .expect("`Nat` carries at the Trust-owned bignum since I6; the projection plans");
    assert_eq!(plan.shape(), &CleanOriginShape::Projection { projected: 0 });
    assert_eq!(
        plan.param_tys(),
        vec![Ty::BignumNat, Ty::BignumNat],
        "every `Nat` position must carry at the EXACT unbounded bignum"
    );
    assert_eq!(plan.return_ty(), &Ty::BignumNat);
    assert!(
        !plan.param_tys().iter().chain([plan.return_ty()]).any(|ty| matches!(
            ty,
            Ty::Int { .. }
        )),
        "a FIXED-WIDTH type in a `Nat` plan is the wrap-into-u64 miscompile this half \
         exists to make unreachable; got {plan:?}"
    );
}

#[test]
fn half_9_an_unchecked_declaration_cannot_be_planned_even_though_it_has_a_body() {
    // Provenance is checked at PLAN time as well as at gate time. A
    // structurally-inserted declaration has a perfectly good body; what it does
    // not have is a kernel verdict, and shaping emitted MIR from it would mean
    // the emitted signature rests on something the kernel never validated.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    let body = Expr::lam(
        BinderInfo::Default,
        uint64(),
        Expr::lam(BinderInfo::Default, uint64(), Expr::bvar(1)),
    );
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("sneaky"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        value: body,
        is_reducible: true,
    })
    .expect("a structural insertion of a well-formed declaration succeeds");

    let refusal = plan_clean_origin_body(&env, "sneaky")
        .expect_err("a declaration the kernel never checked must not shape emitted code");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
}
