// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 5 — THE WRAPPING-BINOP EMITTER MUTATION FIXTURE.**
//!
//! `control_3` is the emitter-mutation discipline pointed at the `Projection`
//! arm. This file is the same discipline pointed at
//! [`CleanOriginShape::WrappingBinOp`] — the second emittable shape, landed
//! 2026-08-19 on the kernel measurements in `fragment_widening_probes.rs`
//! (probes a/a2/b/c/d, and a4–a6 for numeral operands, measured BEFORE this
//! arm existed).
//!
//! The route and the soundness argument are control_3's, unchanged:
//!
//! ```text
//! emitted body (as read back out of MIR by trust_mir_extract)
//!   -> trust_types::recognize_admissible_body            (Arithmetic)
//!   -> trust_spec_elab::admit_expr_function              (side B, "p0 + p1")
//!   -> check_faithful                                    (against side A)
//! ```
//!
//! and the mutation is injected into **the emitted body**, never into side B,
//! so what is measured is that a mistranslating emitter cannot pass the gate.
//! The `VerifiableFunction`s are hand-built in the exact extracted shape the
//! probes already use (`WADD`/`WSUB`/`WMUL` marker strings) — the decision
//! procedure under test, `admit_lowering`, takes the extractor's output type,
//! and whether the real emitter produces this MIR is the compiler lane's
//! question (`tests/ui/trust/clean_origin_wrapping_binop.rs`).
//!
//! # DOUBLE-FAULT STRUCTURE, stated so an edit cannot quietly break it
//!
//! A swap bug in `render_wrapping_binop` ALONE is caught by the structural
//! plan-vs-recognizer check (halves 2/4/5); a de Bruijn inversion in side-A
//! recognition ALONE is caught by the kernel (halves 3/4/5's kernel halves);
//! only both together admit a wrong binary — the same fault structure the
//! projection lane already accepts, pinned per half below.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` and `trust_spec_elab::admit_*_function` are
//! frozen against this lane, exactly as for control_3. If a mutated body ever
//! passes, the defect is in the emitter or the gate — never in this fixture.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, admit_lowering, check_faithful,
    plan_clean_origin_body,
};
use trust_types::admissible_body::{ArithBinOp, ArithOperand};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A helpers ─────────────────────────────

fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

fn uint32() -> Expr {
    Expr::const_(Name::from_string("UInt32"), vec![])
}

fn env_uint() -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith().expect("UInt8/16/32/64 + arithmetic must init");
    env
}

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e:?}"));
}

fn u64_arrows(n: usize) -> Expr {
    (0..n).fold(uint64(), |acc, _| Expr::arrow(uint64(), acc))
}

/// `UInt64.<op> lhs rhs` — the carrier spelling.
fn carrier_op(op: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(&format!("UInt64.{op}")), vec![]), [lhs, rhs])
}

/// `HAdd.hAdd UInt64 UInt64 UInt64 <inst> lhs rhs` — the surface spelling,
/// with the instance constant a parameter so half_10 can route through a
/// NON-prelude instance.
fn surface_add_via(inst: &str, lhs: Expr, rhs: Expr) -> Expr {
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    Expr::apps(
        Expr::const_(Name::from_string("HAdd.hAdd"), zero3),
        [uint64(), uint64(), uint64(), Expr::const_(Name::from_string(inst), vec![]), lhs, rhs],
    )
}

/// `UInt64.ofNat n` — the carrier numeral.
fn carrier_lit(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt64.ofNat"), vec![]), Expr::nat_lit(n))
}

/// `def wsum (a b : UInt64) : UInt64 := UInt64.add a b`, kernel-checked.
fn env_with_wsum() -> Environment {
    let mut env = env_uint();
    define(
        &mut env,
        "wsum",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                carrier_op("add", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    env
}

/// `def wdiff (a b : UInt64) : UInt64 := UInt64.sub a b`, kernel-checked.
fn env_with_wdiff() -> Environment {
    let mut env = env_uint();
    define(
        &mut env,
        "wdiff",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                carrier_op("sub", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    env
}

/// `def winc6 (a : UInt64) : UInt64 := UInt64.add a (UInt64.ofNat 6)`.
fn env_with_winc6() -> Environment {
    let mut env = env_uint();
    define(
        &mut env,
        "winc6",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), carrier_op("add", Expr::bvar(0), carrier_lit(6))),
    );
    env
}

// ─────────────── the emitter's MIR, as extracted, and mutants ───────────────

const WADD: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
const WSUB: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub";
const WADD32: &str = "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_add";

fn locals(n: usize, ty: Ty) -> Vec<LocalDecl> {
    (0..n).map(|index| LocalDecl { index, ty: ty.clone(), name: None }).collect()
}

fn vf(
    name: &str,
    arg_count: usize,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("crate::m::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn prim_call(callee: &str, args: Vec<Operand>, dest: Place, target: BlockId) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        unwind: UnwindEdge::Unreachable,
    }
}

/// The two-block call shape the emitter produces, at the given local type.
fn emitted_binop_at(
    name: &str,
    callee: &str,
    args: Vec<Operand>,
    arg_count: usize,
    ty: Ty,
) -> VerifiableFunction {
    vf(
        name,
        arg_count,
        locals(arg_count + 1, ty),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: prim_call(callee, args, Place::local(0), BlockId(1)),
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

fn emitted_binop(
    name: &str,
    callee: &str,
    args: Vec<Operand>,
    arg_count: usize,
) -> VerifiableFunction {
    emitted_binop_at(name, callee, args, arg_count, Ty::u64())
}

fn copy_arg(i: usize) -> Operand {
    Operand::Copy(Place::local(i))
}

/// Reflect a spec-syntax body directly through the frozen expr mint — the
/// kernel half of a mutation, bypassing the structural check on purpose so
/// the KERNEL's own verdict is measured (control_3 half_3's rationale).
fn reflect_expr(env: &Environment, body: &str, n_params: usize) -> Expr {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut scratch = env.clone();
    let name = "control5_reflection";
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        name,
        body,
        &name_refs,
        &trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
    )
    .unwrap_or_else(|e| panic!("`{body}` must reflect: {e}"));
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .expect("a minted definition carries a value")
}

fn u64_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_at(&uint64(), &Ty::u64())
        .expect("UInt64 -> u64 is the exact-width carrier")
}

// ═══════════════════════════════ the halves ═══════════════════════════════

#[test]
fn half_0_the_plan_reads_both_spellings_as_the_same_shape() {
    let mut env = env_with_wsum();
    define(
        &mut env,
        "wsum_s",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_add_via("instHAddUInt64", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    let expected = CleanOriginShape::WrappingBinOp {
        op: ArithBinOp::Add,
        left: ArithOperand::Param(0),
        right: ArithOperand::Param(1),
    };
    for name in ["wsum", "wsum_s"] {
        let plan = plan_clean_origin_body(&env, name).expect("a single wrapping op plans");
        assert_eq!(plan.shape(), &expected, "`{name}` must read as `a + b`");
        assert_eq!(plan.signature().arity(), 2);
        assert_eq!(plan.return_ty(), &Ty::u64());
    }
}

#[test]
fn half_1_the_gate_admits_the_faithful_emission() {
    let env = env_with_wsum();
    let plan = plan_clean_origin_body(&env, "wsum").expect("plannable");

    let emitted = emitted_binop("wsum", WADD, vec![copy_arg(1), copy_arg(2)], 2);
    let admitted = admit_lowering(&env, &plan, &emitted)
        .expect("`wrapping_add(_1, _2)` IS `UInt64.add a b`; the gate must admit it");
    assert_eq!(admitted.name(), "wsum");
    assert_eq!(
        admitted.admitted_at(),
        &Ty::u64(),
        "admitted AT THE CARRIER TYPE, never the Clean type"
    );
}

#[test]
fn half_1b_the_gate_admits_the_faithful_NUMERAL_operand_emission() {
    // The positive Const-operand half the plan review required: the numeral
    // kernel ADMIT (probe a4) exercised through the full round trip, not only
    // at the bare kernel comparison.
    let env = env_with_winc6();
    let plan = plan_clean_origin_body(&env, "winc6").expect("plannable");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(6),
        }
    );

    let emitted = emitted_binop(
        "winc6",
        WADD,
        vec![copy_arg(1), Operand::Constant(ConstValue::Uint(6, 64))],
        1,
    );
    let admitted = admit_lowering(&env, &plan, &emitted)
        .expect("`wrapping_add(_1, const 6)` IS `UInt64.add a (UInt64.ofNat 6)`");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
}

#[test]
fn half_2_an_emitter_that_emitted_the_WRONG_OP_is_refused() {
    let env = env_with_wsum();
    let plan = plan_clean_origin_body(&env, "wsum").expect("plannable");

    // ONE construct changed: the callee is wrapping_sub. Same blocks, same
    // operands, same types — a body computing `a - b` for a def that says
    // `a + b`.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_binop("wsum", WSUB, vec![copy_arg(1), copy_arg(2)], 2),
    )
    .expect_err(
        "THE GATE IS DECORATION IF THIS PASSES: a body computing `a - b` was accepted \
         for a definition that says `a + b` — a WRONG BINARY. Do NOT fix this by \
         editing side B's producers; they are frozen against this lane.",
    );
    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect: {refusal:?}");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "the structural catch fires first; got {refusal:?}"
    );
}

#[test]
fn half_3_the_kernel_alone_catches_the_wrong_op_too() {
    // half_2 is the STRUCTURAL catch. Put the same mutation to the kernel
    // directly: reflect `p0 - p1` through the frozen producers and compare it
    // against `wsum`. If the kernel identifies `a + b` with `a - b`,
    // everything above is theatre. (Probe a3 measures the same fact; it is
    // re-pinned here under this control's honesty rules so the control stands
    // alone.)
    let env = env_with_wsum();
    let wrong = reflect_expr(&env, "p0 - p1", 2);
    let refusal = check_faithful(&env, "wsum", &wrong, &u64_carrier())
        .expect_err("the kernel must separate `a + b` from `a - b`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_4_an_operand_SWAP_on_the_noncommutative_op_is_refused_by_both_layers() {
    let env = env_with_wdiff();
    let plan = plan_clean_origin_body(&env, "wdiff").expect("plannable");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        }
    );

    // Structural half: emitted wrapping_sub(_2, _1) — an argument-order bug.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_binop("wdiff", WSUB, vec![copy_arg(2), copy_arg(1)], 2),
    )
    .expect_err("`b - a` emitted for a def that says `a - b` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half: the swapped reflection alone.
    let refusal = check_faithful(&env, "wdiff", &reflect_expr(&env, "p1 - p0", 2), &u64_carrier())
        .expect_err("the kernel must separate `a - b` from `b - a`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_5_a_WRONG_NUMERAL_is_refused_by_both_layers() {
    let env = env_with_winc6();
    let plan = plan_clean_origin_body(&env, "winc6").expect("plannable");

    // Structural half: the emitter baked in 7 where the def says 6.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_binop(
            "winc6",
            WADD,
            vec![copy_arg(1), Operand::Constant(ConstValue::Uint(7, 64))],
            1,
        ),
    )
    .expect_err("a wrong constant is a wrong binary and must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half: `p0 + 7` against `a + 6`.
    let refusal = check_faithful(&env, "winc6", &reflect_expr(&env, "p0 + 7", 1), &u64_carrier())
        .expect_err("the kernel must separate `a + 6` from `a + 7`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_6_an_UNMARKED_callee_is_refused() {
    // Marker authentication is load-bearing in the round trip: a callee
    // without the compiler-authenticated primitive marker — however plausible
    // its name — must not recognize, so the round trip refuses BEFORE any
    // reflection happens.
    let env = env_with_wsum();
    let plan = plan_clean_origin_body(&env, "wsum").expect("plannable");

    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_binop("wsum", "my_crate::wrapping_add", vec![copy_arg(1), copy_arg(2)], 2),
    )
    .expect_err("an unmarked callee must never be treated as the core primitive");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "the recognizer itself must refuse the unmarked callee; got {refusal:?}"
    );
}

#[test]
fn half_7_the_natural_lowering_trap_a_BinaryOp_body_is_refused() {
    // The emitter MUST emit the authenticated call. An emitter that
    // "simplified" to `_0 = Add(_1, _2)` — the body ordinary Rust `a + b`
    // lowers to — is refused, not silently admitted: `recognize_arithmetic`
    // has no `Rvalue::BinaryOp` arm, by measurement. This pins that the
    // constraint holds, so a future "optimization" of the emitter surfaces
    // here instead of in a binary.
    let env = env_with_wsum();
    let plan = plan_clean_origin_body(&env, "wsum").expect("plannable");

    let body = vf(
        "wsum",
        2,
        locals(3, Ty::u64()),
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(BinOp::Add, copy_arg(1), copy_arg(2)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    );
    let refusal = admit_lowering(&env, &plan, &body)
        .expect_err("a bare BinaryOp body is not the authenticated-call shape");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }), "got {refusal:?}");
}

#[test]
fn half_8_an_emission_at_the_WRONG_WIDTH_is_refused_by_the_kernel() {
    // The binop analogue of control_3 half_5b: u32 locals and the u32 callee
    // for a UInt64 def. The body is a perfectly valid `fn(u32, u32) -> u32`
    // wrapping add — it recognizes, the shapes agree structurally, it
    // reflects at UInt32 — and it TRUNCATES every value the declaration talks
    // about. Only the kernel comparison at the emitted width can see that.
    let env = env_with_wsum();
    let plan = plan_clean_origin_body(&env, "wsum").expect("plannable");

    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_binop_at(
            "wsum",
            WADD32,
            vec![copy_arg(1), copy_arg(2)],
            2,
            Ty::Int { width: 32, signed: false },
        ),
    )
    .expect_err("a u32 body emitted for a UInt64 declaration truncates and must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::Gate(GateRefusal::Disagreement { .. })),
        "the width mistake must be caught by the KERNEL comparison — no structural check \
         above it can see a truncation; got {refusal:?}"
    );
}

#[test]
fn half_9_a_MIXED_WIDTH_signature_refuses_at_plan_time() {
    // The single-domain constraint, pinned on the case that actually planned:
    // `def skew (a : UInt32) (b c : UInt64) : UInt64 := UInt64.add b c`. The
    // BODY is a perfectly recognizable single op over two UInt64 parameters;
    // the UNUSED `a : UInt32` is what makes the signature unemittable, because
    // the reflected side B (`admit_expr_function`) is single-domain over ALL
    // parameters — a mixed-width side A can never be identified with any
    // mintable side B. (A mixed-width OPERAND cannot even be written without
    // a heterogeneous instance, which half_10's boundary already refuses; the
    // unused-parameter case is the one that would otherwise slip through.)
    let mut env = env_uint();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("skew"),
        level_params: vec![],
        type_: Expr::arrow(uint32(), Expr::arrow(uint64(), Expr::arrow(uint64(), uint64()))),
        // Under 3 binders: b = bvar 1, c = bvar 0.
        value: Expr::lam(
            BinderInfo::Default,
            uint32(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                Expr::lam(
                    BinderInfo::Default,
                    uint64(),
                    carrier_op("add", Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("`skew` is well-typed");

    let refusal = plan_clean_origin_body(&env, "skew")
        .expect_err("a mixed-width signature must refuse AT PLAN TIME");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(
        !refusal.is_compiler_defect(),
        "a fragment boundary is user-actionable, never an internal error"
    );
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(
        note.contains("EVERY signature position"),
        "the refusal must state the single-domain rule it enforces: {note}"
    );
}

#[test]
fn half_10_a_NON_PRELUDE_instance_is_a_capability_refusal() {
    // `def myInstHAdd : HAdd UInt64 UInt64 UInt64 := instHAddUInt64` is
    // well-typed, kernel-reducible to the prelude instance, and a def spelled
    // through it would even pass defeq. It is refused at RECOGNITION anyway,
    // as a capability boundary: only the prelude's homogeneous instance is in
    // the measured fragment, and tunneling an unknown instance into the
    // internal-error family would tell the user to report a compiler bug that
    // is actually a spelling boundary.
    let mut env = env_uint();
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    define(
        &mut env,
        "myInstHAdd",
        Expr::apps(Expr::const_(Name::from_string("HAdd"), zero3), [uint64(), uint64(), uint64()]),
        Expr::const_(Name::from_string("instHAddUInt64"), vec![]),
    );
    define(
        &mut env,
        "via_my_inst",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_add_via("myInstHAdd", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );

    let refusal = plan_clean_origin_body(&env, "via_my_inst")
        .expect_err("a non-prelude instance is outside the measured fragment");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a capability refusal, never an internal error");
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(
        note.contains("instHAddUInt64"),
        "the refusal must name the prelude instance that IS in the fragment: {note}"
    );
}

#[test]
fn half_11_an_OUT_OF_RANGE_numeral_refuses_naming_the_range() {
    // `def big (a : UInt64) : UInt64 := UInt64.add a (UInt64.ofNat 2^64)`.
    // Kernel-checks fine — `ofNat` wraps, and emitting `0` would even be
    // defeq-faithful — but the claim is subtle and the honest answer is a
    // refusal that names the range. Fail-closed costs capability, never
    // soundness.
    let mut env = env_uint();
    define(
        &mut env,
        "big",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            carrier_op(
                "add",
                Expr::bvar(0),
                Expr::app(
                    Expr::const_(Name::from_string("UInt64.ofNat"), vec![]),
                    Expr::nat_lit_u128(1u128 << 64),
                ),
            ),
        ),
    );

    let refusal = plan_clean_origin_body(&env, "big")
        .expect_err("an out-of-range numeral must refuse, never silently reduce");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(
        note.contains("0..2^64"),
        "the refusal must name the range the literal must fit: {note}"
    );
    assert!(
        note.contains("will not silently reduce"),
        "the refusal must state the non-reduction rule: {note}"
    );
}
