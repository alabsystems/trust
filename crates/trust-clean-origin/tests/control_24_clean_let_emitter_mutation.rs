// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 24 — THE `let`-BINDING EMITTER MUTATION FIXTURE**
//! (2026-09-13, W5 widening: a Rust program calling a Clean `def` whose body
//! contains a `let`).
//!
//! A `let y := v; b` is definitionally `b[y := v]` — the kernel's own zeta
//! step (`clean_kernel::tc::whnf`: `Let(_, _, val, body, _) =>
//! Continue(body.instantiate(val))`). The emitter therefore reduces every
//! PURE `let` away BEFORE recognition (`emit::zeta_normalize`, invoked from
//! `recognise_clean_shape`), so a `let`-bearing body flows into the SAME shape
//! recognisers, the SAME materializer, the SAME side-B readers and the SAME
//! faithfulness gate as its `let`-free equivalent. For PURE lets there is no
//! new `CleanOriginShape`, no new `MirShape` and no new reflect producer; a
//! `let` whose value is a RUST CALL is instead one shared `RustCallChain`
//! node, an explicit value temporary (W5 increment 7,
//! `control_27_clean_let_temp_emitter_mutation`), and never reaches this
//! file's reduction.
//!
//! ```text
//! def f (x) := let y := x + 1; y * y     side A (kernel term, with the `let`)
//!   -> emit::zeta_normalize                 (x+1)*(x+1)      (the reduced shape)
//!   -> recognise_clean_shape                Composed
//!   -> materialize / trust_mir_extract      the wrapping call chain
//!   -> recognize_admissible_body            Composed  (temp unfolded twice)
//!   -> admit_expr_function                  side B, "(p0+1)*(p0+1)"
//!   -> check_faithful                       is_def_eq vs the `let` decl (ZETA)
//! ```
//!
//! # WHY THIS IS SOUND — the reduction is never trusted
//!
//! `zeta_normalize` is a HEURISTIC that pre-computes the shape.
//! [`check_faithful`] re-decides definitional equality against the UNTOUCHED
//! declaration term the kernel stored — which the kernel zeta-reduces on its
//! own — so a wrong reduction can only produce a body that FAILS def-eq and is
//! refused fail-closed, NEVER a silently wrong binary. This file measures both
//! directions:
//!
//! * the correct reduction ADMITS (proving the kernel zeta-reduces the `let`);
//! * a body that returns the WRONG bound value, or that binds the WRONG
//!   expression, is REFUSED BY THE KERNEL GATE.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` and `trust_spec_elab::admit_*_function` are
//! frozen against this lane, exactly as for control_3/control_5. If a mutated
//! body ever passes, the defect is in the emitter or the gate — never here.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_clean_origin::{
    CleanOriginShape, GateRefusal, admit_lowering, check_faithful, plan_clean_origin_body,
};
use trust_types::admissible_body::{ArithBinOp, ArithExpr, ArithOperand};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A helpers ─────────────────────────────

fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
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

/// `UInt64.ofNat n` — the carrier numeral.
fn carrier_lit(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt64.ofNat"), vec![]), Expr::nat_lit(n))
}

/// A `let y : UInt64 := <val>; <body>`, non-dependent flag `false`.
fn let_u64(val: Expr, body: Expr) -> Expr {
    Expr::let_named(Name::from_string("y"), uint64(), val, body, false)
}

/// `def flet_id (x : UInt64) : UInt64 := let y := x; y`.
fn env_id() -> Environment {
    let mut env = env_uint();
    // Under x: BVar(0) = x. Under the let binder: BVar(0) = y, BVar(1) = x.
    let value = Expr::lam(BinderInfo::Default, uint64(), let_u64(Expr::bvar(0), Expr::bvar(0)));
    define(&mut env, "flet_id", u64_arrows(1), value);
    env
}

/// `def flet_add (x : UInt64) : UInt64 := let y := x + 1; y`.
fn env_add() -> Environment {
    let mut env = env_uint();
    let value = Expr::lam(
        BinderInfo::Default,
        uint64(),
        let_u64(carrier_op("add", Expr::bvar(0), carrier_lit(1)), Expr::bvar(0)),
    );
    define(&mut env, "flet_add", u64_arrows(1), value);
    env
}

/// `def flet_sq (x : UInt64) : UInt64 := let y := x + 1; y * y` — the value is
/// USED TWICE, so the reduced shape DUPLICATES it into `(x+1)*(x+1)`.
fn env_sq() -> Environment {
    let mut env = env_uint();
    let value = Expr::lam(
        BinderInfo::Default,
        uint64(),
        let_u64(
            carrier_op("add", Expr::bvar(0), carrier_lit(1)),
            carrier_op("mul", Expr::bvar(0), Expr::bvar(0)),
        ),
    );
    define(&mut env, "flet_sq", u64_arrows(1), value);
    env
}

/// `def flet_shadow (x : UInt64) : UInt64 := let x := x + 1; x` — the `let`
/// REBINDS the parameter name; the innermost binding must win, exactly as the
/// kernel resolves de Bruijn.
fn env_shadow() -> Environment {
    let mut env = env_uint();
    // `let x := (param x) + 1; (inner x)`: val reads BVar(0)=param, body reads
    // BVar(0)=the let-bound x.
    let value = Expr::lam(
        BinderInfo::Default,
        uint64(),
        Expr::let_named(
            Name::from_string("x"),
            uint64(),
            carrier_op("add", Expr::bvar(0), carrier_lit(1)),
            Expr::bvar(0),
            false,
        ),
    );
    define(&mut env, "flet_shadow", u64_arrows(1), value);
    env
}

/// `def flet_nested (x : UInt64) : UInt64 := let y := x; let z := y + 1; z`.
fn env_nested() -> Environment {
    let mut env = env_uint();
    let inner = Expr::let_named(
        Name::from_string("z"),
        uint64(),
        carrier_op("add", Expr::bvar(0), carrier_lit(1)), // y + 1
        Expr::bvar(0),                                    // z
        false,
    );
    let value = Expr::lam(
        BinderInfo::Default,
        uint64(),
        let_u64(Expr::bvar(0), inner), // let y := x; <inner>
    );
    define(&mut env, "flet_nested", u64_arrows(1), value);
    env
}

/// `def flet_letval (x : UInt64) : UInt64 := let y := (let w := x; w + 1); y * 2`
/// — the bound EXPRESSION is itself a `let`.
fn env_letval() -> Environment {
    let mut env = env_uint();
    let bound = Expr::let_named(
        Name::from_string("w"),
        uint64(),
        Expr::bvar(0),                                    // x
        carrier_op("add", Expr::bvar(0), carrier_lit(1)), // w + 1
        false,
    );
    let value = Expr::lam(
        BinderInfo::Default,
        uint64(),
        let_u64(bound, carrier_op("mul", Expr::bvar(0), carrier_lit(2))), // y * 2
    );
    define(&mut env, "flet_letval", u64_arrows(1), value);
    env
}

// ─────────────── the emitter's MIR, as extracted, and mutants ───────────────

const WADD: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
const WSUB: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub";

fn locals(n: usize) -> Vec<LocalDecl> {
    (0..n).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect()
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

fn copy_arg(i: usize) -> Operand {
    Operand::Copy(Place::local(i))
}

/// The two-block single-call body the emitter produces for `x + 1`.
fn emitted_add1(name: &str) -> VerifiableFunction {
    vf(
        name,
        1,
        locals(2),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: prim_call(
                    WADD,
                    vec![copy_arg(1), Operand::Constant(ConstValue::Uint(1, 64))],
                    Place::local(0),
                    BlockId(1),
                ),
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

/// The three-block wrapping call CHAIN the emitter produces for `(x+1)*(x+1)`:
/// one shared temp `_2 = x + 1`, then `_0 = _2 * _2`.
fn emitted_sq(name: &str, mul_left: Operand, mul_right: Operand) -> VerifiableFunction {
    const WMUL: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_mul";
    vf(
        name,
        1,
        locals(3), // _0 result, _1 param, _2 temp
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: prim_call(
                    WADD,
                    vec![copy_arg(1), Operand::Constant(ConstValue::Uint(1, 64))],
                    Place::local(2),
                    BlockId(1),
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: Vec::new(),
                terminator: prim_call(WMUL, vec![mul_left, mul_right], Place::local(0), BlockId(2)),
            },
            BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

fn u64_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_at(&uint64(), &Ty::u64())
        .expect("UInt64 -> u64 is the exact-width carrier")
}

/// Reflect a spec-syntax body directly through the frozen expr mint — the
/// kernel half of a mutation, so the KERNEL's own verdict is measured.
fn reflect_expr(env: &Environment, body: &str, n_params: usize) -> Expr {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut scratch = env.clone();
    let name = "control24_reflection";
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

// ═══════════════════════════════ the halves ═══════════════════════════════

#[test]
fn half_0_the_reduced_shape_is_the_let_free_equivalent() {
    // Each `let` def reduces (zeta) to exactly the shape its `let`-free
    // equivalent would produce — nothing downstream learns the `let` exists.
    let cases: Vec<(Environment, &str, CleanOriginShape)> = vec![
        (env_id(), "flet_id", CleanOriginShape::Projection { projected: 0 }),
        (
            env_add(),
            "flet_add",
            CleanOriginShape::WrappingBinOp {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            },
        ),
        (
            env_shadow(),
            "flet_shadow",
            CleanOriginShape::WrappingBinOp {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            },
        ),
        (
            env_nested(),
            "flet_nested",
            CleanOriginShape::WrappingBinOp {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            },
        ),
    ];
    for (env, name, expected) in cases {
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|e| panic!("`{name}` must plan through the zeta reduction: {e:?}"));
        assert_eq!(plan.shape(), &expected, "`{name}` reduced to the wrong shape");
        assert_eq!(plan.signature().arity(), 1);
        assert_eq!(plan.return_ty(), &Ty::u64());
    }
}

#[test]
fn half_1_a_reused_binding_reduces_to_a_duplicating_tree() {
    // `let y := x+1; y*y` USES the binding twice, so it reduces to the
    // Composed tree `(x+1)*(x+1)`, which is what recognize_call_chain reads
    // back by unfolding the shared temp.
    let env = env_sq();
    let plan = plan_clean_origin_body(&env, "flet_sq").expect("flet_sq must plan");
    let add = ArithExpr::Bin {
        op: ArithBinOp::Add,
        left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
        right: Box::new(ArithExpr::Operand(ArithOperand::Const(1))),
    };
    let expected = CleanOriginShape::Composed {
        expr: ArithExpr::Bin {
            op: ArithBinOp::Mul,
            left: Box::new(add.clone()),
            right: Box::new(add),
        },
    };
    assert_eq!(plan.shape(), &expected, "flet_sq must duplicate `x+1`");

    // And the bound-expr-is-itself-a-`let` case reduces too.
    let env = env_letval();
    let plan = plan_clean_origin_body(&env, "flet_letval").expect("flet_letval must plan");
    let expected = CleanOriginShape::Composed {
        expr: ArithExpr::Bin {
            op: ArithBinOp::Mul,
            left: Box::new(ArithExpr::Bin {
                op: ArithBinOp::Add,
                left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                right: Box::new(ArithExpr::Operand(ArithOperand::Const(1))),
            }),
            right: Box::new(ArithExpr::Operand(ArithOperand::Const(2))),
        },
    };
    assert_eq!(plan.shape(), &expected, "flet_letval must reduce the inner `let`");
}

#[test]
fn half_2_the_gate_admits_the_faithful_emission() {
    // `let y := x+1; y` emits the same body as `x+1`, and the gate admits it
    // against the `let` declaration — i.e. the kernel zeta-reduces the `let`.
    let env = env_add();
    let plan = plan_clean_origin_body(&env, "flet_add").expect("plannable");
    let admitted = admit_lowering(&env, &plan, &emitted_add1("flet_add"))
        .expect("`wrapping_add(_1, 1)` IS `let y := x+1; y`; the gate must admit it");
    assert_eq!(admitted.name(), "flet_add");
    assert_eq!(admitted.admitted_at(), &Ty::u64());

    // The reused-binding case, end to end: the shared-temp chain admits.
    let env = env_sq();
    let plan = plan_clean_origin_body(&env, "flet_sq").expect("plannable");
    let admitted = admit_lowering(&env, &plan, &emitted_sq("flet_sq", copy_arg(2), copy_arg(2)))
        .expect("`_2 = x+1; _2 * _2` IS `let y := x+1; y*y`; the gate must admit it");
    assert_eq!(admitted.name(), "flet_sq");
}

#[test]
fn half_3_shadowing_resolves_to_the_innermost_binding() {
    // `let x := x+1; x` returns the SHADOWING binding (param+1), never the
    // parameter. The kernel gate admits `p0+1` and REFUSES `p0`.
    let env = env_shadow();
    let ok = reflect_expr(&env, "p0 + 1", 1);
    check_faithful(&env, "flet_shadow", &ok, &u64_carrier())
        .expect("the shadowing `let` denotes `x+1`; the gate must admit it");

    let wrong = reflect_expr(&env, "p0", 1);
    let refusal = check_faithful(&env, "flet_shadow", &wrong, &u64_carrier())
        .expect_err("returning the OUTER parameter mis-resolves the shadow and must refuse");
    assert!(
        matches!(refusal, GateRefusal::Disagreement { .. }),
        "a shadow mis-resolution is a def-eq divergence, got {refusal:?}"
    );
}

#[test]
fn half_4_a_WRONG_BOUND_VALUE_is_refused_by_the_kernel_gate() {
    // The emitter binds `x + 2` where the declaration binds `x + 1`. Reflected
    // as `(p0+2)*(p0+2)`, the kernel refuses it against `let y := x+1; y*y`.
    let env = env_sq();
    let wrong = reflect_expr(&env, "(p0 + 2) * (p0 + 2)", 1);
    let refusal = check_faithful(&env, "flet_sq", &wrong, &u64_carrier())
        .expect_err("binding `x+2` instead of `x+1` must be refused by the kernel gate");
    assert!(
        matches!(refusal, GateRefusal::Disagreement { .. }),
        "a wrong bound value is a def-eq divergence, got {refusal:?}"
    );
}

#[test]
fn half_5_a_WRONG_BODY_using_of_the_binding_is_refused_by_the_kernel_gate() {
    // The declaration's body is `y * y`; the emitter computes `y * x` instead.
    // Reflected as `(p0+1) * p0`, the kernel refuses it.
    let env = env_sq();
    let wrong = reflect_expr(&env, "(p0 + 1) * p0", 1);
    let refusal = check_faithful(&env, "flet_sq", &wrong, &u64_carrier())
        .expect_err("using `x` where the body uses the binding `y` must be refused");
    assert!(
        matches!(refusal, GateRefusal::Disagreement { .. }),
        "a wrong use of the binding is a def-eq divergence, got {refusal:?}"
    );

    // And the SAME mutation reaches the gate through the full round trip: the
    // emitted chain multiplies `_2 * _1` (temp * param) instead of `_2 * _2`.
    let plan = plan_clean_origin_body(&env, "flet_sq").expect("plannable");
    let bad = admit_lowering(&env, &plan, &emitted_sq("flet_sq", copy_arg(2), copy_arg(1)));
    assert!(bad.is_err(), "`_2 * _1` computes `(x+1)*x`, not `(x+1)^2` — must refuse");
}

#[test]
fn half_6_a_correct_faithful_term_admits_across_every_let_shape() {
    // The positive control: for each `let` def, the correctly reduced side-B
    // term ADMITS — the kernel zeta-reduces the `let` on its own.
    for (env, name, body) in [
        (env_add(), "flet_add", "p0 + 1"),
        (env_nested(), "flet_nested", "p0 + 1"),
        (env_sq(), "flet_sq", "(p0 + 1) * (p0 + 1)"),
        (env_letval(), "flet_letval", "(p0 + 1) * 2"),
    ] {
        let ok = reflect_expr(&env, body, 1);
        check_faithful(&env, name, &ok, &u64_carrier())
            .unwrap_or_else(|e| panic!("`{name}` == `{body}` via zeta; must admit: {e:?}"));
    }
}

#[test]
fn half_7_a_wrong_op_in_the_reduced_tree_is_refused() {
    // A sub-op mutation inside the reduced tree: `(x+1)*(x+1)` emitted with a
    // SUBTRACT at the outer op. Through admit_lowering the structural
    // plan-vs-recognizer check refuses it, and the kernel refuses the reflected
    // `(p0+1) - (p0+1)` directly.
    let env = env_sq();
    let wrong = reflect_expr(&env, "(p0 + 1) - (p0 + 1)", 1);
    assert!(
        check_faithful(&env, "flet_sq", &wrong, &u64_carrier()).is_err(),
        "a subtract where the body multiplies must refuse"
    );

    // Guard against WSUB being unused when the end-to-end mutant is trimmed.
    let _ = (WSUB, emitted_add1("flet_add"));
}
