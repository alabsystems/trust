// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 6 — THE COMPOSED-CHAIN EMITTER MUTATION FIXTURE.**
//!
//! `control_3` is the emitter-mutation discipline pointed at the `Projection`
//! arm; `control_5` points it at `WrappingBinOp`. This file is the same
//! discipline pointed at [`CleanOriginShape::Composed`] — the third emittable
//! shape, landed 2026-08-20 on the kernel measurements in
//! `fragment_widening_probes.rs` (probe_f for the nested ADMIT in both side-A
//! spellings, probe_f2 for the depth cap) and the e6 corpus's
//! `f21_composed_wrapping`, which discharges the chain end-to-end.
//!
//! The route and the soundness argument are control_5's, unchanged:
//!
//! ```text
//! emitted body (as read back out of MIR by trust_mir_extract)
//!   -> trust_types::recognize_admissible_body            (Composed)
//!   -> trust_spec_elab::admit_expr_function              (side B, "((p0 + p1) * p0)")
//!   -> check_faithful                                    (against side A)
//! ```
//!
//! and the mutation is injected into **the emitted body** — the linear
//! wrapping-call chain — never into side B, so what is measured is that a
//! mistranslating chain emitter cannot pass the gate. The
//! `VerifiableFunction`s are hand-built in the exact extracted shape the
//! probes already use (`fragment_widening_probes::emitted_nested`); whether
//! the real emitter produces this MIR is the compiler lane's question
//! (`tests/ui/trust/clean_origin_composed.rs`).
//!
//! # WHAT IS NEW OVER CONTROL 5, AND WHY
//!
//! A chain has a mutation a single op cannot have: **associativity**. The
//! same ops over the same operand multiset compose to different values —
//! `(a + b) * a` at (2, 3) is 10, `a + (b * a)` is 8 — and only the TREE
//! distinguishes them. half_4 pins that mutation at both layers, because an
//! emitter that flattened the tree in the wrong order is exactly the bug a
//! linear-chain emitter can have while every node is individually correct.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` (including `recognize_call_chain`) and
//! `trust_spec_elab::admit_*_function` are frozen against this lane, exactly
//! as for control_3/control_5. If a mutated chain ever passes, the defect is
//! in the emitter or the gate — never in this fixture.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::{
    admit_lowering, check_faithful, plan_clean_origin_body, CleanOriginShape, EmitRefusal,
    GateRefusal,
};
use trust_types::admissible_body::{ArithBinOp, ArithExpr, ArithOperand};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
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

/// `H<Op>.h<op> UInt64 UInt64 UInt64 instH<Op>UInt64 lhs rhs` — the surface
/// spelling a real island stores.
fn surface_op(class: &str, proj: &str, lhs: Expr, rhs: Expr) -> Expr {
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    Expr::apps(
        Expr::const_(Name::from_string(&format!("{class}.{proj}")), zero3),
        [
            uint64(),
            uint64(),
            uint64(),
            Expr::const_(Name::from_string(&format!("inst{class}UInt64")), vec![]),
            lhs,
            rhs,
        ],
    )
}

/// `def wmix (a b : UInt64) : UInt64 := (a + b) * a`, carrier spelling,
/// kernel-checked — probe_f's subject, now emittable.
fn env_with_wmix() -> Environment {
    let mut env = env_uint();
    define(
        &mut env,
        "wmix",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                carrier_op("mul", carrier_op("add", Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
            ),
        ),
    );
    env
}

/// The tree `(a + b) * a` — what BOTH sides must read.
fn wmix_tree() -> ArithExpr {
    ArithExpr::Bin {
        op: ArithBinOp::Mul,
        left: Box::new(ArithExpr::Bin {
            op: ArithBinOp::Add,
            left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
            right: Box::new(ArithExpr::Operand(ArithOperand::Param(1))),
        }),
        right: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
    }
}

// ─────────────── the emitter's chain, as extracted, and mutants ───────────────

const WADD: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
const WSUB: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub";
const WMUL: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_mul";
const WADD32: &str = "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_add";
const WMUL32: &str = "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_mul";

fn locals(n: usize, ty: Ty) -> Vec<LocalDecl> {
    (0..n).map(|index| LocalDecl { index, ty: ty.clone(), name: None }).collect()
}

/// A linear call chain: one `Call` block per `(callee, args, dest)` triple,
/// each targeting the next block, then a bare `Return` block — the exact
/// shape the Composed emitter produces and `recognize_call_chain` reads.
fn emitted_chain(
    name: &str,
    arg_count: usize,
    locals: Vec<LocalDecl>,
    calls: Vec<(&str, Vec<Operand>, Place)>,
) -> VerifiableFunction {
    let n = calls.len();
    let mut blocks: Vec<BasicBlock> = calls
        .into_iter()
        .enumerate()
        .map(|(k, (callee, args, dest))| BasicBlock {
            id: BlockId(k),
            stmts: Vec::new(),
            terminator: Terminator::Call {
                func: callee.into(),
                args,
                dest,
                target: Some(BlockId(k + 1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: UnwindEdge::Unreachable,
            },
        })
        .collect();
    blocks.push(BasicBlock { id: BlockId(n), stmts: Vec::new(), terminator: Terminator::Return });
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
    }
}

fn copy_local(i: usize) -> Operand {
    Operand::Copy(Place::local(i))
}

/// The FAITHFUL chain for `wmix`: `_3 = wrapping_add(_1, _2)`;
/// `_0 = wrapping_mul(_3, _1)`; `return` — post-order, temp `_3`, over
/// (u64, u64) -> u64.
fn faithful_wmix_chain() -> VerifiableFunction {
    emitted_chain(
        "wmix",
        2,
        locals(4, Ty::u64()),
        vec![
            (WADD, vec![copy_local(1), copy_local(2)], Place::local(3)),
            (WMUL, vec![copy_local(3), copy_local(1)], Place::local(0)),
        ],
    )
}

/// Reflect a spec-syntax body directly through the frozen expr mint — the
/// kernel half of a mutation, bypassing the structural check on purpose so
/// the KERNEL's own verdict is measured (control_3 half_3's rationale).
fn reflect_expr(env: &Environment, body: &str, n_params: usize) -> Expr {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut scratch = env.clone();
    let name = "control6_reflection";
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
fn half_0_the_plan_reads_both_spellings_as_the_same_composed_tree() {
    let mut env = env_with_wmix();
    define(
        &mut env,
        "wmix_s",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_op(
                    "HMul",
                    "hMul",
                    surface_op("HAdd", "hAdd", Expr::bvar(1), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
    let expected = CleanOriginShape::Composed { expr: wmix_tree() };
    for name in ["wmix", "wmix_s"] {
        let plan = plan_clean_origin_body(&env, name).expect("a composed tree plans");
        assert_eq!(plan.shape(), &expected, "`{name}` must read as `(a + b) * a`");
        assert_eq!(plan.signature().arity(), 2);
        assert_eq!(plan.return_ty(), &Ty::u64());
    }
}

#[test]
fn half_1_the_gate_admits_the_faithful_chain() {
    let env = env_with_wmix();
    let plan = plan_clean_origin_body(&env, "wmix").expect("plannable");

    let admitted = admit_lowering(&env, &plan, &faithful_wmix_chain())
        .expect("the post-order chain IS `(a + b) * a`; the gate must admit it");
    assert_eq!(admitted.name(), "wmix");
    assert_eq!(
        admitted.admitted_at(),
        &Ty::u64(),
        "admitted AT THE CARRIER TYPE, never the Clean type"
    );
}

#[test]
fn half_2_a_chain_with_the_WRONG_OP_is_refused_by_both_layers() {
    let env = env_with_wmix();
    let plan = plan_clean_origin_body(&env, "wmix").expect("plannable");

    // ONE construct changed: the inner callee is wrapping_sub. Same blocks,
    // same temps, same operands — a chain computing `(a - b) * a` for a def
    // that says `(a + b) * a`.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_chain(
            "wmix",
            2,
            locals(4, Ty::u64()),
            vec![
                (WSUB, vec![copy_local(1), copy_local(2)], Place::local(3)),
                (WMUL, vec![copy_local(3), copy_local(1)], Place::local(0)),
            ],
        ),
    )
    .expect_err(
        "THE GATE IS DECORATION IF THIS PASSES: a chain computing `(a - b) * a` was \
         accepted for a definition that says `(a + b) * a` — a WRONG BINARY. Do NOT fix \
         this by editing side B's producers; they are frozen against this lane.",
    );
    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect: {refusal:?}");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "the structural catch fires first; got {refusal:?}"
    );

    // Kernel half: the same mutation put to the kernel directly.
    let wrong = reflect_expr(&env, "((p0 - p1) * p0)", 2);
    let refusal = check_faithful(&env, "wmix", &wrong, &u64_carrier())
        .expect_err("the kernel must separate `(a + b) * a` from `(a - b) * a`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_3_an_OPERAND_SWAP_in_the_chain_is_refused_by_both_layers() {
    let env = env_with_wmix();
    let plan = plan_clean_origin_body(&env, "wmix").expect("plannable");

    // The root multiplies by `_2` instead of `_1`: `(a + b) * b`.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_chain(
            "wmix",
            2,
            locals(4, Ty::u64()),
            vec![
                (WADD, vec![copy_local(1), copy_local(2)], Place::local(3)),
                (WMUL, vec![copy_local(3), copy_local(2)], Place::local(0)),
            ],
        ),
    )
    .expect_err("`(a + b) * b` emitted for a def that says `(a + b) * a` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half — probe_f measures the same fact; re-pinned here under this
    // control's honesty rules so the control stands alone.
    let refusal =
        check_faithful(&env, "wmix", &reflect_expr(&env, "((p0 + p1) * p1)", 2), &u64_carrier())
            .expect_err("the kernel must separate `(a + b) * a` from `(a + b) * b`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_4_the_WRONG_ASSOCIATIVITY_is_refused_by_both_layers() {
    // THE CHAIN-SPECIFIC MUTATION. `a + (b * a)` uses the same two ops and
    // the same operand multiset as `(a + b) * a`; only the TREE differs —
    // at (2, 3): 10 versus 8. An emitter that flattened the tree in the wrong
    // order produces exactly this chain, with every individual node correct.
    let env = env_with_wmix();
    let plan = plan_clean_origin_body(&env, "wmix").expect("plannable");

    // Structural half: `_3 = wrapping_mul(_2, _1); _0 = wrapping_add(_1, _3)`.
    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_chain(
            "wmix",
            2,
            locals(4, Ty::u64()),
            vec![
                (WMUL, vec![copy_local(2), copy_local(1)], Place::local(3)),
                (WADD, vec![copy_local(1), copy_local(3)], Place::local(0)),
            ],
        ),
    )
    .expect_err("`a + (b * a)` emitted for a def that says `(a + b) * a` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half: the re-associated reflection alone. If the kernel
    // identified the two trees, the fully-parenthesized rendering would be
    // decoration.
    let refusal =
        check_faithful(&env, "wmix", &reflect_expr(&env, "(p0 + (p1 * p0))", 2), &u64_carrier())
            .expect_err("the kernel must separate `(a + b) * a` from `a + (b * a)`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_5_a_chain_at_the_WRONG_WIDTH_is_refused_by_the_kernel() {
    // The composed analogue of control_5 half_8 — and the reason the
    // structural tree comparison can never substitute for the kernel: the
    // tree is WIDTH-BLIND. A u32 chain for a UInt64 def recognizes as the
    // IDENTICAL `ArithExpr`, passes the structural match, reflects at UInt32
    // — and truncates every value the declaration talks about. Only the
    // kernel comparison at the emitted width can see that.
    let env = env_with_wmix();
    let plan = plan_clean_origin_body(&env, "wmix").expect("plannable");

    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_chain(
            "wmix",
            2,
            locals(4, Ty::Int { width: 32, signed: false }),
            vec![
                (WADD32, vec![copy_local(1), copy_local(2)], Place::local(3)),
                (WMUL32, vec![copy_local(3), copy_local(1)], Place::local(0)),
            ],
        ),
    )
    .expect_err("a u32 chain emitted for a UInt64 declaration truncates and must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::Gate(GateRefusal::Disagreement { .. })),
        "the width mistake must be caught by the KERNEL comparison — the structural tree \
         match is width-blind and cannot see a truncation; got {refusal:?}"
    );
}

#[test]
fn half_6_a_chain_with_an_EXTRA_op_is_refused_structurally() {
    // A three-call chain computing `((a + b) * a) * a` for the two-op def:
    // every node authenticated, every block well-formed, one node too many.
    // The recognizer reads the LARGER tree and the structural comparison
    // against the plan must refuse it.
    let env = env_with_wmix();
    let plan = plan_clean_origin_body(&env, "wmix").expect("plannable");

    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_chain(
            "wmix",
            2,
            locals(5, Ty::u64()),
            vec![
                (WADD, vec![copy_local(1), copy_local(2)], Place::local(3)),
                (WMUL, vec![copy_local(3), copy_local(1)], Place::local(4)),
                (WMUL, vec![copy_local(4), copy_local(1)], Place::local(0)),
            ],
        ),
    )
    .expect_err("an extra multiplication is a different function and must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}
