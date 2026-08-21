// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **FRAGMENT-WIDENING PROBES — which `CleanOriginShape` can be added NEXT,
//! measured at the kernel, before any rustc work.**
//!
//! Per ruling v7/D2 the way to widen `CleanOriginShape` is to make the two
//! sides agree at the kernel — extend the COMPILER — never to relax the gate.
//! This file measures, for each candidate shape, whether the two sides CAN
//! agree today:
//!
//! * **side A** — the Clean `def`'s body, inserted through the FULL kernel
//!   check (`Environment::add_decl`), exactly as `control_2`/`control_3` build
//!   theirs. Where the surface spelling a real island would elaborate to
//!   differs from the carrier-op spelling (`HAdd.hAdd`/`OfNat.ofNat` versus
//!   `UInt64.add`/`UInt64.ofNat`), BOTH are probed — the surface spelling is
//!   hand-built but kernel-checked at `add_decl`, so a malformed construction
//!   fails loudly rather than measuring the wrong term.
//! * **side B** — the reflection of the admissible-body form a FUTURE emitter
//!   would produce, through the exact frozen producers the compiler uses
//!   (`trust_types::recognize_admissible_body`, then the same
//!   `trust_spec_elab::admit_*` routing as
//!   `trust_certify::clean_island::admit_function_into`: `Arithmetic` →
//!   `admit_expr_function("p0 + p1", …)`, `Composed` → the fully-parenthesized
//!   rendering, `ConstantUint` → `admit_constant_function`). Minted into a
//!   CLONE of the environment, mirroring `emit.rs`.
//! * **the verdict** — [`check_faithful`], at the u64 carrier.
//!
//! Every probe also pins TODAY's planner verdict: a refusal
//! (`plan_clean_origin_body` → `NotEmittable`) for shapes with no
//! `CleanOriginShape` variant, or the PLANNED SHAPE for a landed widening — a
//! landed widening flips the named assertions in the same commit as its
//! variant (the e6-fragment-probe ratchet discipline, on the fast lane).
//! `WrappingBinOp` landed 2026-08-19 and flipped a/a2/b/c/d, with the numeral
//! probes a4–a6 measured first. `Composed` landed 2026-08-20 and flipped
//! probe_f, with the nested kernel ADMIT measured 2026-08-19 (and the e6
//! corpus's f21 discharging the chain end-to-end before that); probe_f2 pins
//! its measured depth cap.
//!
//! # HONESTY RULES (same as the controls)
//!
//! * A probe that REFUSES asserts the refusal and its kind. A probe that
//!   ADMITS asserts admission. No probe passes vacuously.
//! * Admitting probes carry a paired MUTATION control (a one-construct-wrong
//!   side B must be refused), so an ADMIT is a decision, not a rubber stamp.
//! * Side B's producers are FROZEN against this lane. If a probe's verdict is
//!   not the one you want, the fix is in the emitter-to-be or the kernel
//!   prelude — never in `recognize_admissible_body`, `admit_*_function`,
//!   `reflect.rs`, or this fixture's assertions.
//!
//! # Measured verdicts (2026-08-19, this file's assertions ARE the record)
//!
//! | shape | side B constructible? | kernel verdict | plans today? |
//! |---|---|---|---|
//! | `a + b` (carrier + surface side A) | yes | ADMIT | `WrappingBinOp` |
//! | `a - b` (carrier + surface side A) | yes | ADMIT | `WrappingBinOp` |
//! | `a * b` (carrier + surface side A) | yes | ADMIT | `WrappingBinOp` |
//! | `a + c` over 3 params | yes | ADMIT | `WrappingBinOp` |
//! | `a + 6` / `a - 1` (carrier + surface side A) | yes | ADMIT (a4–a6) | `WrappingBinOp` |
//! | nullary `6` (carrier + surface side A) | yes (nullary mint) | ADMIT — both spellings | refused: arity 0 |
//! | unary constant `6` via ConstantUint route | wrong arity | REFUSE (Disagreement) | refused |
//! | unary constant `6` via expr route | yes | ADMIT — both spellings | refused: a bare numeral body is not a binop |
//! | `(a + b) * a` (carrier + surface side A) | yes | ADMIT | `Composed` (flipped 2026-08-20) |
//! | chain of `COMPOSED_MAX_OPS` ops / one more | yes | ADMIT at the cap | `Composed` at the cap; refused past it (probe_f2) |
//! | `a < b : Bool` | NO — no recognizer arm, no admit path | unreachable | refused |
//!
//! The constant rows locate the corpus's finding 3 (`f04`–`f09`, every
//! constant probe fails): the bare kernel comparison ADMITS the constant in
//! BOTH spellings, so the compiler-lane failures live upstream of the kernel
//! — in the arity-erasing `ConstantUint` -> nullary-mint routing (measured
//! REFUSED here) and the clause path — not in definitional equality.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_carrier::{carrier_at, Carrier};
use trust_clean_origin::{
    check_faithful, plan_clean_origin_body, CleanOriginShape, EmitRefusal, GateRefusal,
    COMPOSED_MAX_OPS,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    recognize_admissible_body, AdmissibleBody, ArithBinOp, ArithExpr, ArithOperand,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A helpers ─────────────────────────────

fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

fn u64_carrier() -> Carrier {
    carrier_at(&uint64(), &Ty::u64())
        .expect("UInt64 -> u64 is the exact-width carrier and must be granted")
}

fn env_uint() -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith()
        .expect("UInt8/16/32/64 plus wrapping add/sub/mul + HAdd/HSub/HMul + OfNat must init");
    env
}

/// Insert `def name : type_ := value` through the FULL kernel check. A
/// malformed hand-built term fails HERE, loudly — this is what keeps the
/// hand-built surface spellings honest.
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

/// `UInt64 -> UInt64 -> ... -> UInt64` with `n` arrows.
fn u64_arrows(n: usize) -> Expr {
    (0..n).fold(uint64(), |acc, _| Expr::arrow(uint64(), acc))
}

/// The carrier-op spelling of a binary op: `UInt64.<op> lhs rhs` — the
/// spelling `control_2` uses for `double`, and the one `Domain::arithmetic`
/// mints on side B.
fn carrier_op(op: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(&format!("UInt64.{op}")), vec![]), [lhs, rhs])
}

/// The SURFACE spelling of a binary op at `UInt64` — what `a + b` elaborates
/// to through the typeclass path: `HAdd.hAdd UInt64 UInt64 UInt64
/// instHAddUInt64 lhs rhs` (projection binder order per
/// `clean_kernel::env::algebra_hetero::build_hetero_projection`; the instance
/// per `add_homogeneous_hetero_instance`). Hand-built, but `define` puts it
/// through the full kernel check, so a wrong construction cannot measure.
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

/// The SURFACE spelling of a numeral at `UInt64` — what a literal `n`
/// elaborates to through the `OfNat` path: `OfNat.ofNat UInt64 n
/// (instOfNatUInt64 n)` (per `init_ofnat` / `init_ofnat_uint64`).
fn surface_lit(n: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            uint64(),
            Expr::nat_lit(n),
            Expr::app(
                Expr::const_(Name::from_string("instOfNatUInt64"), vec![]),
                Expr::nat_lit(n),
            ),
        ],
    )
}

/// The carrier spelling of a numeral: `UInt64.ofNat n` — what
/// `Domain::numeral` mints on side B.
fn carrier_lit(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt64.ofNat"), vec![]), Expr::nat_lit(n))
}

// ─────────────── the future emitter's MIR, as extracted ───────────────
//
// Hand-built in the exact shape `trust_mir_extract::extract_function` reports,
// exactly as control_3 builds its projections — the same soundness argument
// applies: the decision procedures under test take the extractor's output
// type, and whether a real emitter produces this MIR is the compiler lane's
// question, not this file's.

const WADD: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
const WSUB: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub";
const WMUL: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_mul";

fn u64_locals(n: usize) -> Vec<LocalDecl> {
    (0..n).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect()
}

fn vf(arg_count: usize, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: "probe".into(),
        def_path: "probe::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count, return_ty, datatype_defs: Default::default() },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
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
        unwind: UnwindEdge::Unreachable,
    }
}

/// `fn f(p0: u64, …) -> u64 { p_i.wrapping_<op>(p_j) }` as MIR: one call
/// block writing `_0`, one return block — the exact two-block shape
/// `recognize_arithmetic` was written for.
fn emitted_binop(callee: &str, args: Vec<Operand>, arg_count: usize) -> VerifiableFunction {
    vf(
        arg_count,
        u64_locals(arg_count + 1),
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

/// `fn f(a: u64, b: u64) -> u64 { (a.wrapping_add(b)).wrapping_mul(a) }` as
/// MIR: a linear two-call chain through temp `_3` — the
/// `recognize_call_chain` shape.
fn emitted_nested() -> VerifiableFunction {
    vf(
        2,
        u64_locals(4),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: prim_call(
                    WADD,
                    vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    Place::local(3),
                    BlockId(1),
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: Vec::new(),
                terminator: prim_call(
                    WMUL,
                    vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(1))],
                    Place::local(0),
                    BlockId(2),
                ),
            },
            BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

/// `fn f(...) -> u64 { 6 }` as MIR: `_0 = const 6u64; return`.
fn emitted_const(arg_count: usize) -> VerifiableFunction {
    vf(
        arg_count,
        u64_locals(arg_count + 1),
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(6, 64))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// `fn f(a: u64, b: u64) -> bool { a < b }` as MIR: `_0 = Lt(_1, _2); return`
/// — the body a future comparison emitter would most plausibly produce.
fn emitted_lt_bool() -> VerifiableFunction {
    let mut locals = u64_locals(3);
    locals[0].ty = Ty::Bool;
    vf(
        2,
        locals,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

// ─────────────────────────── side B reflection ───────────────────────────

/// Mint side B into a CLONE of `env` (mirroring `emit.rs`: a check must not
/// mutate the environment it checks) and return the reflected body term.
fn reflect(
    env: &Environment,
    mint: impl FnOnce(&mut Environment, &str) -> Result<trust_spec_elab::Admission, String>,
) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let name = "probe_widening_reflection";
    mint(&mut scratch, name)?;
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .ok_or_else(|| "the reflected definition carries no value".to_owned())
}

/// Side B for a recognized `Arithmetic`/`Composed` body — the EXACT routing
/// `trust_certify::clean_island::admit_function_into` performs: a spec-syntax
/// body over positional names `p0…p{n-1}`, through `admit_expr_function` at
/// the shared machine domain.
fn reflect_expr(env: &Environment, body: &str, n_params: usize) -> Result<Expr, String> {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    reflect(env, |scratch, name| {
        trust_spec_elab::admit_expr_function(
            scratch,
            name,
            body,
            &name_refs,
            &Domain::Machine(MachineUIntWidth::U64),
        )
    })
}

/// The `clean_island::admit_function_into` rendering of a recognized
/// `Composed` tree: fully parenthesized over positional parameter names.
fn render_composed(expr: &ArithExpr) -> String {
    match expr {
        ArithExpr::Operand(ArithOperand::Param(i)) => format!("p{i}"),
        ArithExpr::Operand(ArithOperand::Const(v)) => v.to_string(),
        ArithExpr::Bin { op, left, right } => {
            let opstr = match op {
                ArithBinOp::Add => "+",
                ArithBinOp::Sub => "-",
                ArithBinOp::Mul => "*",
            };
            format!("({} {} {})", render_composed(left), opstr, render_composed(right))
        }
    }
}

/// The `clean_island::admit_function_into` rendering of a recognized
/// single-op `Arithmetic` body.
fn render_arith(op: ArithBinOp, left: ArithOperand, right: ArithOperand) -> String {
    let opnd = |o: ArithOperand| match o {
        ArithOperand::Param(i) => format!("p{i}"),
        ArithOperand::Const(v) => v.to_string(),
    };
    let opstr = match op {
        ArithBinOp::Add => "+",
        ArithBinOp::Sub => "-",
        ArithBinOp::Mul => "*",
    };
    format!("{} {} {}", opnd(left), opstr, opnd(right))
}

/// Pin that TODAY's planner refuses this def as a capability boundary
/// (`NotEmittable`, user-facing). When a widening lands its
/// `CleanOriginShape` variant, this assertion fails in the same commit — the
/// ratchet that makes the widening visible.
fn assert_plan_refuses_today(env: &Environment, name: &str) {
    let refusal = plan_clean_origin_body(env, name)
        .expect_err("this shape has no CleanOriginShape variant yet; planning must refuse");
    assert!(
        matches!(refusal, EmitRefusal::NotEmittable { .. }),
        "expected today's capability refusal for `{name}`; got {refusal:?}"
    );
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is not a compiler defect");
}

/// The flipped ratchet: pin that the planner now reads this def as EXACTLY
/// the given emittable shape. A probe moves from `assert_plan_refuses_today`
/// to this helper in the same commit its `CleanOriginShape` variant lands.
fn assert_plan_shape(env: &Environment, name: &str, expected: CleanOriginShape) {
    let plan = plan_clean_origin_body(env, name).unwrap_or_else(|refusal| {
        panic!("`{name}` has a landed CleanOriginShape variant and must plan: {refusal:?}")
    });
    assert_eq!(plan.shape(), &expected, "`{name}` planned the WRONG shape");
}

// ═════════════════════════ (a) binary wrapping add ═════════════════════════

/// `def wsum (a b : UInt64) : UInt64 := UInt64.add a b` — side A in the
/// carrier-op spelling (control_2's convention) — against the reflection of
/// the recognized wrapping_add call form.
#[test]
fn probe_a_add_carrier_spelling_admits() {
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
    assert_plan_shape(
        &env,
        "wsum",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
    );

    // The emitter's body, read back: wrapping_add(_1, _2) -> _0.
    let emitted = emitted_binop(
        WADD,
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        2,
    );
    let recognised = recognize_admissible_body(&emitted)
        .expect("the recognizer must accept the marker-authenticated wrapping_add call");
    assert_eq!(
        recognised,
        AdmissibleBody::Arithmetic {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        }
    );
    let AdmissibleBody::Arithmetic { op, left, right } = recognised else { unreachable!() };

    let side_b = reflect_expr(&env, &render_arith(op, left, right), 2)
        .expect("the E6 expr reflection must mint `p0 + p1` at UInt64");

    let admitted = check_faithful(&env, "wsum", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: the kernel identifies `UInt64.add a b` with R(wrapping_add)");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
    eprintln!("PROBE-ROW | add (carrier side A)      | side B: yes | kernel: ADMIT");
}

/// The same reflected side B against side A in the SURFACE spelling —
/// `def wsum_s (a b : UInt64) : UInt64 := a + b` as the typeclass path
/// elaborates it (`HAdd.hAdd … instHAddUInt64 a b`). This is the spelling a
/// real island would store, so this probe — not the carrier one — is the
/// widening's actual kernel question.
#[test]
fn probe_a2_add_surface_spelling_admits() {
    let mut env = env_uint();
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
                surface_op("HAdd", "hAdd", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    assert_plan_shape(
        &env,
        "wsum_s",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
    );

    let side_b = reflect_expr(&env, "p0 + p1", 2).expect("expr reflection");
    let admitted = check_faithful(&env, "wsum_s", &side_b, &u64_carrier()).expect(
        "MEASURED ADMIT: the kernel unfolds instHAddUInt64 (reducible) and the HAdd.hAdd \
         projection down to `UInt64.add`, identifying the surface spelling with the \
         reflected lowering — the fast-lane analogue of e6 probe f10's discharge",
    );
    assert_eq!(admitted.admitted_at(), &Ty::u64());
    eprintln!("PROBE-ROW | add (surface side A)      | side B: yes | kernel: ADMIT");
}

/// MUTATION CONTROL for the admitting add probes: an emitter that emitted
/// wrapping_sub for `a + b` reflects to `p0 - p1`, and the gate must refuse
/// it. Without this pair the ADMITs above could be a gate that admits
/// everything.
#[test]
fn probe_a3_add_mutation_is_refused() {
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
    let wrong = reflect_expr(&env, "p0 - p1", 2).expect("the wrong body still reflects");
    let refusal = check_faithful(&env, "wsum", &wrong, &u64_carrier()).expect_err(
        "THE GATE IS DECORATION IF THIS PASSES: a body computing `a - b` was accepted for a \
         definition that says `a + b`",
    );
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

// ═══════════════════ (a4/a5) numeral operands — MEASURED ═══════════════════
//
// The review of the WrappingBinOp plan found that no probe above ever puts an
// arithmetic op WITH A NUMERAL OPERAND to the kernel: a/a2/b/c/d are all
// `Param ⊕ Param`, and e2/e3 measure a BARE constant body, never a constant in
// operand position. Side B's numeral is the carrier spelling `UInt64.ofNat n`
// (`Domain::numeral`), while side A's surface numeral is
// `OfNat.ofNat UInt64 n (instOfNatUInt64 n)` inside an application spine under
// binders — a different defeq path than the top-level unfolding e2 measured.
// These probes exist so that verdict is a fast-lane measurement, not a
// compiler-lane discovery.

/// `def winc6 (a : UInt64) : UInt64 := UInt64.add a (UInt64.ofNat 6)` — a
/// numeral RIGHT operand, carrier spelling — against the reflection of the
/// recognized `wrapping_add(_1, const 6)` form.
#[test]
fn probe_a4_add_numeral_carrier_spelling_admits() {
    let mut env = env_uint();
    define(
        &mut env,
        "winc6",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            carrier_op("add", Expr::bvar(0), carrier_lit(6)),
        ),
    );
    assert_plan_shape(
        &env,
        "winc6",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(6),
        },
    );

    // The future emitter's body, read back: wrapping_add(_1, const 6u64) -> _0.
    let emitted = emitted_binop(
        WADD,
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(6, 64)),
        ],
        1,
    );
    assert_eq!(
        recognize_admissible_body(&emitted),
        Some(AdmissibleBody::Arithmetic {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(6),
        })
    );

    let side_b = reflect_expr(&env, "p0 + 6", 1).expect("the expr reflection mints `p0 + 6`");
    let admitted = check_faithful(&env, "winc6", &side_b, &u64_carrier()).expect(
        "MEASURED ADMIT (2026-08-19): the kernel identifies `UInt64.add a (UInt64.ofNat 6)` \
         with R(wrapping_add(a, 6)) — the numeral-operand case the earlier probes never put \
         to the kernel",
    );
    assert_eq!(admitted.admitted_at(), &Ty::u64());

    // MUTATION: an emitter that emitted the WRONG constant reflects to
    // `p0 + 7` and must be refused.
    let wrong = reflect_expr(&env, "p0 + 7", 1).expect("the wrong body still reflects");
    assert!(
        matches!(
            check_faithful(&env, "winc6", &wrong, &u64_carrier()),
            Err(GateRefusal::Disagreement { .. })
        ),
        "an emitter that baked in 7 for a definition that says 6 must be caught"
    );
    eprintln!("PROBE-ROW | a + 6 (carrier side A)    | side B: yes | kernel: ADMIT");
}

/// `def winc6_s (a : UInt64) : UInt64 := a + 6` in the SURFACE spelling of
/// BOTH the op and the numeral — `HAdd.hAdd … instHAddUInt64 a
/// (OfNat.ofNat UInt64 6 (instOfNatUInt64 6))`. This is what a real island
/// literal elaborates to, so this probe — not the carrier one — is the numeral
/// widening's actual kernel question.
#[test]
fn probe_a5_add_numeral_surface_spelling_admits() {
    let mut env = env_uint();
    define(
        &mut env,
        "winc6_s",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            surface_op("HAdd", "hAdd", Expr::bvar(0), surface_lit(6)),
        ),
    );
    assert_plan_shape(
        &env,
        "winc6_s",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(6),
        },
    );

    let side_b = reflect_expr(&env, "p0 + 6", 1).expect("expr reflection");
    check_faithful(&env, "winc6_s", &side_b, &u64_carrier()).expect(
        "MEASURED ADMIT (2026-08-19): the kernel unfolds instHAddUInt64 AND the operand's \
         `OfNat.ofNat UInt64 6 (instOfNatUInt64 6)` down to `UInt64.add a (UInt64.ofNat 6)`, \
         identifying the surface numeral spelling with the reflected lowering",
    );

    let wrong = reflect_expr(&env, "p0 + 7", 1).expect("reflects");
    assert!(
        matches!(
            check_faithful(&env, "winc6_s", &wrong, &u64_carrier()),
            Err(GateRefusal::Disagreement { .. })
        ),
        "wrong-constant mutation must refuse in the surface spelling too"
    );
    eprintln!("PROBE-ROW | a + 6 (surface side A)    | side B: yes | kernel: ADMIT");
}

/// `def wdec (a : UInt64) : UInt64 := a - 1`, both side-A spellings — the
/// non-commutative op with a numeral, i.e. the exact shape the run-pass UI
/// fixture `clean_origin_wrapping_binop.rs` ships (`wdec(0) == u64::MAX`).
#[test]
fn probe_a6_sub_numeral_both_spellings_admit() {
    let mut env = env_uint();
    define(
        &mut env,
        "wdec",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            carrier_op("sub", Expr::bvar(0), carrier_lit(1)),
        ),
    );
    define(
        &mut env,
        "wdec_s",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            surface_op("HSub", "hSub", Expr::bvar(0), surface_lit(1)),
        ),
    );
    assert_plan_shape(
        &env,
        "wdec",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(1),
        },
    );
    assert_plan_shape(
        &env,
        "wdec_s",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(1),
        },
    );

    let side_b = reflect_expr(&env, "p0 - 1", 1).expect("expr reflection");
    check_faithful(&env, "wdec", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: carrier-spelled `a - 1`");
    check_faithful(&env, "wdec_s", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: surface-spelled `a - 1` (numeral inside the spine)");

    // MUTATION, on the non-commutative op: `1 - p0` — the operand-swap an
    // emitter argument-order bug would produce — must refuse.
    let swapped = reflect_expr(&env, "1 - p0", 1).expect("reflects");
    assert!(
        matches!(
            check_faithful(&env, "wdec", &swapped, &u64_carrier()),
            Err(GateRefusal::Disagreement { .. })
        ),
        "a swapped-operand `1 - a` must never be admitted for `a - 1`"
    );
    eprintln!("PROBE-ROW | a - 1 (both side A forms) | side B: yes | kernel: ADMIT");
}

// ═════════════════════════ (b) wrapping sub and mul ═════════════════════════

#[test]
fn probe_b_sub_carrier_and_surface_admit() {
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
    define(
        &mut env,
        "wdiff_s",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_op("HSub", "hSub", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    assert_plan_shape(
        &env,
        "wdiff",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
    );

    let emitted = emitted_binop(
        WSUB,
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        2,
    );
    assert_eq!(
        recognize_admissible_body(&emitted),
        Some(AdmissibleBody::Arithmetic {
            op: ArithBinOp::Sub,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        })
    );

    let side_b = reflect_expr(&env, "p0 - p1", 2).expect("expr reflection");
    check_faithful(&env, "wdiff", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: carrier-spelled sub");
    check_faithful(&env, "wdiff_s", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: surface-spelled sub (HSub.hSub via instHSubUInt64)");
    eprintln!("PROBE-ROW | sub (both side A forms)   | side B: yes | kernel: ADMIT");
}

#[test]
fn probe_c_mul_carrier_and_surface_admit() {
    let mut env = env_uint();
    define(
        &mut env,
        "wprod",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                carrier_op("mul", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    define(
        &mut env,
        "wprod_s",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_op("HMul", "hMul", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    assert_plan_shape(
        &env,
        "wprod",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Mul,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
    );

    let emitted = emitted_binop(
        WMUL,
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        2,
    );
    assert_eq!(
        recognize_admissible_body(&emitted),
        Some(AdmissibleBody::Arithmetic {
            op: ArithBinOp::Mul,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        })
    );

    let side_b = reflect_expr(&env, "p0 * p1", 2).expect("expr reflection");
    check_faithful(&env, "wprod", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: carrier-spelled mul");
    check_faithful(&env, "wprod_s", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: surface-spelled mul (HMul.hMul via instHMulUInt64)");
    eprintln!("PROBE-ROW | mul (both side A forms)   | side B: yes | kernel: ADMIT");
}

// ═══════════ (c) projections composed with one arithmetic op ═══════════

/// `def skipsum (a b c : UInt64) : UInt64 := a + c` — the arithmetic op over
/// NON-ADJACENT parameters. Pins that the positional `p0…p{n-1}` naming and
/// the de Bruijn inversion survive an ignored middle parameter.
#[test]
fn probe_d_add_over_three_params_admits() {
    let mut env = env_uint();
    define(
        &mut env,
        "skipsum",
        u64_arrows(3),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                Expr::lam(
                    BinderInfo::Default,
                    uint64(),
                    // Under 3 binders: a = bvar 2, c = bvar 0.
                    carrier_op("add", Expr::bvar(2), Expr::bvar(0)),
                ),
            ),
        ),
    );
    assert_plan_shape(
        &env,
        "skipsum",
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(2),
        },
    );

    // wrapping_add(_1, _3) -> _0 over three u64 parameters.
    let emitted = emitted_binop(
        WADD,
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(3))],
        3,
    );
    let recognised = recognize_admissible_body(&emitted).expect("recognized");
    assert_eq!(
        recognised,
        AdmissibleBody::Arithmetic {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(2),
        }
    );

    let side_b = reflect_expr(&env, "p0 + p2", 3).expect("expr reflection over 3 params");
    check_faithful(&env, "skipsum", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: `a + c` over (a, b, c)");

    // Mutation: `p0 + p1` — the adjacent-parameter mistake — must refuse.
    let wrong = reflect_expr(&env, "p0 + p1", 3).expect("reflects");
    assert!(
        matches!(
            check_faithful(&env, "skipsum", &wrong, &u64_carrier()),
            Err(GateRefusal::Disagreement { .. })
        ),
        "an emitter that added the WRONG parameter pair must be caught"
    );
    eprintln!("PROBE-ROW | a + c over 3 params       | side B: yes | kernel: ADMIT");
}

// ═════════════════════════════ (d) constants ═════════════════════════════

/// `def six : UInt64 := UInt64.ofNat 6` (carrier spelling) against the
/// nullary constant mint. The e6 corpus records every ConstantUint probe
/// defeq-rejected or unproved ON THE COMPILER LANE; this measures where that
/// failure lives — at the kernel comparison itself, or upstream of it.
#[test]
fn probe_e_nullary_constant_carrier_spelling() {
    let mut env = env_uint();
    define(&mut env, "six", uint64(), carrier_lit(6));

    // Today's boundary, pinned: arity 0 refuses at PLAN time.
    let refusal = plan_clean_origin_body(&env, "six").expect_err("nullary refuses at plan");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");

    // The emitted body recognizes and the nullary mint reflects.
    assert_eq!(
        recognize_admissible_body(&emitted_const(0)),
        Some(AdmissibleBody::ConstantUint { value: 6, width_bits: 64 })
    );
    let side_b = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_constant_function(scratch, name, 6, MachineUIntWidth::U64)
    })
    .expect("the nullary constant mint reflects `UInt64.ofNat 6`");

    // MEASURED: the kernel identifies the two carrier-spelled constants.
    check_faithful(&env, "six", &side_b, &u64_carrier()).expect(
        "MEASURED ADMIT: side A and side B are both `UInt64.ofNat 6`; the corpus's \
         constant failures are NOT reproduced at the bare kernel comparison in the \
         carrier spelling",
    );
    eprintln!("PROBE-ROW | const 6, nullary, carrier | side B: yes | kernel: ADMIT");
}

/// `def six_s : UInt64 := 6` in the SURFACE numeral spelling
/// (`OfNat.ofNat UInt64 6 (instOfNatUInt64 6)`) — the spelling a real island
/// literal elaborates to, and the corpus's suspected obstacle (f04's note:
/// "a Nat-defaulted literal on the island side").
#[test]
fn probe_e2_nullary_constant_surface_spelling() {
    let mut env = env_uint();
    define(&mut env, "six_s", uint64(), surface_lit(6));

    let side_b = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_constant_function(scratch, name, 6, MachineUIntWidth::U64)
    })
    .expect("nullary mint");

    check_faithful(&env, "six_s", &side_b, &u64_carrier()).expect(
        "MEASURED ADMIT (2026-08-19): the kernel unfolds `OfNat.ofNat UInt64 6 \
         (instOfNatUInt64 6)` down to `UInt64.ofNat 6` and identifies the two sides. \
         The corpus's constant failures (f04-f09) are therefore NOT a kernel-defeq \
         obstacle at either spelling: they live upstream, in the clause path and in \
         the arity-erasing ConstantUint routing probe_e3 pins",
    );
    eprintln!("PROBE-ROW | const 6, nullary, surface | side B: yes | kernel: ADMIT");
}

/// `def const6 (a : UInt64) : UInt64 := 6` — a constant behind an IGNORED
/// parameter. The recognizer reports `ConstantUint` (erasing the arity), and
/// the compiler's ConstantUint routing mints a NULLARY definition — so the
/// reflected side B has the wrong type against a unary side A. Both halves
/// are pinned here, plus the repair that already exists in the frozen
/// producers: the expr route CAN mint the lambda-wrapped constant.
#[test]
fn probe_e3_unary_constant() {
    let mut env = env_uint();
    define(
        &mut env,
        "const6",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), carrier_lit(6)),
    );
    define(
        &mut env,
        "const6_s",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), surface_lit(6)),
    );
    assert_plan_refuses_today(&env, "const6");

    // The recognizer ERASES the parameter: a unary body recognizes as the
    // same ConstantUint a nullary one does. Pinned because a future
    // Constant shape's round trip must re-check arity from the signature.
    assert_eq!(
        recognize_admissible_body(&emitted_const(1)),
        Some(AdmissibleBody::ConstantUint { value: 6, width_bits: 64 })
    );

    // Route 1 — the compiler's actual ConstantUint routing
    // (admit_constant_function): mints nullary `UInt64.ofNat 6`, which is the
    // WRONG ARITY against `fun a => UInt64.ofNat 6`. The kernel refuses.
    let nullary_b = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_constant_function(scratch, name, 6, MachineUIntWidth::U64)
    })
    .expect("nullary mint");
    let refusal = check_faithful(&env, "const6", &nullary_b, &u64_carrier()).expect_err(
        "a nullary side B must never be admitted for a unary definition — this arity \
         erasure is the corpus's suspected `arity-0 mint` defect, measured",
    );
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");

    // Route 2 — the expr reflection CAN mint the lambda-wrapped constant
    // (`fun p0 => UInt64.ofNat 6`), and the kernel admits it. The gap is the
    // clean_island ROUTING (ConstantUint -> nullary mint), not the producers.
    let unary_b = reflect_expr(&env, "6", 1).expect("`6` over [p0] reflects lambda-wrapped");
    check_faithful(&env, "const6", &unary_b, &u64_carrier())
        .expect("MEASURED ADMIT: the lambda-wrapped constant agrees at the kernel");
    check_faithful(&env, "const6_s", &unary_b, &u64_carrier())
        .expect("MEASURED ADMIT: surface numeral spelling, lambda-wrapped");
    eprintln!(
        "PROBE-ROW | const 6 behind a param    | side B: wrong arity via ConstantUint \
         route (REFUSE Disagreement); yes via expr route | kernel: ADMIT via expr route"
    );
}

// ═════════════════════════ (e) nested arithmetic ═════════════════════════

/// The composed tree `(a + b) * a` reads as, on both sides.
fn nested_tree() -> ArithExpr {
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

/// `def nested (a b : UInt64) : UInt64 := (a + b) * a` — the `Composed`
/// call-chain shape, in both side A spellings.
#[test]
fn probe_f_nested_arithmetic_admits() {
    let mut env = env_uint();
    define(
        &mut env,
        "nested",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                carrier_op(
                    "mul",
                    carrier_op("add", Expr::bvar(1), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
    define(
        &mut env,
        "nested_s",
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
    // FLIPPED 2026-08-20: `CleanOriginShape::Composed` landed, so the planner
    // must now read BOTH spellings as exactly this tree — the same ratchet
    // discipline that flipped a/a2/b/c/d when `WrappingBinOp` landed.
    assert_plan_shape(&env, "nested", CleanOriginShape::Composed { expr: nested_tree() });
    assert_plan_shape(&env, "nested_s", CleanOriginShape::Composed { expr: nested_tree() });

    let recognised = recognize_admissible_body(&emitted_nested())
        .expect("the two-call linear chain must recognize as Composed");
    let AdmissibleBody::Composed { expr } = &recognised else {
        panic!("expected Composed; got {recognised:?}");
    };
    let rendered = render_composed(expr);
    assert_eq!(rendered, "((p0 + p1) * p0)", "the exact clean_island rendering");

    let side_b = reflect_expr(&env, &rendered, 2).expect("composed expr reflection");
    check_faithful(&env, "nested", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: carrier-spelled `(a + b) * a`");
    check_faithful(&env, "nested_s", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: surface-spelled `(a + b) * a`");

    // Mutation: `(a + b) * b` must refuse.
    let wrong = reflect_expr(&env, "((p0 + p1) * p1)", 2).expect("reflects");
    assert!(
        matches!(
            check_faithful(&env, "nested", &wrong, &u64_carrier()),
            Err(GateRefusal::Disagreement { .. })
        ),
        "a chain that multiplied by the wrong parameter must be caught"
    );
    eprintln!("PROBE-ROW | (a + b) * a (both forms)  | side B: yes | kernel: ADMIT");
}

/// **THE MEASURED DEPTH CAP** (`COMPOSED_MAX_OPS`). A left-nested chain of
/// exactly that many wrapping adds — in BOTH side-A spellings, since a real
/// island stores the surface one — plans as `Composed` and ADMITS at the
/// kernel through the exact fully-parenthesized rendering `admit_lowering`
/// uses; ONE more op refuses at PLAN time as a capability boundary. Raising
/// the constant without re-measuring here is exactly the drift this probe
/// exists to block.
#[test]
fn probe_f2_composed_depth_cap_measured() {
    let mut env = env_uint();
    // fun a => ((((a + 1) + 1) …) + 1), `ops` ops, carrier spelling.
    let carrier_chain = |ops: usize| {
        let mut acc = Expr::bvar(0);
        for _ in 0..ops {
            acc = carrier_op("add", acc, carrier_lit(1));
        }
        Expr::lam(BinderInfo::Default, uint64(), acc)
    };
    // The same chain in the surface spelling of BOTH the op and the numeral.
    let surface_chain = |ops: usize| {
        let mut acc = Expr::bvar(0);
        for _ in 0..ops {
            acc = surface_op("HAdd", "hAdd", acc, surface_lit(1));
        }
        Expr::lam(BinderInfo::Default, uint64(), acc)
    };
    define(&mut env, "deep", u64_arrows(1), carrier_chain(COMPOSED_MAX_OPS));
    define(&mut env, "deep_s", u64_arrows(1), surface_chain(COMPOSED_MAX_OPS));
    define(&mut env, "too_deep", u64_arrows(1), carrier_chain(COMPOSED_MAX_OPS + 1));
    define(&mut env, "too_deep_s", u64_arrows(1), surface_chain(COMPOSED_MAX_OPS + 1));

    // At the cap: both spellings plan as the SAME Composed tree…
    let plan = plan_clean_origin_body(&env, "deep")
        .expect("the cap itself is inside the measured fragment");
    let CleanOriginShape::Composed { expr } = plan.shape() else {
        panic!("expected Composed at the cap; got {:?}", plan.shape());
    };
    let plan_s = plan_clean_origin_body(&env, "deep_s").expect("surface spelling plans too");
    assert_eq!(plan_s.shape(), plan.shape(), "the two spellings must read as one tree");

    // …and the kernel ADMITS the rendering against BOTH.
    let rendered = render_composed(expr);
    let side_b = reflect_expr(&env, &rendered, 1).expect("the cap-depth rendering reflects");
    check_faithful(&env, "deep", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT (2026-08-20): the cap-depth chain, carrier spelling");
    check_faithful(&env, "deep_s", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT (2026-08-20): the cap-depth chain, surface spelling");

    // MUTATION at depth: the same tree with the OUTERMOST numeral flipped
    // (`… + 1` → `… + 2`) must refuse — depth must not dull the kernel's
    // discrimination.
    let ArithExpr::Bin { op, left, right: _ } = expr.clone() else {
        unreachable!("matched Composed above");
    };
    let wrong_tree =
        ArithExpr::Bin { op, left, right: Box::new(ArithExpr::Operand(ArithOperand::Const(2))) };
    let wrong = reflect_expr(&env, &render_composed(&wrong_tree), 1)
        .expect("the wrong chain still reflects");
    assert!(
        matches!(
            check_faithful(&env, "deep", &wrong, &u64_carrier()),
            Err(GateRefusal::Disagreement { .. })
        ),
        "a wrong final numeral at the cap depth must be caught"
    );

    // One past the cap: a PLAN-time capability refusal naming the boundary,
    // in both spellings.
    for name in ["too_deep", "too_deep_s"] {
        let refusal = plan_clean_origin_body(&env, name)
            .expect_err("past the measured cap the planner must refuse");
        assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
        assert!(!refusal.is_compiler_defect(), "the cap is a capability boundary");
        let note = refusal.note();
        assert!(note.contains("options:"), "v7/D3: {note}");
        assert!(
            note.contains(&COMPOSED_MAX_OPS.to_string()),
            "the refusal must name the measured cap: {note}"
        );
    }
    eprintln!(
        "PROBE-ROW | {COMPOSED_MAX_OPS}-op chain (both forms) | side B: yes | kernel: ADMIT; \
         +1 refuses at plan"
    );
}

// ═════════════════════════ (f) comparison to Bool ═════════════════════════

/// `def lt (a b : UInt64) : Bool := a < b` — NEITHER side-B producer exists:
/// the recognizer has no Bool-comparison shape (an `Rvalue::BinaryOp` body
/// matches nothing), and `admit_expr_function` rejects `<` in term position.
/// This is a "no reflection path" finding, categorically different from a
/// kernel refusal: there is nothing to put to the kernel yet.
#[test]
fn probe_g_bool_comparison_has_no_reflection_path() {
    // Half 1: the body a comparison emitter would produce is NOT recognized.
    assert_eq!(
        recognize_admissible_body(&emitted_lt_bool()),
        None,
        "no AdmissibleBody variant covers `_0 = Lt(_1, _2)`; if this ever recognizes, \
         a Bool-comparison shape has landed and this probe must be rewritten to \
         measure its kernel verdict"
    );

    // Half 2: the expr reflection refuses `<` in term position — over the
    // machine domain AND over Bool. Both refusals are producer-side; the
    // kernel is never reached.
    let mut scratch = env_uint();
    let err = trust_spec_elab::admit_expr_function(
        &mut scratch,
        "lt_probe",
        "p0 < p1",
        &["p0", "p1"],
        &Domain::Machine(MachineUIntWidth::U64),
    )
    .expect_err("`<` is not a machine TERM; the expr fragment is + - * & | ^ / %");
    assert!(
        err.contains("unsupported binary op"),
        "the refusal must be the term-fragment boundary, not a kernel rejection: {err}"
    );

    // And there is no mixed-domain spelling to reach for: admit_expr_function
    // is single-domain by contract (u64 params with a Bool result cannot be
    // stated), and admit_select_function returns a PARAMETER, never the
    // comparison itself. No admit_* function can mint this side B today.
    eprintln!(
        "PROBE-ROW | a < b : Bool              | side B: NO (no recognizer arm, no \
         admit path) | kernel: unreachable"
    );
}

// ═════════════════════════ (h) the Select shape (C5.0) ═════════════════════════

/// `def min2_isl (a b : UInt64) : UInt64 := if a < b then a else b` — the
/// check_faithful measurement Select does NOT yet have. Its existing green
/// lives on the CLAUSE lane (e6 probes f01/f02; trust-certify's
/// `natural_if_island_discharges_against_the_minted_select`), which compares
/// a cited contract by defeq — never an EMITTED body through
/// `plan_clean_origin_body`/`admit_lowering`'s gate.
///
/// Side A is the `ite` term Clean's `elab_if` mints — `ite.{1} UInt64
/// (LT.lt.{0} UInt64 instLTUInt64 a b) (instDecidableUInt64Lt a b) a b`,
/// hand-built but FULL-kernel-checked by `define`, so a wrong construction
/// fails loudly. It is the same term `admit_select_function` builds BY
/// CONSTRUCTION (the 2026-07-25 Option-B ruling), which is exactly why the
/// verdict must be measured rather than assumed: two independent builders of
/// "the same" term is precisely where a drifted level or instance argument
/// would hide.
///
/// Environment: `with_prelude()` — `init_uint_arith` alone lacks `ite`,
/// `LT.lt`, and the Decidable instances.
#[test]
fn probe_h_select_admits() {
    let mut env = Environment::with_prelude();

    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    // Under 2 binders: a = bvar 1, b = bvar 0.
    let lt_prop = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![zero]),
        [
            uint64(),
            Expr::const_(Name::from_string("instLTUInt64"), vec![]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    let dec_inst = Expr::apps(
        Expr::const_(Name::from_string("instDecidableUInt64Lt"), vec![]),
        [Expr::bvar(1), Expr::bvar(0)],
    );
    let ite_body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [uint64(), lt_prop, dec_inst, Expr::bvar(1), Expr::bvar(0)],
    );
    define(
        &mut env,
        "min2_isl",
        u64_arrows(2),
        Expr::lam(BinderInfo::Default, uint64(), Expr::lam(BinderInfo::Default, uint64(), ite_body)),
    );

    // FLIPPED (R2/C5a): the planner reads the ite as the exact Select value.
    let plan = plan_clean_origin_body(&env, "min2_isl")
        .expect("the parameter-select ite is inside the C5a fragment");
    assert_eq!(
        plan.shape(),
        &trust_clean_origin::CleanOriginShape::Select {
            cmp: trust_types::admissible_body::SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        },
        "the plan must denote the exact select the Clean body does"
    );

    // The emitted body a C5a emitter would produce, read back: the 4-block
    // O0 diamond. The recognizer — written for the E6 direction — must read
    // it as the exact Select value.
    let emitted = emitted_select_diamond();
    assert_eq!(
        recognize_admissible_body(&emitted),
        Some(AdmissibleBody::Select {
            cmp: trust_types::admissible_body::SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        }),
        "the O0 diamond must read back as min2's Select"
    );

    // Side B through the frozen producer, into a CLONE.
    let side_b = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_select_function(
            scratch,
            name,
            &[
                Domain::Machine(MachineUIntWidth::U64),
                Domain::Machine(MachineUIntWidth::U64),
            ],
            trust_spec_elab::SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
    })
    .expect("the select side B reflects");
    check_faithful(&env, "min2_isl", &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
        panic!(
            "MEASURED ADMIT expected: side A is the term admit_select_function builds \
             by construction (2026-07-25 Option-B ruling): {refusal:?}"
        )
    });
    eprintln!("PROBE-ROW | if a < b then a else b   | side B: yes (admit_select) | kernel: ADMIT");

    // Paired mutation 1: swapped arms — the max2 body for a min2 declaration.
    let wrong = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_select_function(
            scratch,
            name,
            &[
                Domain::Machine(MachineUIntWidth::U64),
                Domain::Machine(MachineUIntWidth::U64),
            ],
            trust_spec_elab::SelectCmp::Lt,
            0,
            1,
            1,
            0,
        )
    })
    .expect("the wrong body still reflects");
    let refusal = check_faithful(&env, "min2_isl", &wrong, &u64_carrier())
        .expect_err("a body selecting max was accepted for a definition that says min");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");

    // Paired mutation 2: the wrong COMPARISON (Le for Lt). At UInt64 min the
    // two differ only on equality inputs, where both arms return the same
    // value — so this measures whether the kernel distinguishes the
    // DECIDABLE INSTANCE, not the extensional function. Either verdict is a
    // finding; the assertion records the measured one.
    let wrong_cmp = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_select_function(
            scratch,
            name,
            &[
                Domain::Machine(MachineUIntWidth::U64),
                Domain::Machine(MachineUIntWidth::U64),
            ],
            trust_spec_elab::SelectCmp::Le,
            0,
            1,
            0,
            1,
        )
    })
    .expect("the Le body still reflects");
    let refusal = check_faithful(&env, "min2_isl", &wrong_cmp, &u64_carrier()).expect_err(
        "MEASURED: kernel defeq is intensional on the stuck ite — a different \
         comparison instance is a different term",
    );
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

/// The 4-block O0 select diamond, in extractor shape — trust-certify's
/// `min2_verifiable_function`, transplanted (the probes crate cannot reach a
/// `#[cfg(test)]` helper in another crate).
fn emitted_select_diamond() -> VerifiableFunction {
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "min2".into(),
        def_path: "crate::m::min2".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![asn(
                        4,
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(1))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(2))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                    terminator: Terminator::Return,
                },
            ],
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
