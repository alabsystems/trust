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
//!   rendering, `ConstantUint` → `admit_constant_function`, `Select` →
//!   `admit_select_function`, `SelectLiteral` → `admit_select_literal_function`
//!   — the R2/C9 route, added BESIDE the frozen producers after probe_i's
//!   phase-1 "no reflection path" finding). Minted into a CLONE of the
//!   environment, mirroring `emit.rs`.
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
//! | nullary `6` (carrier + surface side A) | yes (nullary mint; and the expr route at ZERO params, l2_p1) | ADMIT — both spellings | `ConstantUint` (flipped 2026-08-22, §6f landing 2) |
//! | unary constant `6` via the OLD nullary-mint route | wrong arity | REFUSE (Disagreement) | still refused, and now a standing control (l2_p3b) |
//! | unary constant `6` via expr route | yes | ADMIT — both spellings | `ConstantUint` (flipped 2026-08-22): this route IS what landing 2 wired |
//! | `(a + b) * a` (carrier + surface side A) | yes | ADMIT | `Composed` (flipped 2026-08-20) |
//! | chain of `COMPOSED_MAX_OPS` ops / one more | yes | ADMIT at the cap | `Composed` at the cap; refused past it (probe_f2) |
//! | `a < b : Bool` | NO — no recognizer arm, no admit path | unreachable | refused |
//! | `a % b` at UInt64, VARIABLE divisor (both spellings) | side A STATES since clean `bad1fd5f8` (probe_i, flipped 2026-08-23); side B **refused** — the frozen producer will not mint a variable divisor (probe_j2) | no comparison exists to make | refused (soundness, not wiring) |
//! | `a % 7` at UInt64, LITERAL divisor (both spellings) | yes — `p0 % 7` mints the total round trip | **ADMIT both spellings; `p0 % 8` mutant REFUSED** (probe_j1, 2026-08-25) | `RawBinOp { Rem }` on the SURFACE spelling (§6f landing 7); the carrier spelling has no row |
//! | `a % 0` at UInt64 | ground `13 % 0` is defeq to `13`; symbolic `a % 0` is NOT defeq to the identity | Clean TOTAL vs Rust PANIC — the divisor rule's reason (probe_j3) | refused on both sides |
//! | `a % 7` via the island-writable `UInt64.ofNat (a.toNat % 7)` round trip | yes (`p0 % 7` literal-divisor mint) | ADMIT (probe_i2, 2026-08-21) | refused: no Rem shape reads THIS spelling |
//! | `if a < b then a else b` | yes (admit_select) | ADMIT; arm/instance mutants refused | `Select` (flipped 2026-08-20, C5a) |
//! | `if a < 10 then a else b` (both numeral spellings) | phase 1: NO producer ("no reflection path", 2026-08-21); phase 2: yes, via the NEW `admit_select_literal_function` | ADMIT both spellings; off-by-one/arm/instance mutants refused | `SelectLiteral` (flipped 2026-08-21, C9) |
//! | `if 10 < a then a else b` (left literal) | NO — unrepresentable in the producer's vocabulary | unreachable | refused (probe_i2) |
//!
//! The constant rows locate the corpus's finding 3 (`f04`–`f09`, every
//! constant probe fails): the bare kernel comparison ADMITS the constant in
//! BOTH spellings, so the compiler-lane failures live upstream of the kernel
//! — in the arity-erasing `ConstantUint` -> nullary-mint routing (measured
//! REFUSED here) and the clause path — not in definitional equality.
//!
//! **§6f LANDING 2 (2026-08-22) acted on exactly that finding.** The routing is
//! repaired: `admit_lowering` reflects a `ConstantUint` reading through
//! `admit_expr_function` at the EMITTED body's arity, which serves the nullary
//! body and the ignored-binder body with one route. `landing2_selection_probes`
//! holds the measurements taken before the flip — including that the two
//! producers mint the SAME term at zero parameters, so this is a routing change
//! and not a semantic one, and that the arity erasure is still refused by the
//! kernel in BOTH wrong directions.
//!
//! **THE REM ROWS ARE UNBLOCKED, and the paragraph that used to stand here was
//! stale (corrected 2026-08-25).** It read: *"the kernel prelude cannot even
//! state side A — `init_uint_arith` seeds wrapping add/sub/mul ONLY … no
//! `HMod UInt64` instance exists anywhere in the pinned clean tree … C8's
//! total-primitive story is therefore STOPPED until the clean sibling's
//! prelude gains `UInt64.mod` + `instHModUInt64` as CHECKED definitions."*
//! That sibling pin move HAPPENED (clean `bad1fd5f8`, carried by the pin this
//! superproject names today), `probe_i` flipped the constant-presence ratchet
//! on 2026-08-23, and §6f landing 7 shipped the `uint.div`/`uint.mod` rows —
//! yet these table rows were left asserting the opposite of the tests below
//! them. Re-measured end to end by `probe_j1`/`probe_j2`/`probe_j3`:
//!
//! | Rem question | measured verdict (2026-08-25, clean pin `99e2128ef2`) |
//! |---|---|
//! | can side A be STATED — `a % b`, `a % 7`? | **yes, in BOTH spellings** — carrier `UInt64.mod` and surface `HMod.hMod .. instHModUInt64`, each through the full `add_decl` check; and the two are DEFEQ to each other (`probe_j2`) |
//! | does the kernel ADMIT `a % 7` against side B? | **yes, both spellings** (`probe_j1`), across two different encodings — the producer mints the round trip `UInt64.ofNat (Nat.mod (UInt64.toNat p0) 7)`, never `UInt64.mod` |
//! | is a wrong divisor refused? | **yes** — `p0 % 8` against a `% 7` declaration is a `Disagreement`, in both spellings (`probe_j1`) |
//! | `a % b` at a VARIABLE divisor? | side A states; **side B REFUSED** by the frozen producer, so there is nothing to compare (`probe_j2`) |
//! | `n % 0`? | Clean is TOTAL where Rust PANICS: ground `13 % 0` is defeq to `13`, but symbolic `a % 0` is **NOT** defeq to the identity — `Nat.mod` recurses on the DIVIDEND, unlike `Nat.div`, whose `a / 0` does collapse to `0` (`probe_j3`, and landing 7's `l7_p6`) |
//! | what may be EMITTED? | a strictly positive LITERAL divisor only — the slice on which the total Clean semantics and the trapping Rust semantics agree at every input |
//!
//! The one C8 claim that still stands is the narrow one: `gcd`'s own `a % b`
//! remains unemittable, because a symbolic divisor needs a real `b != 0`
//! obligation and a MIR-level `if b == 0 { … }` guard does not supply it —
//! at an open `b` the scrutinee is stuck, so the guarded body is not defeq to
//! side A. That is a soundness boundary, not missing wiring.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::{
    COMPOSED_MAX_OPS, CleanOriginShape, EmitRefusal, GateRefusal, check_faithful,
    plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    AdmissibleBody, ArithBinOp, ArithExpr, ArithOperand, RawBinOpKind, recognize_admissible_body,
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
    try_define(env, name, type_, value)
        .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e}"));
}

/// The same insertion, refusal returned as data — for probes whose FINDING is
/// that a spelling cannot enter the environment at all (probe_i measures
/// exactly that for both island spellings of `a % b`).
fn try_define(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .map_err(|e| format!("{e:?}"))
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
            Expr::app(Expr::const_(Name::from_string("instOfNatUInt64"), vec![]), Expr::nat_lit(n)),
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
        Expr::lam(BinderInfo::Default, uint64(), carrier_op("add", Expr::bvar(0), carrier_lit(6))),
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
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(6, 64))],
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
        Expr::lam(BinderInfo::Default, uint64(), carrier_op("sub", Expr::bvar(0), carrier_lit(1))),
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

    // FLIPPED (§6f landing 2, 2026-08-22): this probe's own finding — that the
    // kernel ADMITS the nullary constant in both spellings, so the corpus's
    // failures live UPSTREAM of defeq — is what landing 2 acted on. The planner
    // now reads a nullary carrier numeral as the exact ConstantUint value. The
    // paired mutations and the full round trip are in
    // `landing2_selection_probes` (l2_p1..l2_p3b), measured before this flip.
    assert_plan_shape(&env, "six", CleanOriginShape::ConstantUint { value: 6 });

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
    // FLIPPED (§6f landing 2, 2026-08-22). Route 2 below is the measurement
    // this probe took and landing 2 acted on: the expr reflection CAN mint the
    // lambda-wrapped constant and the kernel admits it, so *"the gap is the
    // clean_island ROUTING (ConstantUint -> nullary mint), not the producers"*.
    // `admit_lowering` now routes `ConstantUint` through the expr producer at
    // the EMITTED body's arity, and the planner reads both spellings as the
    // exact ConstantUint value.
    for side_a in ["const6", "const6_s"] {
        assert_plan_shape(&env, side_a, CleanOriginShape::ConstantUint { value: 6 });
    }

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
                carrier_op("mul", carrier_op("add", Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
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
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(BinderInfo::Default, uint64(), ite_body),
        ),
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
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
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
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
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
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
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

// ═══════════════ (i) remainder — the R2/C8 kernel-first question ═══════════════

/// **THE RATCHET FIRED, AND THIS IS THE FLIP.**
///
/// Until 2026-08-23 this probe asserted the opposite of what it asserts now,
/// and its own text said what to do when it stopped holding:
///
/// > the ratchet below fails the moment the prelude gains either constant …
/// > landed as a deliberate sibling pin move with this probe flipped in the
/// > same commit
///
/// The clean pin `bad1fd5f8` did exactly that. `UInt{N}.div`, `.mod`, `.land`
/// and `.lor` and their `H*` instances entered the prelude as CHECKED
/// definitions through the `toNat`/`ofNat` round trip over total `Nat.div` /
/// `Nat.mod` / `Nat.land` / `Nat.lor` — the add/sub/mul pattern, zero new
/// axioms — the ratchet went red on the superproject pin bump, and §6f landing
/// 7 is the Trust half.
///
/// # What this probe measures NOW
///
/// The C8 record inverted, construct by construct, so the file that carried
/// the blocker carries its removal:
///
/// * both constants are PRESENT and are `Definition`s the kernel checked, not
///   axioms — which is what makes the whole landing possible and would be the
///   thing to re-examine if they ever arrived as assumptions;
/// * the CARRIER spelling `def wmod (a b : UInt64) : UInt64 := UInt64.mod a b`
///   now kernel-checks, where it used to die on `UnknownConst`;
/// * the SURFACE spelling — the one a real island `a % b` actually produces —
///   kernel-checks too.
///
/// # AND THE HALF THAT DID NOT MOVE
///
/// The old reason had two halves. The first is gone; the second STANDS, and it
/// is re-asserted here rather than deleted: side B still refuses a VARIABLE
/// divisor, because `p0 % p1` needs a nonzero side-condition the frozen
/// producer will not assume. That is not a gap waiting to be filled — §6f
/// landing 7 measured that it CANNOT be filled by an emitted guard
/// (`landing7_selection_probes::l7_p6`: `if b == 0 then 0 else a / b` is not
/// definitionally equal to `a / b` at an open divisor, because the `ite`
/// scrutinee is stuck), and Clean's `/`/`%` being TOTAL where Rust's PANIC is
/// what makes emitting the bare operator a wrong binary. So the emittable
/// remainder is exactly the positive-literal divisor, which is what the
/// `uint.div`/`uint.mod` rows carry.
#[test]
fn probe_i_rem_island_spelling_is_statable_since_clean_bad1fd5f8() {
    let prelude = Environment::with_prelude();
    let has = |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_some();

    // The class and the Nat instance, unchanged — kept so the flip is visibly
    // a change of ONE fact rather than a rewrite of the probe.
    assert!(has(&prelude, "HMod.hMod"), "the HMod class is in the prelude");
    assert!(has(&prelude, "instHModNat"), "the Nat instance is still there");

    // THE FLIPPED RATCHET. Both constants are present now, in both
    // environments this file uses.
    for name in ["UInt64.mod", "instHModUInt64", "UInt64.div", "instHDivUInt64"] {
        assert!(
            has(&prelude, name),
            "measured 2026-08-23 at clean pin `bad1fd5f8`: `{name}` is PRESENT in \
             `with_prelude`. If it has gone again, the `uint.div`/`uint.mod` rows are \
             unreachable and §6f landing 7 must be re-measured from this probe."
        );
        assert!(has(&env_uint(), name), "`{name}` must be present in the binop probes' env too");
    }

    // …and they are DEFINITIONS the kernel checked, not axioms. A prelude that
    // supplied these as assumptions would make every verdict downstream rest
    // on them, which is a different accounting entirely.
    for name in ["UInt64.mod", "UInt64.div", "UInt64.land", "UInt64.lor"] {
        let decl = prelude.get_const(&Name::from_string(name)).expect("present");
        assert!(
            decl.value.is_some(),
            "`{name}` carries no value — it is an assumption, not a definition, and nothing \
             emitted may rest on it"
        );
    }

    // MEASURED ADMIT 1 — the carrier spelling, which used to die on
    // `UnknownConst`.
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "wmod",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                carrier_op("mod", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );

    // MEASURED ADMIT 2 — the SURFACE spelling, the one a real island `a % b`
    // produces (pinned node by node at four widths by
    // `landing7_selection_probes::l7_p1`).
    define(
        &mut env,
        "wmod_s",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_op("HMod", "hMod", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );

    // THE HALF THAT STANDS — side B for gcd's own `a % b`: a variable divisor
    // is outside the mintable fragment, and §6f landing 7 measured that it
    // stays outside for a SOUNDNESS reason rather than a wiring one.
    let mut scratch = env_uint();
    let rem_err = trust_spec_elab::admit_expr_function(
        &mut scratch,
        "rem_probe",
        "p0 % p1",
        &["p0", "p1"],
        &Domain::Machine(MachineUIntWidth::U64),
    )
    .expect_err("a variable divisor must still be refused (nonzero side-condition not wired)");
    assert!(rem_err.contains("divisor"), "must name the divisor boundary: {rem_err}");

    eprintln!(
        "PROBE-ROW | a % b at UInt64 (island)  | side A: STATABLE since clean bad1fd5f8 \
         (UInt64.mod + instHModUInt64 are checked definitions) | side B: still refused at a \
         VARIABLE divisor | emittable slice: a POSITIVE LITERAL divisor (rows uint.div, \
         uint.mod)"
    );
}
/// The ONE remainder form whose kernel-defeq question IS reachable today —
/// measured so the C8 blocker report carries the fix's options (v7/D3), not
/// just the refusal. Side A is the island-WRITABLE round-trip spelling
/// `def remlit_isl (a : UInt64) : UInt64 := UInt64.ofNat (a.toNat % 7)`:
/// every constant it needs exists (`UInt64.toNat`/`ofNat`, `HMod.hMod` at
/// Nat via `instHModNat`, the OfNat Nat numeral), hand-built here exactly as
/// the elaborator would spell it and FULL-kernel-checked by `define`. Side B
/// is the EXISTING literal-divisor mint (`p0 % 7` →
/// `UInt64.ofNat (Nat.mod (UInt64.toNat p0) 7)`).
///
/// MEASURED ADMIT: the kernel unfolds `instHModNat` (reducible) down to
/// `Nat.mod` and the OfNat-wrapped Nat numeral down to the literal,
/// identifying the two sides. So the literal-divisor Rem slice has a LIVE
/// kernel path today through the round-trip spelling.
///
/// **REASON REPLACED, 2026-08-23 (§6f landing 7).** This probe used to add
/// *"what it lacks is everything downstream (no Rem in `ArithBinOp`, no
/// `checked_rem`/guarded classification in `RustcTotalPrimitiveMethod`, no
/// planner arm reading this tree, no emitter)"*, and the island `a % 7` SUGAR
/// was blocked by probe_i's missing `instHModUInt64`. Both halves have moved:
/// the instance exists at clean pin `bad1fd5f8`, and the SUGAR is now emitted —
/// `uint.mod` realizes it as a bare `Rvalue::BinaryOp(Rem)` at a strictly
/// positive numeral divisor. What is still unplanned is exactly the term THIS
/// probe hand-builds: the ROUND-TRIP spelling `UInt64.ofNat (a.toNat % 7)`,
/// which no source produces and no side-A reader looks for. The plan refusal
/// below therefore still holds and now pins a different fact — that the lane
/// reads the spelling the elaborator emits, and only that one.
#[test]
fn probe_i2_rem_literal_divisor_round_trip_admits() {
    let mut env = Environment::with_prelude();

    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Level::zero();
    // a.toNat, under 1 binder: a = bvar 0.
    let to_nat_a =
        Expr::app(Expr::const_(Name::from_string("UInt64.toNat"), vec![]), Expr::bvar(0));
    // The island's `7 : Nat` — `OfNat.ofNat Nat 7 (instOfNatNat 7)`.
    let seven_nat = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            nat(),
            Expr::nat_lit(7),
            Expr::app(Expr::const_(Name::from_string("instOfNatNat"), vec![]), Expr::nat_lit(7)),
        ],
    );
    // `a.toNat % 7` — HMod.hMod at Nat through instHModNat, the instance the
    // prelude actually has.
    let hmod_nat = Expr::apps(
        Expr::const_(Name::from_string("HMod.hMod"), vec![zero.clone(), zero.clone(), zero]),
        [
            nat(),
            nat(),
            nat(),
            Expr::const_(Name::from_string("instHModNat"), vec![]),
            to_nat_a,
            seven_nat,
        ],
    );
    define(
        &mut env,
        "remlit_isl",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::app(Expr::const_(Name::from_string("UInt64.ofNat"), vec![]), hmod_nat),
        ),
    );

    // TODAY's planner: refused as a capability boundary — the ratchet a Rem
    // widening must flip in its own commit.
    assert_plan_refuses_today(&env, "remlit_isl");

    // Side B through the frozen literal-divisor mint.
    let side_b = reflect_expr(&env, "p0 % 7", 1).expect("`p0 % 7` is in the mintable fragment");
    check_faithful(&env, "remlit_isl", &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
        panic!(
            "MEASURED ADMIT expected: side A is the round-trip term the mint builds, \
             modulo the reducible instHModNat/OfNat wrappers: {refusal:?}"
        )
    });

    // Paired mutation: the WRONG divisor must refuse — an emitter that baked
    // in 8 for a definition that says 7 must be caught.
    let wrong = reflect_expr(&env, "p0 % 8", 1).expect("the wrong body still reflects");
    let refusal = check_faithful(&env, "remlit_isl", &wrong, &u64_carrier())
        .expect_err("a body computing `a % 8` was accepted for a definition that says `a % 7`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");

    eprintln!(
        "PROBE-ROW | a.toNat % 7 round trip    | side B: yes (literal-divisor mint) | \
         kernel: ADMIT | plan: refused (no Rem shape)"
    );
}

// ════════════════ (i) Select vs LITERAL — R2/C9 (param-vs-const compare) ════════════════

/// Side A for `def min10_isl (a b : UInt64) : UInt64 := if a < 10 then a
/// else b` — the `ite` tree `elab_if` mints, with the comparison's RIGHT
/// operand a numeral instead of a parameter. `rhs` is the numeral term, so
/// one builder serves BOTH spellings (`surface_lit(10)` — what a real island
/// elaborates — and `carrier_lit(10)`, the `Domain::numeral` restatement).
/// Under 2 binders: a = bvar 1, b = bvar 0.
fn ite_lt_literal_body(rhs: Expr) -> Expr {
    let lt_prop = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            uint64(),
            Expr::const_(Name::from_string("instLTUInt64"), vec![]),
            Expr::bvar(1),
            rhs.clone(),
        ],
    );
    // The REAL instance spelling (measured 2026-08-21, the C9 spelling gap):
    // decidability of a literal comparison resolves by reduction to Nat —
    // `instDecidableNatLt` over the parameter's toNat projection chain and
    // the bare Nat literal. The carrier-instance spelling this helper used
    // to hand-build was a fiction no elaborator emits; defeq is intensional
    // on the stuck ite, so the fiction admitted only against itself.
    let _ = rhs;
    let dec_inst = Expr::apps(
        Expr::const_(Name::from_string("instDecidableNatLt"), vec![]),
        [
            Expr::proj(
                Name::from_string("Fin"),
                0,
                Expr::proj(
                    Name::from_string("BitVec"),
                    0,
                    Expr::proj(Name::from_string("UInt64"), 0, Expr::bvar(1)),
                ),
            ),
            Expr::nat_lit(10),
        ],
    );
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [uint64(), lt_prop, dec_inst, Expr::bvar(1), Expr::bvar(0)],
    )
}

/// Both side-A spellings of `min10_isl`, FULL-kernel-checked into a prelude
/// environment: `min10_isl` carries the SURFACE numeral (what a real island's
/// `elab_if` + `OfNat` path mints) and `min10_isl_c` the CARRIER numeral
/// (`UInt64.ofNat 10`).
fn env_with_min10() -> Environment {
    let mut env = Environment::with_prelude();
    for (name, rhs) in [("min10_isl", surface_lit(10)), ("min10_isl_c", carrier_lit(10))] {
        define(
            &mut env,
            name,
            u64_arrows(2),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                Expr::lam(BinderInfo::Default, uint64(), ite_lt_literal_body(rhs)),
            ),
        );
    }
    env
}

/// The emitted 4-block O0 diamond for `if a < LIT then a else b`: identical
/// to [`emitted_select_diamond`] except the comparison's right operand is the
/// literal.
fn emitted_select_literal_diamond(lit: u128) -> VerifiableFunction {
    let mut f = emitted_select_diamond();
    f.name = "min10".into();
    f.def_path = "crate::m::min10".into();
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, opr), .. } =
        &mut f.body.blocks[0].stmts[0]
    else {
        unreachable!("emitted_select_diamond's entry is the comparison");
    };
    *opr = Operand::Constant(ConstValue::Uint(lit, 64));
    f
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

/// R2/C9 phase-1 measurement (2026-08-21): `if a < 10 then a else b` — the
/// param-vs-const compare — had **no reflection path** (the probe-g
/// category): side A kernel-checks in both numeral spellings, but NO frozen
/// producer could mint side B:
///
/// * `admit_select_function` compares two PARAMETERS by signature
///   (`cmp_left: usize, cmp_right: usize`) — a literal comparison operand is
///   unrepresentable in its input vocabulary, not merely refused;
/// * `admit_expr_function`'s term fragment has no `if`/comparison (measured
///   below: "unsupported term shape");
/// * `recognize_select` read the comparison operands through
///   `param_of_operand`, so the emitted literal diamond recognized as `None`
///   — nothing to route.
///
/// Consequence recorded per the plan's C9 row: the widening needed a NEW
/// admit route (`admit_select_literal_function` — side-B territory, with its
/// own forgery pins), not a wider rendering into an existing one. This test
/// pins the half of that finding that must STAY true: the expr-route
/// refusal is the term-fragment boundary, so no future rendering can slide
/// a conditional through `admit_expr_function` unmeasured.
#[test]
fn probe_i_select_literal_no_expr_reflection_path() {
    let mut scratch = env_uint();
    let err = trust_spec_elab::admit_expr_function(
        &mut scratch,
        "min10_probe",
        "if p0 < 10 { p0 } else { p1 }",
        &["p0", "p1"],
        &Domain::Machine(MachineUIntWidth::U64),
    )
    .expect_err("an `if` expression is not in the machine TERM fragment");
    assert!(
        err.contains("unsupported term shape"),
        "the refusal must be the term-fragment boundary, not a kernel rejection: {err}"
    );
    eprintln!(
        "PROBE-ROW | if a < 10 then a else b  | expr route: NO (term fragment) | \
         select route: literal unrepresentable pre-C9"
    );
}

/// R2/C9 phase-2 measurement (2026-08-21): the KERNEL verdict on the literal
/// select, through the NEW admit route the phase-1 finding demanded
/// (`admit_select_literal_function` — see `probe_i_select_literal_no_expr_reflection_path`
/// for why no pre-existing producer could mint this side B).
///
/// Side B is minted in the CARRIER numeral spelling (`Domain::numeral` →
/// `UInt64.ofNat 10`); side A is measured in BOTH spellings — the surface
/// `OfNat.ofNat` tree a real island's `elab_if` mints, and the carrier
/// restatement — so the cross-spelling identification is a measured fact
/// exactly as the a4–a6 arithmetic numeral probes made it for their shape.
///
/// Paired mutations, each one construct wrong, each REFUSED by the kernel:
/// * the literal off by one (11 for 10) — THE C9-distinctive forgery: an
///   emitter that misreads the threshold mints a body that agrees with the
///   declaration everywhere except `a = 10`;
/// * swapped arms (the max body for a min declaration);
/// * Le for Lt — extensionally equal at min-vs-literal only on the boundary,
///   where both arms differ; defeq is intensional on the stuck `ite`
///   (probe_h's measured finding, re-pinned here for the literal tree).
#[test]
fn probe_i_select_literal_admits() {
    let env = env_with_min10();

    // FLIPPED (R2/C9): the planner reads the literal ite as the exact
    // SelectLiteral value — in BOTH side-A numeral spellings.
    for side_a in ["min10_isl", "min10_isl_c"] {
        assert_plan_shape(
            &env,
            side_a,
            CleanOriginShape::SelectLiteral {
                cmp: trust_types::admissible_body::SelectCmp::Lt,
                cmp_param: 0,
                literal: 10,
                then_param: 0,
                else_param: 1,
            },
        );
    }

    // The emitted body a C9 emitter produces, read back: the recognizer —
    // widened with its own forgery pins in trust-types — reads the literal
    // diamond as the exact SelectLiteral value.
    assert_eq!(
        recognize_admissible_body(&emitted_select_literal_diamond(10)),
        Some(AdmissibleBody::SelectLiteral {
            cmp: trust_types::admissible_body::SelectCmp::Lt,
            cmp_param: 0,
            literal: 10,
            then_param: 0,
            else_param: 1,
        }),
        "the literal-compare O0 diamond must read back as min10's SelectLiteral"
    );

    // Side B through the NEW producer, into a CLONE.
    let side_b = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_select_literal_function(
            scratch,
            name,
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
            trust_spec_elab::SelectCmp::Lt,
            0,
            10,
            0,
            1,
        )
    })
    .expect("the select-literal side B reflects");
    for side_a in ["min10_isl", "min10_isl_c"] {
        check_faithful(&env, side_a, &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
            panic!(
                "MEASURED ADMIT expected against `{side_a}`: the reflected ite must \
                 identify with the island tree in both numeral spellings: {refusal:?}"
            )
        });
    }
    eprintln!(
        "PROBE-ROW | if a < 10 then a else b  | side B: yes (admit_select_literal, NEW \
         route) | kernel: ADMIT (both side-A spellings)"
    );

    // Paired mutations — a one-construct-wrong side B must be REFUSED against
    // BOTH side-A spellings, or the widening admits a forgery.
    let mutants: [(&str, trust_spec_elab::SelectCmp, u128, usize, usize); 3] = [
        ("literal off by one", trust_spec_elab::SelectCmp::Lt, 11, 0, 1),
        ("swapped arms", trust_spec_elab::SelectCmp::Lt, 10, 1, 0),
        ("Le for Lt", trust_spec_elab::SelectCmp::Le, 10, 0, 1),
    ];
    for (what, cmp, literal, then_param, else_param) in mutants {
        let wrong = reflect(&env, |scratch, name| {
            trust_spec_elab::admit_select_literal_function(
                scratch,
                name,
                &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
                cmp,
                0,
                literal,
                then_param,
                else_param,
            )
        })
        .expect("the wrong body still reflects");
        for side_a in ["min10_isl", "min10_isl_c"] {
            let refusal = check_faithful(&env, side_a, &wrong, &u64_carrier())
                .unwrap_err_or_panic(what, side_a);
            assert!(
                matches!(refusal, GateRefusal::Disagreement { .. }),
                "{what} vs `{side_a}`: got {refusal:?}"
            );
        }
    }
}

/// `Result::unwrap_err` with a message naming the mutation and the side-A
/// spelling — the probe's refusals must never pass vacuously or anonymously.
trait UnwrapErrNamed<E> {
    fn unwrap_err_or_panic(self, what: &str, side_a: &str) -> E;
}
impl<T: std::fmt::Debug, E> UnwrapErrNamed<E> for Result<T, E> {
    fn unwrap_err_or_panic(self, what: &str, side_a: &str) -> E {
        match self {
            Ok(value) => panic!(
                "the `{what}` mutant was ADMITTED against `{side_a}` (got {value:?}); \
                 a one-construct-wrong side B must be refused"
            ),
            Err(refusal) => refusal,
        }
    }
}

/// R2/C9 boundary pin: the literal on the LEFT of the comparison
/// (`if 10 < a then a else b`) stays OUTSIDE the fragment. The vocabulary
/// places the literal strictly on the comparison's right — on the recognizer,
/// the planner AND the producer (`admit_select_literal_function`'s signature
/// cannot even spell a left literal) — so this side A must keep refusing as a
/// capability boundary, and the mirrored MIR diamond must not recognize.
/// Flipping this pin is a deliberate future widening (`10 < a` ≡ `a > 10`
/// needs the `>` normalization the recognizer's doc already names), never a
/// side effect.
#[test]
fn probe_i2_select_literal_on_the_left_refuses_today() {
    let mut env = Environment::with_prelude();
    let lt_prop = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            uint64(),
            Expr::const_(Name::from_string("instLTUInt64"), vec![]),
            surface_lit(10),
            Expr::bvar(1),
        ],
    );
    let dec_inst = Expr::apps(
        Expr::const_(Name::from_string("instDecidableUInt64Lt"), vec![]),
        [surface_lit(10), Expr::bvar(1)],
    );
    let ite_body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [uint64(), lt_prop, dec_inst, Expr::bvar(1), Expr::bvar(0)],
    );
    define(
        &mut env,
        "min10_flip",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(BinderInfo::Default, uint64(), ite_body),
        ),
    );
    assert_plan_refuses_today(&env, "min10_flip");

    // The mirrored emission: the literal as the comparison's LEFT operand.
    let mut flipped = emitted_select_literal_diamond(10);
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, opl, opr), .. } =
        &mut flipped.body.blocks[0].stmts[0]
    else {
        unreachable!("the diamond's entry is the comparison");
    };
    std::mem::swap(opl, opr);
    assert_eq!(
        recognize_admissible_body(&flipped),
        None,
        "a left-literal compare must not recognize; if it does, a `>` \
         normalization has landed and this pin must be rewritten with its \
         own kernel measurement"
    );
    eprintln!("PROBE-ROW | if 10 < a then a else b  | side B: NO (left literal) | refused");
}

/// R2/C9 SPELLING-GAP pin (2026-08-21, the measurement rule's FOURTH
/// teaching): side A obtained through the REAL island elaboration path —
/// `CleanIslandSession::check_all`, the exact pipeline `clean_origin_mir`
/// drives — never hand-built. The gap this pins: the hand-built probes above
/// admit with the carrier Decidable instance, but the real elaborator
/// resolves a literal comparison's decidability by REDUCTION TO NAT
/// (`instDecidableNatLt (a.toNat-as-Proj-chain) 10`), a different tree the
/// planner refused — so every crate suite was green while the driver-level
/// fixture died at the mint with E0425. A shape is only measured when its
/// side A comes from the producer that will really run.
#[test]
fn probe_i3_select_literal_real_elaboration_admits() {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session
        .check_all(&["def clamp10 (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b"]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    let env = session.environment().expect("an untainted session has an environment");

    // The planner reads the REAL elaborated tree as the exact SelectLiteral.
    assert_plan_shape(
        env,
        "clamp10",
        CleanOriginShape::SelectLiteral {
            cmp: trust_types::admissible_body::SelectCmp::Lt,
            cmp_param: 0,
            literal: 10,
            then_param: 0,
            else_param: 1,
        },
    );

    // Side B through the C9 producer identifies with the REAL side A — and
    // the wrong-literal mutation is refused against it.
    let side_b = reflect(env, |scratch, name| {
        trust_spec_elab::admit_select_literal_function(
            scratch,
            name,
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
            trust_spec_elab::SelectCmp::Lt,
            0,
            10,
            0,
            1,
        )
    })
    .expect("the select-literal side B reflects");
    check_faithful(env, "clamp10", &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
        panic!("MEASURED ADMIT expected against the REAL elaborated tree: {refusal:?}")
    });

    let wrong = reflect(env, |scratch, name| {
        trust_spec_elab::admit_select_literal_function(
            scratch,
            name,
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
            trust_spec_elab::SelectCmp::Lt,
            0,
            11,
            0,
            1,
        )
    })
    .expect("the wrong body still reflects");
    let refusal = check_faithful(env, "clamp10", &wrong, &u64_carrier())
        .expect_err("a drifted literal must be refused against the real tree");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

// ════════════ (j) Rem at UInt64 — the C8 blocker, RE-MEASURED ════════════
//
// The R2/C8 question this file's table used to answer "unreachable — side A
// cannot be STATED" is asked again here, end to end, against whatever clean
// pin the superproject currently names. These probes are deliberately
// INDEPENDENT of `landing7_selection_probes`: landing 7 drives side A through
// the real island session (`CleanIslandSession::check_all`), whereas these
// hand-build both spellings and put them through `add_decl`, the same way
// every other probe in this file does. Two different roads to the same three
// verdicts is the point — if they ever disagree, one of them is measuring a
// spelling nobody produces.
//
// Nothing here is a widening request. The `uint.mod` row already landed
// (§6f landing 7); what these probes pin is WHY it is shaped the way it is,
// in this file's own vocabulary, so the C8 row in the table above stops
// contradicting the code under it.

/// The island surface spelling of `%` at `UInt64`:
/// `HMod.hMod UInt64 UInt64 UInt64 instHModUInt64 lhs rhs`.
fn rem_surface(lhs: Expr, rhs: Expr) -> Expr {
    surface_op("HMod", "hMod", lhs, rhs)
}

/// The carrier spelling: `UInt64.mod lhs rhs`.
fn rem_carrier(lhs: Expr, rhs: Expr) -> Expr {
    carrier_op("mod", lhs, rhs)
}

/// **(1) + (2) — `a % 7` at `UInt64` is STATABLE in both spellings, and the
/// kernel ADMITS it against the frozen producer's side B.**
///
/// Side A is built twice and `define`d, so a malformed term fails at
/// `add_decl` rather than measuring nothing:
///
/// ```text
/// carrier:  def rem7_c (a : UInt64) : UInt64 := UInt64.mod a (UInt64.ofNat 7)
/// surface:  def rem7_s (a : UInt64) : UInt64 :=
///             HMod.hMod UInt64 UInt64 UInt64 instHModUInt64 a
///                       (OfNat.ofNat UInt64 7 (instOfNatUInt64 7))
/// ```
///
/// Side B is the FROZEN producer, unchanged: `admit_expr_function("p0 % 7")`,
/// which does NOT mint `UInt64.mod` at all — it mints the total round trip
/// `UInt64.ofNat (Nat.mod (UInt64.toNat p0) 7)` (`trust_spec_elab`'s `Div`/
/// `Rem` arm). So this ADMIT is a real kernel identification across two
/// different encodings, not a syntactic match: the kernel must unfold
/// `instHModUInt64` and `UInt64.mod` down to the same `Nat.mod` round trip and
/// reduce `UInt64.toNat (OfNat.ofNat UInt64 7 _)` to the literal `7`.
///
/// MEASURED 2026-08-25 at clean pin `99e2128ef2` — ADMIT in BOTH spellings,
/// with the wrong-divisor mutant REFUSED in both.
#[test]
fn probe_j1_rem_literal_divisor_both_spellings_admit() {
    let mut env = Environment::with_prelude();

    // The constants side A needs are DEFINITIONS with an EMPTY axiom closure.
    // The sibling's claim is "checked, axiom-free through total `Nat.mod`", and
    // an ADMIT that rested on an assumed `UInt64.mod` would be a different
    // accounting entirely — so it is checked here, from the consumer's side,
    // rather than taken on the sibling's word.
    for name in ["UInt64.mod", "instHModUInt64"] {
        let decl = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be present in `with_prelude`"));
        assert!(decl.value.is_some(), "`{name}` is an assumption, not a definition");
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            deps.is_empty(),
            "`{name}` must be AXIOM-FREE — the Rem lane may not rest on assumptions; got {:?}",
            deps.iter().map(ToString::to_string).collect::<Vec<_>>()
        );
    }

    // (1) — side A can be STATED. This is the assertion that flipped.
    define(
        &mut env,
        "rem7_c",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), rem_carrier(Expr::bvar(0), carrier_lit(7))),
    );
    define(
        &mut env,
        "rem7_s",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), rem_surface(Expr::bvar(0), surface_lit(7))),
    );

    // (2) — the frozen producer's side B, and the ADMIT.
    let side_b = reflect_expr(&env, "p0 % 7", 1)
        .expect("a positive literal divisor is inside the frozen producer's fragment");
    for name in ["rem7_c", "rem7_s"] {
        check_faithful(&env, name, &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
            panic!(
                "MEASURED ADMIT expected for `{name}`: the kernel must identify the island \
                 spelling of `a % 7` with the producer's `UInt64.ofNat (Nat.mod (UInt64.toNat \
                 p0) 7)` round trip: {refusal:?}"
            )
        });
    }

    // (2, paired mutation) — a one-construct-wrong divisor must be REFUSED, or
    // the ADMIT above is a rubber stamp.
    let wrong = reflect_expr(&env, "p0 % 8", 1).expect("the wrong body still reflects");
    for name in ["rem7_c", "rem7_s"] {
        let Err(refusal) = check_faithful(&env, name, &wrong, &u64_carrier()) else {
            panic!("a body computing `a % 8` was accepted for `{name}`, which says `a % 7`")
        };
        assert!(
            matches!(refusal, GateRefusal::Disagreement { .. }),
            "the wrong divisor must be a Disagreement for `{name}`; got {refusal:?}"
        );
    }

    // THE SPELLING ASYMMETRY, which is a fact about the TABLE, not the kernel.
    // Both spellings are kernel-equal (probe_j2 pins that directly), but the
    // selection table keys `uint.mod` on the SURFACE head only — which is
    // correct, because `l7_p1` measured that no source produces the carrier
    // method. A carrier-spelled island therefore states, admits, and still has
    // no realization.
    assert_plan_shape(
        &env,
        "rem7_s",
        CleanOriginShape::RawBinOp {
            op: RawBinOpKind::Rem,
            left: ArithOperand::Param(0),
            right: ArithOperand::Const(7),
        },
    );
    let carrier_plan = plan_clean_origin_body(&env, "rem7_c")
        .expect_err("the carrier spelling has no selection row and must refuse");
    assert!(
        matches!(carrier_plan, EmitRefusal::NotEmittable { .. }),
        "got {carrier_plan:?}"
    );
    assert!(!carrier_plan.is_compiler_defect(), "a missing row is not a compiler defect");

    eprintln!(
        "PROBE-ROW | a % 7 at UInt64 (island)   | side A: STATABLE in BOTH spellings | \
         side B: yes (frozen producer, round-trip encoding) | kernel: ADMIT both, wrong \
         divisor REFUSED | plan: RawBinOp(Rem) on the SURFACE spelling; carrier spelling \
         has no row"
    );
}

/// **(1) for a SYMBOLIC divisor, and where it stops.**
///
/// `def remv (a b : UInt64) : UInt64 := a % b` STATES in both spellings — the
/// prelude gained everything needed for that. The two spellings are also
/// definitionally EQUAL to each other, measured here by handing the carrier
/// definition's own body to `check_faithful` against the surface definition.
/// (That side B is a kernel term, not an emitter product; this probe is
/// asking a pure spelling-equivalence question, and says so rather than
/// pretending a producer minted it.)
///
/// What does NOT exist is an emittable side B: the frozen producer refuses a
/// variable divisor outright. That refusal is a SOUNDNESS boundary, not
/// missing wiring — see `probe_j3` for the value that makes it one.
#[test]
fn probe_j2_rem_symbolic_divisor_states_but_has_no_side_b() {
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "remv_c",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(BinderInfo::Default, uint64(), rem_carrier(Expr::bvar(1), Expr::bvar(0))),
        ),
    );
    define(
        &mut env,
        "remv_s",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(BinderInfo::Default, uint64(), rem_surface(Expr::bvar(1), Expr::bvar(0))),
        ),
    );

    // The two spellings denote the same function to the kernel.
    let carrier_body = env
        .get_const(&Name::from_string("remv_c"))
        .and_then(|c| c.value.clone())
        .expect("`remv_c` was just defined and carries a value");
    check_faithful(&env, "remv_s", &carrier_body, &u64_carrier()).unwrap_or_else(|refusal| {
        panic!(
            "MEASURED ADMIT expected: `HMod.hMod .. instHModUInt64 a b` must unfold to \
             `UInt64.mod a b`, or the surface spelling means something else: {refusal:?}"
        )
    });

    // …and there is no emittable side B for it.
    let err = reflect_expr(&env, "p0 % p1", 2)
        .expect_err("a VARIABLE divisor must be refused by the frozen producer");
    assert!(err.contains("divisor"), "the refusal must name the divisor boundary: {err}");
    assert!(
        err.contains("nonzero side-condition"),
        "the refusal must name the MISSING OBLIGATION, not merely decline: {err}"
    );

    assert_plan_refuses_today(&env, "remv_s");
    assert_plan_refuses_today(&env, "remv_c");

    eprintln!(
        "PROBE-ROW | a % b at UInt64 (symbolic) | side A: STATABLE in both spellings, and \
         the two are DEFEQ | side B: REFUSED by the frozen producer (variable divisor) | \
         kernel verdict: unreachable — no side B exists to compare | plan: refused"
    );
}

/// **(3) THE ZERO-DIVISOR FINDING — why `a % b` cannot simply be emitted.**
///
/// Lean's `Nat.mod` is TOTAL and gives `n % 0 = n`; Rust's `%` PANICS. So a
/// declaration `def f (a b : UInt64) := a % b` and a MIR body
/// `_0 = Rem(a, b); return` are DIFFERENT FUNCTIONS at `b = 0` — the
/// declaration has a value there and the binary traps. This probe measures the
/// three facts that fix what an emitted body would have to do:
///
/// * **GROUND, zero divisor** — `13 % 0` IS definitionally `13`. The kernel
///   really does carry the total semantics, so this is not a theoretical gap.
/// * **SYMBOLIC, zero divisor** — `fun a => a % 0` is NOT definitionally the
///   identity. `Nat.mod` recurses on the DIVIDEND (via `Nat.modCore`'s fuel),
///   so at an open `a` the term is stuck. Note the contrast landing 7 records
///   for `/`: `a / 0` DOES collapse to the constant `0` at an open `a`, because
///   `Nat.div` recurses on the divisor. `%` and `/` are not symmetric here.
/// * **SIDE B** — the frozen producer refuses a literal `0` divisor for the
///   same reason it refuses a variable one.
///
/// **What the emitted body would have to do.** A LITERAL nonzero divisor is
/// total on both sides and needs nothing: the two semantics agree on every
/// input, which is exactly the slice `uint.mod` emits. A SYMBOLIC divisor
/// needs a real `b != 0` obligation discharged before emission — and NOT a
/// `if b == 0 { .. } else { a % b }` guard bolted onto the MIR: at an open `b`
/// the scrutinee is stuck, the guarded body is not defeq to side A, and
/// `check_faithful` refuses it (`l7_p6`). Teaching the recognizer to COLLAPSE
/// such a guard would restore defeq by making the guard invisible to the
/// kernel, which is the one move this lane must never make.
#[test]
fn probe_j3_rem_zero_divisor_is_total_in_clean_and_panicking_in_rust() {
    let mut env = Environment::with_prelude();

    // GROUND: the total semantics are really there.
    define(&mut env, "rem_ground", uint64(), rem_surface(surface_lit(13), surface_lit(0)));
    define(&mut env, "thirteen", uint64(), carrier_lit(13));
    let thirteen = env
        .get_const(&Name::from_string("thirteen"))
        .and_then(|c| c.value.clone())
        .expect("value");
    check_faithful(&env, "rem_ground", &thirteen, &u64_carrier()).unwrap_or_else(|refusal| {
        panic!(
            "MEASURED ADMIT expected: Lean's total `Nat.mod` makes `13 % 0` the VALUE 13 at \
             UInt64, where a Rust `%` would trap. If this ever refuses, the divisor rule was \
             derived from semantics the prelude no longer has: {refusal:?}"
        )
    });

    // SYMBOLIC: and yet the kernel cannot reduce `a % 0` to `a`.
    define(
        &mut env,
        "rem_zero_open",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), rem_surface(Expr::bvar(0), surface_lit(0))),
    );
    define(
        &mut env,
        "ident_u64",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), Expr::bvar(0)),
    );
    let identity = env
        .get_const(&Name::from_string("ident_u64"))
        .and_then(|c| c.value.clone())
        .expect("value");
    let refusal = check_faithful(&env, "rem_zero_open", &identity, &u64_carrier()).expect_err(
        "MEASURED REFUSAL expected: `Nat.mod` recurses on the DIVIDEND, so `a % 0` is stuck \
         at an open `a` and is NOT definitionally the identity — unlike `a / 0`, which does \
         collapse to `0` (landing 7's l7_p6)",
    );
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");

    // SIDE B refuses the literal zero, for the same stated reason as a variable.
    let err = reflect_expr(&env, "p0 % 0", 1)
        .expect_err("a literal ZERO divisor must be refused by the frozen producer");
    assert!(err.contains("divisor"), "must name the divisor boundary: {err}");

    // …while the literal NONZERO divisor is the slice that is total on both
    // sides, and it mints.
    let _total_slice = reflect_expr(&env, "p0 % 7", 1)
        .expect("a strictly positive literal divisor is total in Clean AND in Rust");

    eprintln!(
        "PROBE-ROW | n % 0 at UInt64            | GROUND `13 % 0` = 13 (kernel ADMIT: Clean \
         is TOTAL where Rust PANICS) | SYMBOLIC `a % 0` NOT defeq to identity (Nat.mod \
         recurses on the DIVIDEND; contrast `a / 0` = 0) | side B refuses both a ZERO and a \
         VARIABLE divisor | emittable slice: strictly positive LITERAL divisor only"
    );
}
