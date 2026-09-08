// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f LANDING 3 — the probe battery, measured BEFORE the table moved.**
//!
//! Landing 2 left a ranked MISS list. This file takes it in order and measures
//! each candidate under landing 1's discipline, with ONE change of method that
//! is itself the landing's methodological finding:
//!
//! > **Side A comes from the REAL island elaborator, never from a hand-built
//! > term.** `trust_certify::clean_island::CleanIslandSession::check_all` is
//! > the exact pipeline `clean_origin_mir` drives, and it is available on the
//! > fast lane. R2/C9's spelling gap (probe_i3) was a hand-built side A that
//! > admitted while the real elaboration refused; landing 3 measures every
//! > candidate against the producer that will really run, and **three of its
//! > four findings are only visible that way** (l3_p1, l3_p5, l3_p6).
//!
//! Everything else is landing 1's discipline unchanged: side B through a
//! `trust_spec_elab` producer into a CLONE of the environment, the verdict
//! from [`check_faithful`] at the carrier, and every ADMIT paired with a
//! one-construct-wrong MUTATION that must be REFUSED.
//!
//! # What was measured, and what landed
//!
//! | ranked MISS | measured verdict | landed? |
//! |---|---|---|
//! | 1. `Nat` numeral as a WHOLE body | side A's REAL spelling is `OfNat.ofNat Nat 5 (instOfNatNat 5)`, not the `Nat` literal l2_p4 hand-built; the kernel still ADMITs. Blocked TWICE on this side: `AdmissibleBody` cannot gain a variant without an arm in the gate-free E6 import direction, and the row would be the THIRD MIR alias, which `h_c` pins closed | **no** — refused, with both blockers measured |
//! | 2. constant `ite` ARM | **ADMIT** at `<` and `<=`, param-vs-param and param-vs-literal comparisons, one arm or both, arity 1 and 2; wrong-value, swapped-arm, param-for-const and Le-for-Lt mutants REFUSED | **YES** — no new row: the select rows' DATAFLOW reach |
//! | 3. COMPUTED `ite` condition | side A elaborates, but its decidability instance is a `Nat.rec`-headed NORMAL FORM of the modular reduction — side B would have to reproduce an elaborator normal form, not spell an operand | no — refused, reason REPLACED |
//! | 4. numeral on the comparison's LEFT | **does not elaborate at all**: the bare numeral types as `Nat` and the comparison is a type mismatch. The blocker is `first-party/clean`, upstream of the producer vocabulary the ledger blamed | no — refused, reason REPLACED |
//! | 5–8 | already measured (probe_mod, e2, `recursion_boundary_probes::gcd`, e4); no verdict moved | no |
//! | NEW: `a == b` as an `ite` condition | the real elaborator mints `Eq Bool (BEq.beq …) Bool.true`, which the planner refuses; the `select.eq` row's `Eq {C} a b` spelling is reachable from `a = b` and only from there | no — recorded as a measured MISS |
//!
//! # THE FINDING THAT PICKED THE ROW (candidate 2), and why it is not a row
//!
//! For the third landing running, the capability increment was **not a row**.
//! Landing 2's was a second side-A ROUTE; this one is not even that. The
//! kernel HEAD is unchanged — `ite` at `<` is `ite` at `<` whether its arms
//! are parameters or numerals — so no selector, no row and no realization
//! moves. What moved is the ARMS, and an arm is dataflow, which side B owns.
//! That is `table.rs`'s own invariant (*"the table selects VOCABULARY, the
//! readers own DATAFLOW"*) instantiated a second time, and it is why this
//! landing's diff is in the reader, the producer and the planner rather than
//! in the table.

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::table::{CarrierClass, MirShape, RowContext, row};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, check_faithful, plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth, SelectOperand};
use trust_types::admissible_body::{
    AdmissibleBody, ArithOperand, GeneralSelectBody, SelectCmp, recognize_admissible_body,
    recognize_select_general,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ───────────────────── side A: the REAL island elaborator ─────────────────────

/// Elaborate `sources` through the pipeline `clean_origin_mir` drives and hand
/// back the environment. A rejected batch panics: a probe that measured a
/// half-built environment would measure nothing.
fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn uint_ty(bits: u32) -> Expr {
    Expr::const_(Name::from_string(&format!("UInt{bits}")), vec![])
}

fn carrier_of(bits: u32) -> Carrier {
    carrier_at(&uint_ty(bits), &Ty::Int { width: bits, signed: false })
        .expect("UIntN -> uN is the exact-width carrier and must be granted")
}

fn u64_carrier() -> Carrier {
    carrier_of(64)
}

fn machine(bits: u32) -> Domain {
    Domain::Machine(match bits {
        8 => MachineUIntWidth::U8,
        16 => MachineUIntWidth::U16,
        32 => MachineUIntWidth::U32,
        64 => MachineUIntWidth::U64,
        other => panic!("{other} is not a machine width this battery measures"),
    })
}

// ───────────────────────── side B: mint into a CLONE ─────────────────────────

/// Mint side B into a CLONE of `env` (mirroring `emit.rs`: a check must not
/// mutate the environment it checks) and return the reflected body term.
fn reflect(
    env: &Environment,
    mint: impl FnOnce(&mut Environment, &str) -> Result<trust_spec_elab::Admission, String>,
) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let name = "probe_landing3_reflection";
    mint(&mut scratch, name)?;
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .ok_or_else(|| "the reflected definition carries no value".to_owned())
}

/// Side B through the §6f landing 3 GENERAL select route.
#[allow(clippy::too_many_arguments)]
fn reflect_general_select(
    env: &Environment,
    arity: usize,
    bits: u32,
    cmp: trust_spec_elab::SelectCmp,
    cmp_left: usize,
    cmp_right: SelectOperand,
    then_arm: SelectOperand,
    else_arm: SelectOperand,
) -> Result<Expr, String> {
    let domains: Vec<Domain> = (0..arity).map(|_| machine(bits)).collect();
    reflect(env, |scratch, name| {
        trust_spec_elab::admit_select_operands_function(
            scratch, name, &domains, cmp, cmp_left, cmp_right, then_arm, else_arm,
        )
    })
}

/// Assert the kernel REFUSES `side_b` for `side_a`, naming the mutation. A
/// refusal that passes anonymously measures nothing.
fn refused(env: &Environment, side_a: &str, side_b: &Expr, carrier: &Carrier, what: &str) {
    match check_faithful(env, side_a, side_b, carrier) {
        Ok(value) => panic!(
            "the `{what}` mutant was ADMITTED against `{side_a}` (got {value:?}); a \
             one-construct-wrong side B must be refused, or the ADMITs in this file measure a \
             gate that admits everything"
        ),
        Err(refusal) => assert!(
            matches!(refusal, GateRefusal::Disagreement { .. }),
            "`{what}` vs `{side_a}`: expected a value-level disagreement, got {refusal:?}"
        ),
    }
}

/// The flipped ratchet: the planner reads this def as EXACTLY this shape.
fn assert_plan_shape(env: &Environment, name: &str, expected: CleanOriginShape) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    assert_eq!(plan.shape(), &expected, "`{name}` planned the WRONG shape");
}

/// Pin that TODAY's planner refuses this def as a capability boundary.
fn assert_plan_refuses_today(env: &Environment, name: &str) {
    let refusal =
        plan_clean_origin_body(env, name).expect_err("this shape has no row yet; planning refuses");
    assert!(
        matches!(refusal, EmitRefusal::NotEmittable { .. }),
        "expected today's capability refusal for `{name}`; got {refusal:?}"
    );
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is not a compiler defect");
}

// ───────────────── the emitted MIR, in extractor shape ─────────────────

/// The four-block O0 select diamond with OPERAND arms and an operand
/// comparison right-hand side — the MIR the §6f landing 3 emitter builds.
/// `arity` parameters, all at `bits`.
fn emitted_general_diamond(
    arity: usize,
    bits: u32,
    cmp: BinOp,
    cmp_left: usize,
    cmp_right: ArithOperand,
    then_arm: ArithOperand,
    else_arm: ArithOperand,
) -> VerifiableFunction {
    let ty = Ty::Int { width: bits, signed: false };
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    let operand = |o: ArithOperand| match o {
        ArithOperand::Param(index) => Operand::Copy(Place::local(index + 1)),
        ArithOperand::Const(value) => Operand::Constant(ConstValue::Uint(value, bits)),
    };
    let select_temp = arity + 1;
    let cmp_local = arity + 2;
    let mut locals: Vec<LocalDecl> =
        (0..=arity).map(|index| LocalDecl { index, ty: ty.clone(), name: None }).collect();
    locals.push(LocalDecl { index: select_temp, ty: ty.clone(), name: None });
    locals.push(LocalDecl { index: cmp_local, ty: Ty::Bool, name: None });
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::m::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![asn(
                        cmp_local,
                        Rvalue::BinaryOp(
                            cmp,
                            Operand::Copy(Place::local(cmp_left + 1)),
                            operand(cmp_right),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(cmp_local)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![asn(select_temp, Rvalue::Use(operand(then_arm)))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(select_temp, Rvalue::Use(operand(else_arm)))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(select_temp))))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: arity,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

// ═══════ L3-P1 — ranked MISS 1: a `Nat` numeral as the WHOLE body. REFUSED ═══════

/// **Candidate 1, re-measured at the REAL elaborator and refused, with BOTH
/// blockers pinned.**
///
/// Landing 2 recorded this MISS with one blocker (side B's reader has no arm)
/// and one complication (that reader also feeds the gate-free E6 import
/// direction). This landing measures three things landing 2 did not:
///
/// 1. **l2_p4's side A was a probe fiction.** It hand-built `Expr::nat_lit(5)`.
///    The REAL elaborator mints the SURFACE spelling `OfNat.ofNat.{0} Nat 5
///    (instOfNatNat 5)` for `def five : Nat := 5`. The kernel still ADMITs
///    `Domain::Nat`'s mint against it, so the verdict survives the correction —
///    but the correction had to be made, because R2/C9's teaching is that a
///    shape is only measured when its side A comes from the producer that will
///    really run.
/// 2. **The E6 question has a MECHANICAL answer, not a judgement.**
///    `trust_certify::clean_island::admit_function_into` matches
///    `recognize_admissible_body(func)?` EXHAUSTIVELY, with no wildcard arm. A
///    new `AdmissibleBody` variant therefore cannot widen the CALL direction
///    alone — it is a compile error in the import direction until someone
///    writes that arm, and writing it widens what may become a defining
///    equation with no side A and no kernel gate. The variant set is pinned
///    below by an exhaustive match in THIS file, so a future variant is a
///    review event here too.
/// 3. **The row is closed off independently, by H-C.** A whole-body `Nat`
///    constant is emitted as a CALL to the bignum runtime, so its realization
///    is `MirShape::Call(Fixed(NatFromU64))` — which `nat.lit` ALREADY
///    realizes. That would be the THIRD aliasing pair, and
///    `table_controls::h_c_shared_mir_realizations_are_declared_and_separated`
///    pins the set at exactly two. Landing 2's escape (a second side-A route on
///    the existing row) is unavailable: `nat.lit` sits at
///    `RowContext::RecursionArm` and a whole body is `RowContext::Body`, and a
///    row carries exactly ONE context. One vocabulary item in two LAYERS is
///    unrepresentable in the row type — the dual of landing 2's one vocabulary
///    item in two POSITIONS, and the honest statement is that the table would
///    have to change shape, which is not a thing to do in passing.
#[test]
fn l3_p1_nat_whole_body_numeral_is_refused_with_both_blockers_measured() {
    let env = island(&["def five : Nat := 5"]);

    // (1a) Side A's REAL spelling — the surface `OfNat.ofNat`, not a literal.
    let side_a = env
        .get_const(&Name::from_string("five"))
        .and_then(|c| c.value.clone())
        .expect("the island registered `five`");
    let (head, args) = uncurry(&side_a);
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "OfNat.ofNat"),
        "MEASURED: the real elaborator mints the SURFACE numeral for a `Nat` body, not the \
         kernel literal `l2_p4` hand-built. If this ever becomes a bare literal, l2_p4's \
         side A is valid again and this note must be rewritten: {side_a:?}"
    );
    assert_eq!(args.len(), 3, "OfNat.ofNat takes the type, the literal and the instance");

    // (1b) The kernel verdict SURVIVES the corrected side A: `Domain::Nat`'s
    // mint still identifies with the real tree, and its mutation is refused.
    let nat_carrier = carrier_at(&Expr::const_(Name::from_string("Nat"), vec![]), &Ty::BignumNat)
        .expect("Nat carries at the bignum runtime type");
    let side_b = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_expr_function(scratch, name, "5", &[], &Domain::Nat)
    })
    .expect("`Domain::Nat` mints a nullary bignum constant");
    check_faithful(&env, "five", &side_b, &nat_carrier)
        .expect("MEASURED ADMIT against the REAL side A, not the hand-built one");
    let wrong = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_expr_function(scratch, name, "6", &[], &Domain::Nat)
    })
    .expect("the wrong body still reflects");
    refused(&env, "five", &wrong, &nat_carrier, "wrong Nat constant (6 for 5)");

    // (2) The E6 vocabulary is pinned BY TYPE. This match is exhaustive with
    // no wildcard: a new `AdmissibleBody` variant fails compilation HERE as
    // well as in `trust_certify::clean_island::admit_function_into`, which is
    // the mechanical reason a reader widening cannot be CALL-only if it is
    // spelled as a variant.
    fn e6_vocabulary(body: &AdmissibleBody) -> &'static str {
        match body {
            AdmissibleBody::ConstantUint { .. } => "constant",
            AdmissibleBody::Projection { .. } => "projection",
            AdmissibleBody::Arithmetic { .. } => "arithmetic",
            AdmissibleBody::Composed { .. } => "composed",
            AdmissibleBody::Select { .. } => "select",
            AdmissibleBody::SelectLiteral { .. } => "select-literal",
            // The merged E6 per-field/checked-arith series, named as
            // control_12's twin pin does.
            AdmissibleBody::ConstantInt { .. } => "constant-int",
            AdmissibleBody::FieldProjection { .. } => "field-projection",
            AdmissibleBody::ComparisonBool { .. } => "comparison-bool",
            AdmissibleBody::BoolBinary { .. } => "bool-binary",
            AdmissibleBody::CheckedArithmetic { .. } => "checked-arithmetic",
            AdmissibleBody::GuardedNarrow { .. } => "guarded-narrow",
            AdmissibleBody::WidenedEq { .. } => "widened-eq",
            AdmissibleBody::AggregateFields { .. } => "aggregate-fields",
        }
    }
    assert_eq!(
        e6_vocabulary(&AdmissibleBody::ConstantUint { value: 5, width_bits: 64 }),
        "constant"
    );

    // (3) The row is closed by H-C, and this is what makes that checkable
    // rather than asserted: the realization a whole-body `Nat` constant needs
    // is already taken, at a DIFFERENT layer, by a row that cannot also be a
    // body row.
    let nat_lit = row("nat.lit").expect("the bignum numeral row exists");
    assert_eq!(nat_lit.context, RowContext::RecursionArm);
    assert!(
        matches!(nat_lit.mir, MirShape::Call(_)),
        "if `nat.lit` stops being realized as a call, this blocker has changed and the MISS \
         entry must be re-measured: {:?}",
        nat_lit.mir
    );
    assert_eq!(nat_lit.carrier, CarrierClass::BignumNat);

    // (4) And TODAY's planner keeps refusing, which is the boundary this
    // landing deliberately does not move.
    assert_plan_refuses_today(&env, "five");
    eprintln!(
        "PROBE-ROW | def five : Nat := 5       | side A: REAL = OfNat.ofNat | kernel: ADMIT | \
         blocked by the E6 variant coupling AND by H-C | MISS (recorded, not added)"
    );
}

/// Uncurry an application spine — the probe's own reading of side A, so it
/// never depends on `emit.rs`'s.
fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut cursor = expr;
    let mut args = Vec::new();
    while let ExprKind::App(function, argument) = cursor.kind() {
        args.push(&**argument);
        cursor = &**function;
    }
    args.reverse();
    (cursor, args)
}

/// The head of an application spine.
fn head_of(expr: &Expr) -> &Expr {
    uncurry(expr).0
}

/// The name of a `Const` node, or `None` for anything else.
///
/// Used instead of a substring search over `format!("{expr}")`: since clean
/// `6d1663115` the `Display` impl speaks Lean notation, so a head constant with
/// an entry in its notation table — `Eq`, `LT.lt`, `BEq.beq`, the `H*` family,
/// `OfNat.ofNat` — is rendered as an operator and its implicit type and
/// instance arguments are not rendered at all. `Display` is a human channel; a
/// probe that reads a term through it is measuring the printer.
fn const_name(expr: &Expr) -> Option<String> {
    match expr.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// The comparison spine of an `ite`-bodied definition: peel the binders, check
/// the body really is `ite {C} prop inst then else`, and hand back the
/// PROPOSITION's own arguments (`{C} inst lhs rhs` for a `LT.lt`).
fn comparison_spine(env: &Environment, name: &str) -> Vec<Expr> {
    let body = env
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("`{name}` is a definition with a value"));
    let mut cursor = &body;
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = &**inner;
    }
    let (head, args) = uncurry(cursor);
    assert_eq!(
        const_name(head).as_deref(),
        Some("ite"),
        "`{name}`'s body must still be an `ite`"
    );
    assert_eq!(args.len(), 5, "`ite` is `{{C}} prop inst then else`");
    let (cmp_head, cmp_args) = uncurry(args[1]);
    assert_eq!(
        const_name(cmp_head).as_deref(),
        Some("LT.lt"),
        "`{name}`'s condition must be an `LT.lt` proposition"
    );
    cmp_args.into_iter().cloned().collect()
}

// ═══════════ L3-P2 — ranked MISS 2: a CONSTANT `ite` ARM. ADMIT ═══════════

/// **Candidate 2, the row this landing lands: `if a < b then a else 0`.**
///
/// Every layer measured separately, in the order the pipeline runs them:
///
/// * **side A** — the REAL elaboration. Its else arm is `UInt64.ofNat 0`, the
///   CARRIER numeral spelling, which is exactly what `Domain::numeral` mints —
///   so the producer and the elaborator agree by construction here, and the
///   probe measures rather than assumes it (probe_h's rule).
/// * **side B's READER** — `recognize_select_general` reads the const-arm
///   diamond, and `recognize_admissible_body` still returns `None` for it. The
///   second half is the E6 containment, executed: the gate-free import
///   direction's reach did not move.
/// * **side B's PRODUCER** — the new general route.
/// * **the verdict** — ADMIT, with four refused mutations.
#[test]
fn l3_p2_constant_else_arm_admits_and_e6_stays_blind() {
    let env = island(&["def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0"]);

    // FLIPPED (§6f landing 3): the planner reads the const-arm ite as the
    // exact general select. Everything below was green BEFORE this flip.
    assert_plan_shape(
        &env,
        "clampz",
        CleanOriginShape::SelectOperands {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        },
    );

    let emitted = emitted_general_diamond(
        2,
        64,
        BinOp::Lt,
        0,
        ArithOperand::Param(1),
        ArithOperand::Param(0),
        ArithOperand::Const(0),
    );

    // The READER, both halves.
    assert_eq!(
        recognize_select_general(&emitted),
        Some(GeneralSelectBody {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        }),
        "the const-arm diamond must read back as the exact general select"
    );
    assert_eq!(
        recognize_admissible_body(&emitted),
        None,
        "THE E6 CONTAINMENT: the const-arm diamond must NOT enter \
         `recognize_admissible_body`'s chain, which also feeds \
         `trust_certify::clean_island::admit_function_into` — the kernel-import direction \
         where a recognized body becomes a defining equation with NO side A and NO gate. If \
         this ever returns `Some`, the widening stopped being CALL-only and needs its own \
         review."
    );

    // The PRODUCER, and the verdict.
    let side_b = reflect_general_select(
        &env,
        2,
        64,
        trust_spec_elab::SelectCmp::Lt,
        0,
        SelectOperand::Param(1),
        SelectOperand::Param(0),
        SelectOperand::Literal(0),
    )
    .expect("the general select side B reflects");
    check_faithful(&env, "clampz", &side_b, &u64_carrier())
        .unwrap_or_else(|refusal| panic!("MEASURED ADMIT expected against `clampz`: {refusal:?}"));
    eprintln!(
        "PROBE-ROW | if a < b then a else 0    | side A: REAL | reader: general entry point | \
         producer: NEW general route | kernel: ADMIT"
    );

    // PAIRED MUTATIONS — one construct wrong, each refused.
    let mutants: [(&str, SelectOperand, SelectOperand, trust_spec_elab::SelectCmp); 4] = [
        // The constant off by one: agrees with the declaration on every input
        // whose comparison is TRUE, and differs on every other.
        (
            "wrong arm constant (1 for 0)",
            SelectOperand::Param(0),
            SelectOperand::Literal(1),
            trust_spec_elab::SelectCmp::Lt,
        ),
        // The polarity trap, in the arms the new route made asymmetric.
        (
            "swapped arms",
            SelectOperand::Literal(0),
            SelectOperand::Param(0),
            trust_spec_elab::SelectCmp::Lt,
        ),
        // A PARAMETER arm where the declaration has a constant — the exact
        // confusion the widening opens.
        (
            "a parameter arm for a constant arm",
            SelectOperand::Param(0),
            SelectOperand::Param(1),
            trust_spec_elab::SelectCmp::Lt,
        ),
        // Le for Lt: defeq is intensional on the stuck `ite` (probe_h).
        (
            "Le for Lt",
            SelectOperand::Param(0),
            SelectOperand::Literal(0),
            trust_spec_elab::SelectCmp::Le,
        ),
    ];
    for (what, then_arm, else_arm, cmp) in mutants {
        let wrong = reflect_general_select(
            &env,
            2,
            64,
            cmp,
            0,
            SelectOperand::Param(1),
            then_arm,
            else_arm,
        )
        .expect("the wrong body still reflects");
        refused(&env, "clampz", &wrong, &u64_carrier(), what);
    }
}

/// **The same shape at `<=`, at BOTH arms constant, at a LITERAL comparison,
/// and at arity 1** — four more real elaborations, so the capability is stated
/// over the operand vocabulary rather than over one body.
///
/// The arity-1 case (`nz`) is the one that would catch a de Bruijn inversion
/// that arity 2 hides, and the literal-comparison case (`clamp10z`) is the one
/// that measures the general route composing R2/C9's Nat-reduced decidability
/// instance with a constant arm — two widenings in one tree, which is where a
/// route tuned to a body rather than to a vocabulary would come apart.
#[test]
fn l3_p3_the_constant_arm_holds_across_the_operand_vocabulary() {
    let env = island(&[
        "def lez (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else 0",
        "def bothc (a : UInt64) (b : UInt64) : UInt64 := if a < b then 1 else 0",
        "def clamp10z (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else 0",
        "def nz (a : UInt64) : UInt64 := if a < 1 then 7 else a",
    ]);

    struct Case {
        name: &'static str,
        arity: usize,
        cmp: trust_spec_elab::SelectCmp,
        bin_op: BinOp,
        cmp_right: ArithOperand,
        then_arm: ArithOperand,
        else_arm: ArithOperand,
        /// The one-construct mutation, as (then, else).
        mutant: (SelectOperand, SelectOperand),
        mutation: &'static str,
    }
    let cases = [
        Case {
            name: "lez",
            arity: 2,
            cmp: trust_spec_elab::SelectCmp::Le,
            bin_op: BinOp::Le,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
            mutant: (SelectOperand::Param(0), SelectOperand::Literal(1)),
            mutation: "wrong arm constant at <=",
        },
        Case {
            name: "bothc",
            arity: 2,
            cmp: trust_spec_elab::SelectCmp::Lt,
            bin_op: BinOp::Lt,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Const(1),
            else_arm: ArithOperand::Const(0),
            mutant: (SelectOperand::Literal(0), SelectOperand::Literal(1)),
            mutation: "both constants swapped",
        },
        Case {
            name: "clamp10z",
            arity: 2,
            cmp: trust_spec_elab::SelectCmp::Lt,
            bin_op: BinOp::Lt,
            cmp_right: ArithOperand::Const(10),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
            mutant: (SelectOperand::Param(0), SelectOperand::Literal(1)),
            mutation: "wrong arm constant under a literal comparison",
        },
        Case {
            name: "nz",
            arity: 1,
            cmp: trust_spec_elab::SelectCmp::Lt,
            bin_op: BinOp::Lt,
            cmp_right: ArithOperand::Const(1),
            then_arm: ArithOperand::Const(7),
            else_arm: ArithOperand::Param(0),
            mutant: (SelectOperand::Param(0), SelectOperand::Literal(7)),
            mutation: "swapped arms at arity 1",
        },
    ];

    for case in cases {
        // FLIPPED (§6f landing 3), one per case.
        assert_plan_shape(
            &env,
            case.name,
            CleanOriginShape::SelectOperands {
                cmp: match case.cmp {
                    trust_spec_elab::SelectCmp::Lt => SelectCmp::Lt,
                    trust_spec_elab::SelectCmp::Le => SelectCmp::Le,
                    trust_spec_elab::SelectCmp::Eq => SelectCmp::Eq,
                },
                cmp_left: 0,
                cmp_right: case.cmp_right,
                then_arm: case.then_arm,
                else_arm: case.else_arm,
            },
        );

        let emitted = emitted_general_diamond(
            case.arity,
            64,
            case.bin_op,
            0,
            case.cmp_right,
            case.then_arm,
            case.else_arm,
        );
        assert!(
            recognize_select_general(&emitted).is_some(),
            "`{}`: the emitted diamond must read back",
            case.name
        );
        assert_eq!(
            recognize_admissible_body(&emitted),
            None,
            "`{}`: the E6 chain must stay blind to a const-arm diamond",
            case.name
        );

        let operand_of = |o: ArithOperand| match o {
            ArithOperand::Param(index) => SelectOperand::Param(index),
            ArithOperand::Const(value) => SelectOperand::Literal(value),
        };
        let side_b = reflect_general_select(
            &env,
            case.arity,
            64,
            case.cmp,
            0,
            operand_of(case.cmp_right),
            operand_of(case.then_arm),
            operand_of(case.else_arm),
        )
        .expect("the general select side B reflects");
        check_faithful(&env, case.name, &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
            panic!("MEASURED ADMIT expected against `{}`: {refusal:?}", case.name)
        });

        let wrong = reflect_general_select(
            &env,
            case.arity,
            64,
            case.cmp,
            0,
            operand_of(case.cmp_right),
            case.mutant.0,
            case.mutant.1,
        )
        .expect("the wrong body still reflects");
        refused(&env, case.name, &wrong, &u64_carrier(), case.mutation);
        eprintln!(
            "PROBE-ROW | {:<24} | side A: REAL | kernel: ADMIT; `{}` REFUSED",
            case.name, case.mutation
        );
    }
}

/// **A measured side effect, recorded because it is a COST as well as a
/// finding: one member of the new family used to be discovered by a PROOF.**
///
/// `if a < 1 then 0 else a` is extensionally the identity on `UInt64` — the
/// comparison holds exactly at `a = 0`, where the then arm returns `0`. Before
/// this landing `recognise_clean_shape` refused it and the
/// `recognise_inductive_projection` FALLBACK proved it equal to its parameter
/// by closed structural induction, so it planned as
/// `InductiveProjection { projected: 0 }` and emitted a one-instruction copy
/// (measured on this exact source, 2026-08-22, before the planner learned the
/// general select).
///
/// After the landing the direct lane recognizes it first, so it plans as the
/// select and emits the four-block diamond. Both verdicts are gate-checked and
/// both are faithful; what changed is WHICH row, and the emitted code is worse.
///
/// This is not a regression the landing introduced so much as one it inherited:
/// the fallback ORDER is pre-existing (`recognise_clean_shape` first, the
/// induction proof only on its `Err`), and `if a < b then a else a` already
/// took the diamond for exactly the same reason. It is recorded rather than
/// smoothed over, because *"the ladder is an OPTIMIZATION ladder"* cuts both
/// ways: widening the direct lane can take work AWAY from a cleverer route, and
/// the place to fix that is a cost model, not a recognizer order chosen by
/// accident.
#[test]
fn l3_p3b_a_select_that_is_extensionally_a_projection_now_takes_the_direct_route() {
    let env = island(&["def nzid (a : UInt64) : UInt64 := if a < 1 then 0 else a"]);
    assert_plan_shape(
        &env,
        "nzid",
        CleanOriginShape::SelectOperands {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: ArithOperand::Const(1),
            then_arm: ArithOperand::Const(0),
            else_arm: ArithOperand::Param(0),
        },
    );
    // And it is still FAITHFUL through the new route — the point is that the
    // verdict did not change, only the row that produced it.
    let side_b = reflect_general_select(
        &env,
        1,
        64,
        trust_spec_elab::SelectCmp::Lt,
        0,
        SelectOperand::Literal(1),
        SelectOperand::Literal(0),
        SelectOperand::Param(0),
    )
    .expect("the general select side B reflects");
    check_faithful(&env, "nzid", &side_b, &u64_carrier())
        .expect("MEASURED ADMIT: the direct route reaches the same verdict the proof did");
    eprintln!(
        "PROBE-ROW | if a < 1 then 0 else a    | was: InductiveProjection (PROVED) | now: \
         SelectOperands (recognized) | same verdict, a bigger body"
    );
}

// ═════ L3-P4 — the general route REPRODUCES both frozen routes, exactly ═════

/// **The standing anti-drift control for extending a frozen-adjacent
/// producer.**
///
/// `trust-spec-elab`'s existing select routes are UNTOUCHED by this landing —
/// the R2/C9 discipline: a new route is added BESIDE them, never a widened
/// signature on a frozen one. That leaves the hazard the tree names everywhere
/// else: *two builders of one term can only drift.* This control closes it
/// without merging them — the general route must mint the **byte-identical
/// kernel term** the frozen route mints, everywhere their domains overlap.
///
/// It is measured over the whole overlap this crate can reach: three
/// comparisons × four machine widths × three index assignments, for the
/// parameter route, and the same for the literal route at the three thresholds
/// R2/C9's Nat-reduced instance is stated at. If the general route is ever
/// tuned — for a body, for a spelling, for anything — this fails.
#[test]
fn l3_p4_the_general_route_reproduces_the_frozen_routes_exactly() {
    let env = island(&["def anchor (a : UInt64) : UInt64 := a"]);
    let cmps = [
        trust_spec_elab::SelectCmp::Lt,
        trust_spec_elab::SelectCmp::Le,
        trust_spec_elab::SelectCmp::Eq,
    ];
    let mut compared = 0usize;

    for bits in [8u32, 16, 32, 64] {
        let domains = vec![machine(bits), machine(bits)];
        for cmp in cmps {
            for (cl, cr, t, e) in [(0usize, 1usize, 0usize, 1usize), (1, 0, 1, 0), (0, 0, 1, 1)] {
                let frozen = reflect(&env, |scratch, name| {
                    trust_spec_elab::admit_select_function(
                        scratch, name, &domains, cmp, cl, cr, t, e,
                    )
                })
                .expect("the frozen parameter route mints");
                let general = reflect(&env, |scratch, name| {
                    trust_spec_elab::admit_select_operands_function(
                        scratch,
                        name,
                        &domains,
                        cmp,
                        cl,
                        SelectOperand::Param(cr),
                        SelectOperand::Param(t),
                        SelectOperand::Param(e),
                    )
                })
                .expect("the general route mints");
                assert_eq!(
                    frozen, general,
                    "at u{bits}, {cmp:?}, ({cl},{cr},{t},{e}) the general route does not \
                     reproduce `admit_select_function`'s term. The general route is a \
                     GENERALIZATION, not a second builder: a divergence here means one of the \
                     two is now minting a term the other does not, and the shapes that route \
                     through them would be checked against different claims."
                );
                compared += 1;
            }
            for literal in [0u128, 1, 10] {
                let frozen = reflect(&env, |scratch, name| {
                    trust_spec_elab::admit_select_literal_function(
                        scratch, name, &domains, cmp, 0, literal, 0, 1,
                    )
                })
                .expect("the frozen literal route mints");
                let general = reflect(&env, |scratch, name| {
                    trust_spec_elab::admit_select_operands_function(
                        scratch,
                        name,
                        &domains,
                        cmp,
                        0,
                        SelectOperand::Literal(literal),
                        SelectOperand::Param(0),
                        SelectOperand::Param(1),
                    )
                })
                .expect("the general route mints");
                assert_eq!(
                    frozen, general,
                    "at u{bits}, {cmp:?}, literal {literal} the general route does not \
                     reproduce `admit_select_literal_function`'s term — including R2/C9's \
                     Nat-reduced decidability instance, which is the piece a re-derivation \
                     would be most likely to get wrong"
                );
                compared += 1;
            }
        }
    }
    assert_eq!(compared, 4 * 3 * (3 + 3), "the overlap must actually have been walked");
    eprintln!(
        "PROBE-ROW | general vs frozen routes  | {compared} terms compared | IDENTICAL at \
         every comparison, width and index assignment"
    );
}

// ═══ L3-P5 — ranked MISS 3: a COMPUTED `ite` condition. MEASURED, REFUSED ═══

/// **Candidate 3, measured at the real elaborator — and the recorded reason is
/// REPLACED.**
///
/// Landing 2 recorded this as *"the producer's operands are `cmp_left: usize` /
/// `cmp_right: usize` — unrepresentable, so this needs a NEW trust-spec-elab
/// route"*. Measured here against the elaborator that will really run, that is
/// the SMALLER half of the problem. `if a + 1 < b` does elaborate, and its
/// PROPOSITION is a clean `LT.lt UInt64 instLTUInt64 (HAdd.hAdd … a 1) b` — an
/// operand vocabulary a route could carry. But its DECIDABILITY INSTANCE is
/// not `instDecidableNatLt` over a projection chain: it is `instDecidableNatLt`
/// over a **`Nat.rec`-headed normal form** — the elaborator's unfolding of the
/// modular reduction `(a.toNat + 1) % 2^64` at a neutral argument.
///
/// Kernel defeq is INTENSIONAL on the stuck `ite` (the C5.0 finding), so side B
/// would have to reproduce that normal form term-for-term. That is not an
/// operand-vocabulary question and it is not a new admit route: it is
/// re-implementing an elaborator's instance-synthesis output inside a producer,
/// which would be the most brittle trusted surface in this lane. REFUSED, and
/// the ledger entry now says so.
#[test]
fn l3_p5_computed_ite_condition_needs_an_elaborator_normal_form() {
    let env =
        island(&["def shifted (a : UInt64) (b : UInt64) : UInt64 := if a + 1 < b then a else b"]);
    assert_plan_refuses_today(&env, "shifted");

    // The instance argument, read out of the real tree.
    let body = env
        .get_const(&Name::from_string("shifted"))
        .and_then(|c| c.value.clone())
        .expect("the island registered `shifted`");
    let mut cursor = &body;
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = &**inner;
    }
    let (head, args) = uncurry(cursor);
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "ite"),
        "the body is still an `ite`"
    );
    assert_eq!(args.len(), 5);
    let (inst_head, inst_args) = uncurry(args[2]);
    assert!(
        matches!(inst_head.kind(), ExprKind::Const(n, _) if n.to_string() == "instDecidableNatLt"),
        "the decidability still resolves by reduction to Nat: {inst_head:?}"
    );
    // THE FINDING: the instance's first argument is not a projection chain
    // over a parameter (what R2/C9's literal comparison mints) but a
    // `Nat.rec` application — the elaborator's normalized modular reduction.
    let (arg_head, _) = uncurry(inst_args[0]);
    assert!(
        matches!(arg_head.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.rec"),
        "MEASURED: a computed comparison operand's decidability instance is a `Nat.rec`-headed \
         normal form, not a projection chain. If this ever becomes a projection chain, the \
         blocker has moved back to the producer's operand vocabulary and the MISS entry must \
         be re-measured: {arg_head:?}"
    );
    eprintln!(
        "PROBE-ROW | if a + 1 < b then a else b| side A: REAL, and its Decidable instance is \
         a `Nat.rec` NORMAL FORM | MISS (side B would have to reproduce an elaborator normal \
         form)"
    );
}

// ═══ L3-P6 — ranked MISS 4: a numeral on the LEFT. RATCHET FIRED ═══

/// **THE RATCHET FIRED, AND THIS IS THE FLIP — collateral of the clean pin
/// `bad1fd5f8`, not of any landing that asked for it.**
///
/// The reason on this entry has now been replaced TWICE, which is the point of
/// keeping the history in the probe rather than only in the ledger:
///
/// 1. landing 2 recorded *"unrepresentable in the frozen producer's signature
///    (`admit_select_literal_function` cannot spell it), so the row would need
///    a new producer, not a new arm"*;
/// 2. landing 3 replaced that: it HAD a new producer and the shape still did
///    not reach one, because `if 10 < a then a else b` **did not elaborate** —
///    the bare numeral typed as `Nat`, the comparison was heterogeneous, and
///    the island rejected it with a type mismatch. So the blocker was
///    `first-party/clean`'s elaborator, upstream of everything this lane owns.
/// 3. **2026-08-23: it elaborates.** Measured at clean pin `bad1fd5f8`, the
///    same source registers cleanly, and the numeral elaborates AT THE CARRIER
///    — `UInt64.ofNat 10` on the comparison's left, inside the same
///    `LT.lt … instLTUInt64` proposition the served `select.lt` row already
///    reads on the right.
///
/// This probe was RED on `main` before §6f landing 7 touched anything, and it
/// is flipped here because a landing that moves a pin's consumers must move all
/// of them (`CLAUDE.md`: *"a pin move and its consumer updates belong in the
/// SAME commit"*) — but the demand is **NOT SERVED**, and this landing does not
/// serve it. What it now costs is a genuine one-operand widening in THREE
/// places rather than an elaborator commit: `CleanOriginShape::SelectOperands`
/// and its two siblings carry `cmp_left: usize`, `GeneralSelectBody` carries
/// `cmp_left: usize`, and `admit_select_operands_function` takes
/// `cmp_left: usize`. Widening all three to an operand is a landing with its
/// own mutation controls (a numeral on the WRONG side of a `<` is the
/// complementary function), not a line in this one.
///
/// The MISS entry's reason moves with it, in `table.rs`.
///
/// # 2026-08-27 — this probe was RED, and the elaborator had not moved at all
///
/// The row asserted its measurement through `format!("{value}")` and looked for
/// the substring `instLTUInt64`. At clean pin `79926e80a` the same body renders
///
/// ```text
/// ite UInt64 (UInt64.ofNat 10 < u) (instDecidableNatLt 10 Fin.0.BitVec.0.UInt64.0.u) u u1
/// ```
///
/// with no `instLTUInt64` anywhere in it — and the flip is a **rendering gain,
/// not a regression**. Clean `6d1663115` (*"`Display for Expr` speaks Lean
/// notation, not spine juxtaposition"*) added a notation table keyed on head
/// constant and exact arity; `LT.lt` at four arguments now prints infix and
/// drops the leading implicit type and instance telescope, which is exactly
/// what Lean hides. Measured structurally, the term is UNCHANGED and is
/// letter-for-letter the one this doc-comment already described:
///
/// ```text
/// arg[1] head = LT.lt   [ UInt64, instLTUInt64, UInt64.ofNat 10, bvar ]
/// ```
///
/// The `Display` output is a HUMAN CHANNEL and carries no authority; the term
/// is the object the kernel and the gate read. So the assertion is re-pinned
/// onto the term, and it is re-pinned as a **CONTRAST against the served
/// direction** rather than as a bare shape: `if a < 10` is elaborated in the
/// same run and asserted to be the identical `LT.lt` spine with the two
/// operands exchanged. That is the row's actual adversarial claim — the MISS
/// is a ONE-OPERAND widening and nothing else, so a future change that made
/// the left-numeral form heterogeneous (a `Nat` comparison under a coercion,
/// which is what it used to be) would fail here even though the demand is
/// still unserved either way.
///
/// **The hazard this row now also guards.** A probe that reads an
/// authority-bearing fact through `Display` measures the pretty-printer. Assert
/// on the spine; if a message string is genuinely the subject, say so and pin
/// constants that have no notation entry (see `landing5_selection_probes`
/// `l5_p3`, which was red on the same pin move for the same reason).
#[test]
fn l3_p6_a_numeral_on_the_left_now_elaborates_and_still_does_not_plan() {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session
        .check_all(&["def flip10 (a : UInt64) (b : UInt64) : UInt64 := if 10 < a then a else b"]);
    assert!(
        !batch.is_rejected(),
        "MEASURED 2026-08-23 at clean pin `bad1fd5f8`: a numeral on the comparison's LEFT \
         now elaborates. If it has stopped again, the blocker has moved BACK into \
         `first-party/clean` and this entry's reason must be re-measured — do not simply \
         restore the old assertion, because the two reasons rank the work completely \
         differently: {batch:?}"
    );
    let env = session.environment().expect("an untainted session has an environment").clone();

    // The numeral elaborates AT THE CARRIER, which is what makes this a
    // producer-vocabulary question now rather than a typing one.
    //
    // Read off the TERM, never off `format!("{value}")`: since clean
    // `6d1663115` the printer speaks Lean notation, so `@LT.lt UInt64
    // instLTUInt64 x y` renders `x < y` and the instance is invisible in the
    // text while being present in the tree. The tree is what the gate reads.
    let flipped = comparison_spine(&env, "flip10");
    assert_eq!(
        flipped.len(),
        4,
        "`LT.lt` is `{{C}} inst lhs rhs`; a different arity is a different proposition"
    );
    assert_eq!(
        const_name(&flipped[0]).as_deref(),
        Some("UInt64"),
        "the comparison must be HOMOGENEOUS AT THE CARRIER — a `Nat` type argument here is \
         the pre-`bad1fd5f8` heterogeneous reading coming back, and the entry's reason would \
         have to be replaced a fourth time"
    );
    assert_eq!(
        const_name(&flipped[1]).as_deref(),
        Some("instLTUInt64"),
        "the carrier's own `LT` instance, not a `Nat` one reached through a coercion"
    );
    assert_eq!(
        const_name(head_of(&flipped[2])).as_deref(),
        Some("UInt64.ofNat"),
        "the LEFT operand must be a CARRIER numeral — that is the whole subject of this entry"
    );
    assert!(
        matches!(flipped[3].kind(), ExprKind::BVar(_)),
        "the RIGHT operand must be the parameter"
    );

    // THE CONTRAST, and the reason this row is a one-operand widening rather
    // than a typing question: the SERVED direction is the same spine with the
    // two operands exchanged, elaborated in the same way at the same pin.
    let served =
        island(&["def right10 (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b"]);
    let right = comparison_spine(&served, "right10");
    assert_eq!(
        (const_name(&right[0]), const_name(&right[1])),
        (const_name(&flipped[0]), const_name(&flipped[1])),
        "the served direction must carry the SAME carrier and the SAME `LT` instance; if it \
         does not, the two shapes differ by more than an operand and the ledger's \
         one-operand-widening reason is wrong"
    );
    assert!(
        matches!(right[2].kind(), ExprKind::BVar(_)),
        "`if a < 10` must put the parameter on the LEFT"
    );
    assert_eq!(
        const_name(head_of(&right[3])).as_deref(),
        Some("UInt64.ofNat"),
        "`if a < 10` must put the carrier numeral on the RIGHT — the exact mirror of \
         `flip10`, which is what makes the MISS one operand wide"
    );

    // AND IT STILL DOES NOT PLAN. The demand stays a MISS, and this is the
    // half that keeps the flip from being read as a capability claim.
    let refusal = trust_clean_origin::plan_clean_origin_body(&env, "flip10")
        .err()
        .expect("`flip10` must NOT plan — no select shape carries an operand on the LEFT");
    let note = refusal.note();
    assert!(
        note.contains("strictly on the comparison's RIGHT"),
        "the refusal must still name the RIGHT-operand boundary: {note}"
    );

    eprintln!(
        "PROBE-ROW | if 10 < a then a else b   | side A: NOW ELABORATES (carrier numeral on \
         the left) | plan: still refused | MISS (a one-operand widening in three signatures)"
    );
}

// ═══ L3-P7 — the NEW measured absence: `==` as an `ite` condition ═══

/// **A newly measured absence, entering the denominator.**
///
/// The `select.eq` row is stated over `Eq.{1} {C} l r` with
/// `instDecidableEq{C}` — and that IS what the real elaborator mints, for the
/// PROPOSITIONAL equality `a = b`. What it mints for `a == b` is a different
/// tree entirely: `Eq.{1} Bool (BEq.beq {C} (instBEqOfDecidableEq {C}
/// instDecidableEq{C}) a b) Bool.true`, the Bool-level decision lifted back to
/// a proposition. `recognise_select_ite` matches the proposition exactly, so
/// the `==` spelling falls to the fragment refusal.
///
/// This is recorded rather than fixed. It is a real MISS — a user writing the
/// more idiomatic `==` gets a refusal where `=` succeeds — and it is not this
/// landing's candidate: admitting it means matching a second proposition shape
/// whose `Bool.true` scrutinee has to be measured at the kernel in its own
/// right, with its own producer arm and its own mutation controls.
///
/// # SUPERSEDED IN PART by §6f landing 6, and only in its DISPOSITION
///
/// Everything this probe MEASURES is unchanged and is still asserted below: the
/// `=` spelling plans as `Select`, and `a == b` elaborates to a `BEq.beq`
/// decision lifted to a proposition rather than to `Eq {C} a b`. What changed
/// is what the compiler DOES about it. Landing 5 landed the producer and
/// measured the blocker; landing 6 gave the shape its own MIR realization (the
/// two-step diamond) and its own `select.beq` row, so `a == b` now PLANS as
/// `CleanOriginShape::SelectBeq` instead of refusing. The one line that asserted
/// the refusal is therefore replaced by one asserting the shape — deliberately
/// NOT deleted, so this file still records that the two spellings are two
/// trees, which is the fact both landings rest on. End-to-end evidence for the
/// new disposition: `landing6_selection_probes::l6_p2`.
#[test]
fn l3_p7_beq_equality_is_a_second_spelling_the_select_rows_do_not_read() {
    let env = island(&[
        "def eqsingle (a : UInt64) (b : UInt64) : UInt64 := if a = b then a else b",
        "def eqbeq (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
    ]);

    // `=` is the spelling `select.eq` was stated over, and it plans.
    assert_plan_shape(
        &env,
        "eqsingle",
        CleanOriginShape::Select {
            cmp: SelectCmp::Eq,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        },
    );

    // `==` is a DIFFERENT tree — and since §6f landing 6 it has a DIFFERENT
    // SHAPE, a different row and a different emitted realization, rather than a
    // refusal. (Landing 3 asserted `assert_plan_refuses_today` here; landing 6
    // is what changed the verdict, and the tree measurement below is untouched.)
    assert_plan_shape(
        &env,
        "eqbeq",
        CleanOriginShape::SelectBeq {
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Param(1),
        },
    );
    let body = env
        .get_const(&Name::from_string("eqbeq"))
        .and_then(|c| c.value.clone())
        .expect("the island registered `eqbeq`");
    let mut cursor = &body;
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = &**inner;
    }
    let (_, args) = uncurry(cursor);
    let (prop_head, prop_args) = uncurry(args[1]);
    assert!(
        matches!(prop_head.kind(), ExprKind::Const(n, _) if n.to_string() == "Eq"),
        "the `==` proposition is still an `Eq`"
    );
    let (beq_head, _) = uncurry(prop_args[1]);
    assert!(
        matches!(beq_head.kind(), ExprKind::Const(n, _) if n.to_string() == "BEq.beq"),
        "MEASURED: `a == b` elaborates to a BOOL-level `BEq.beq` lifted to a proposition, not \
         to `Eq {{C}} a b`. That is why the `select.eq` row does not read it: {beq_head:?}"
    );
    eprintln!(
        "PROBE-ROW | if a == b then a else b   | side A: REAL = `Eq Bool (BEq.beq …) true` | \
         SERVED since §6f landing 6 (was: MISS — a second proposition spelling, unmeasured at \
         the kernel)"
    );
}
