// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 15 — THE RAW-BINOP EMITTER MUTATION FIXTURE, at `%`.**
//!
//! Every other [`CleanOriginShape`] variant has a per-shape emitter-mutation
//! control — `control_3`/`control_5` (`Projection`, `WrappingBinOp`),
//! `control_6` (`Composed`, `Select`), `control_7` (`SelectLiteral`,
//! `StructuralNatRec`), `control_8`/`control_11` (`WellFoundedNatRec`),
//! `control_9` (`ConstantUint`), `control_10` (`SelectOperands`), `control_13`
//! (`SelectBeq`). [`CleanOriginShape::RawBinOp`] shipped in §6f landing 7
//! WITHOUT one: `landing7_selection_probes` measures the shape thoroughly, but
//! a landing probe records what a capability DOES, and a control records what
//! a mistranslating emitter CANNOT get past. This file is the missing control,
//! pointed at the `%` member of the family.
//!
//! `%` rather than `&&&` on purpose. It is the one operator in the family whose
//! Clean denotation and Rust realization **disagree on a reachable input**:
//! `UInt{N}.mod` is TOTAL and Rust's `%` PANICS at a zero divisor. The
//! shape therefore carries a soundness rule no other shape has — the divisor
//! must be a strictly positive numeral — and a control for `%` is a control for
//! that rule.
//!
//! The route is control_5's, with the family's own reader in the first step:
//!
//! ```text
//! emitted body (as read back out of MIR by trust_mir_extract)
//!   -> trust_types::recognize_raw_binop                  (NOT the E6 chain)
//!   -> trust_spec_elab::admit_expr_function              (side B, "p0 % 7")
//!   -> check_faithful                                    (against side A)
//! ```
//!
//! and the mutation is injected into **the emitted body**, never into side B.
//!
//! # WHAT THIS CONTROL ADDS THAT `l7_p4` DOES NOT
//!
//! `l7_p4` mutates the REAL emissions and is the better probe for that reason.
//! It runs its divisor mutations on `/` (`dv`) and its operator mutations on
//! the bitwise pair, so for `%` specifically the swapped-operand, wrong-divisor
//! and panicking-divisor mutants are **not** measured. It also has no
//! whole-body width mutant at all: its row 8 skews the LITERAL's encoded width,
//! which side B's operand reader catches structurally. `half_7` below is the
//! case no probe in this crate covers — a body that is *internally consistent*
//! at the wrong width, where every structural check agrees and only the kernel
//! can see the truncation. That is `control_5::half_8`'s discipline, which
//! landing 7 never received.
//!
//! # DOUBLE-FAULT STRUCTURE
//!
//! A swap or a wrong constant in the emitter ALONE is caught by the structural
//! plan-vs-recognizer check; a misreading of side A ALONE is caught by the
//! kernel. Each mutation half below asserts BOTH layers where both can see it,
//! and names which layer fires when only one can — `half_7` records that the
//! kernel is load-bearing there and nothing above it is.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` and `trust_spec_elab::admit_*_function` are
//! frozen against this lane. If a mutated body ever passes, the defect is in
//! the emitter or the gate — never in this fixture.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, admit_lowering, check_faithful,
    plan_clean_origin_body,
};
use trust_types::admissible_body::{ArithOperand, RawBinOpKind};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
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

/// `UInt64.ofNat n` — the carrier numeral.
fn carrier_lit(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("UInt64.ofNat"), vec![]), Expr::nat_lit(n))
}

/// `H<Class>.h<proj> UInt64 UInt64 UInt64 <inst> lhs rhs` — the SURFACE
/// spelling, the one a real island produces (`l7_p1`). The instance is a
/// parameter so `half_9` can route through a non-prelude one.
fn surface_via(class: &str, proj: &str, inst: &str, lhs: Expr, rhs: Expr) -> Expr {
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    Expr::apps(
        Expr::const_(Name::from_string(&format!("{class}.{proj}")), zero3),
        [uint64(), uint64(), uint64(), Expr::const_(Name::from_string(inst), vec![]), lhs, rhs],
    )
}

/// `UInt64.mod lhs rhs` — the CARRIER spelling. Stated only so `half_0b` can
/// pin that it is deliberately NOT planned; no source produces it.
fn carrier_mod(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("UInt64.mod"), vec![]), [lhs, rhs])
}

/// `def rem7 (a : UInt64) : UInt64 := a % 7`, in the surface spelling.
fn env_with_rem7() -> Environment {
    let mut env = env_uint();
    define(
        &mut env,
        "rem7",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            surface_via("HMod", "hMod", "instHModUInt64", Expr::bvar(0), carrier_lit(7)),
        ),
    );
    env
}

// ─────────────── the emitter's MIR, as extracted, and mutants ───────────────

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
    }
}

/// The emitter's realization for this family: ONE block, ONE statement, a bare
/// `Rvalue::BinaryOp`, `Return`. No call, no branch, no `Assert` — the absence
/// of the panic guard is exactly what the divisor rule pays for.
fn emitted_raw_at(
    name: &str,
    op: BinOp,
    left: Operand,
    right: Operand,
    arg_count: usize,
    ty: Ty,
) -> VerifiableFunction {
    vf(
        name,
        arg_count,
        locals(arg_count + 1, ty),
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(op, left, right),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

fn emitted_raw(
    name: &str,
    op: BinOp,
    left: Operand,
    right: Operand,
    arg_count: usize,
) -> VerifiableFunction {
    emitted_raw_at(name, op, left, right, arg_count, Ty::u64())
}

fn copy_arg(i: usize) -> Operand {
    Operand::Copy(Place::local(i))
}

fn u64_const(v: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(v, 64))
}

/// Reflect a spec-syntax body through the FROZEN expr mint — the kernel half of
/// a mutation, bypassing the structural check on purpose so the KERNEL's own
/// verdict is measured (control_3 half_3's rationale, control_5's spelling).
fn reflect_expr(env: &Environment, body: &str, n_params: usize) -> Expr {
    reflect_expr_try(env, body, n_params)
        .unwrap_or_else(|e| panic!("`{body}` must reflect: {e}"))
}

/// The same, handing back the FROZEN producer's own refusal — used where the
/// point of the half is that side B does not exist at all.
fn reflect_expr_try(env: &Environment, body: &str, n_params: usize) -> Result<Expr, String> {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut scratch = env.clone();
    let name = "control15_reflection";
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        name,
        body,
        &name_refs,
        &trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
    )?;
    Ok(scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .expect("a minted definition carries a value"))
}

fn u64_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_at(&uint64(), &Ty::u64())
        .expect("UInt64 -> u64 is the exact-width carrier")
}

/// The REAL island elaborator, for the two halves whose subject is a term the
/// PRELUDE defines (`UInt64.mod` unfolding to `Nat.mod`). `env_uint()` is a
/// hand-built environment and would measure a stub rather than the kernel's
/// own reduction — the `probe_i3` rationale in this crate's `[dev-dependencies]`
/// note, applied here.
fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn definition_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("`{name}` must be a definition with a value"))
}

fn rem7_shape() -> CleanOriginShape {
    CleanOriginShape::RawBinOp {
        op: RawBinOpKind::Rem,
        left: ArithOperand::Param(0),
        right: ArithOperand::Const(7),
    }
}

// ═══════════════════════════════ the halves ═══════════════════════════════

#[test]
fn half_0_the_plan_reads_the_surface_spelling_as_a_rem_shape() {
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("`a % 7` plans");
    assert_eq!(plan.shape(), &rem7_shape(), "`rem7` must read as `a % 7`");
    assert_eq!(plan.signature().arity(), 1);
    assert_eq!(plan.return_ty(), &Ty::u64());
}

#[test]
fn half_0b_the_CARRIER_spelling_is_deliberately_NOT_a_second_reader_arm() {
    // The counterpart to `control_5::half_0`, and it asserts the OPPOSITE
    // thing, on purpose. The wrapping family reads two spellings because a real
    // island produces both. This family reads ONE — the homogeneous surface
    // class at the prelude instance — and that is a MEASUREMENT (`l7_p1`): no
    // source emits `UInt64.mod`, and side B renders the `toNat`/`ofNat` round
    // trip rather than the carrier method either.
    //
    // So a `CarrierMethod` reader arm here would be an arm for a spelling
    // NEITHER side produces — `control_14`'s spelling-grain defect class. This
    // half pins the refusal so that adding such an arm is a deliberate act with
    // a failing test in front of it, rather than a plausible-looking widening.
    //
    // The declaration is well-typed and kernel-checked; it is refused for being
    // outside the measured fragment, which is a capability boundary and must
    // therefore be user-actionable rather than an internal error.
    let mut env = env_uint();
    define(
        &mut env,
        "rem7_carrier",
        u64_arrows(1),
        Expr::lam(BinderInfo::Default, uint64(), carrier_mod(Expr::bvar(0), carrier_lit(7))),
    );
    let refusal = plan_clean_origin_body(&env, "rem7_carrier")
        .expect_err("the carrier spelling is outside the measured single-spelling fragment");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(
        !refusal.is_compiler_defect(),
        "a spelling boundary is user-actionable, never an internal error"
    );
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
}

#[test]
fn half_1_the_gate_admits_the_faithful_emission() {
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("plannable");

    let emitted = emitted_raw("rem7", BinOp::Rem, copy_arg(1), u64_const(7), 1);
    // The realization contract, asserted rather than assumed: no `Assert`
    // terminator, no call, one block. A future emitter that "helpfully" added a
    // divide-by-zero guard would be emitting a body side B does not read, and
    // it must surface here.
    assert_eq!(emitted.body.blocks.len(), 1, "one block");
    assert!(matches!(emitted.body.blocks[0].terminator, Terminator::Return));

    let admitted = admit_lowering(&env, &plan, &emitted)
        .expect("`Rem(_1, const 7)` IS `a % 7`; the gate must admit it");
    assert_eq!(admitted.name(), "rem7");
    assert_eq!(
        admitted.admitted_at(),
        &Ty::u64(),
        "admitted AT THE CARRIER TYPE, never the Clean type"
    );
}

#[test]
fn half_2_a_WRONG_DIVISOR_is_refused_by_both_layers() {
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("plannable");

    // Structural half: the emitter baked in 8 where the def says 7.
    let refusal =
        admit_lowering(&env, &plan, &emitted_raw("rem7", BinOp::Rem, copy_arg(1), u64_const(8), 1))
            .expect_err(
                "THE GATE IS DECORATION IF THIS PASSES: a body computing `a % 8` was accepted \
                 for a definition that says `a % 7`. Do NOT fix this by editing side B's \
                 producers; they are frozen against this lane.",
            );
    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect: {refusal:?}");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Kernel half: `p0 % 8` against `a % 7`, with the structural check skipped.
    let refusal = check_faithful(&env, "rem7", &reflect_expr(&env, "p0 % 8", 1), &u64_carrier())
        .expect_err("the kernel must separate `a % 7` from `a % 8`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_3_SWAPPED_OPERANDS_are_refused_STRUCTURALLY_and_have_no_side_B() {
    // `%` is not commutative, and `l7_p4` swaps only `/`. `7 % a` and `a % 7`
    // agree at a = 7 and nowhere else interesting, so a swap here is a wrong
    // binary that a smoke test could easily miss.
    //
    // MEASURED, and it is NOT the shape the other halves have. Every sibling
    // mutation is caught twice — structurally, and again by the kernel on the
    // reflected mutant. This one cannot be, and the reason is this shape's own
    // divisor rule: swapping `a % 7` puts the PARAMETER in divisor position, so
    // the mutant rendering `7 % p0` is a variable divisor and the FROZEN
    // producer refuses to mint it at all.
    //
    // That is strictly stronger than a kernel disagreement, not weaker: a
    // disagreement means the kernel compared two terms and separated them,
    // whereas this means the mutant has NO side B to be compared against, so it
    // cannot reach the kernel by any route. The half asserts the refusal that
    // actually happens rather than manufacturing a comparison — a hand-built
    // side-B term would bypass the frozen producer, which is the one layer in
    // this file that was not written for this lane.
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("plannable");

    // Layer 1 — the structural check, against the sealed plan.
    let refusal =
        admit_lowering(&env, &plan, &emitted_raw("rem7", BinOp::Rem, u64_const(7), copy_arg(1), 1))
            .expect_err("`7 % a` emitted for a def that says `a % 7` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // Layer 2 — the FROZEN producer, which is not this lane.
    let producer = reflect_expr_try(&env, "7 % p0", 1)
        .err()
        .expect("the FROZEN producer must refuse `7 % p0`: swapping puts a variable in divisor \
                 position, and a variable divisor has no side B");
    assert!(
        producer.contains("divisor"),
        "the producer's refusal must name the divisor boundary rather than a parse failure, \
         otherwise this half measured a syntax error instead of the swap: {producer}"
    );

    // THE CONTROL, so layer 2 is not passing for the wrong reason: the
    // UNSWAPPED rendering mints, so the producer is refusing the swap's
    // consequence and not `%` or the numeral spelling.
    assert!(
        reflect_expr_try(&env, "p0 % 7", 1).is_ok(),
        "`p0 % 7` must mint — otherwise layer 2 measured a ban on `%` itself"
    );
}

#[test]
fn half_4_the_SIBLING_OPERATOR_is_refused_by_both_layers() {
    // `/` for `%`. `l7_p4` has the structural half of this; the kernel half is
    // the one that matters, because `Nat.div` and `Nat.mod` are different
    // recursions and a reader that conflated them would be invisible upstream.
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("plannable");

    let refusal =
        admit_lowering(&env, &plan, &emitted_raw("rem7", BinOp::Div, copy_arg(1), u64_const(7), 1))
            .expect_err("`a / 7` emitted for a def that says `a % 7` must refuse");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    let refusal = check_faithful(&env, "rem7", &reflect_expr(&env, "p0 / 7", 1), &u64_carrier())
        .expect_err("the kernel must separate `a % 7` from `a / 7`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_5_a_SYMBOLIC_DIVISOR_is_refused_at_three_independent_layers() {
    // THE SOUNDNESS RULE OF THIS SHAPE. A variable divisor is the case where
    // Clean's totality and Rust's panic actually diverge on a reachable input,
    // and it must not be emittable. The three layers are asserted separately
    // because two of them are this lane agreeing with itself.
    //
    // READ LAYER 2 PRECISELY — `half_11` is the other half of this claim.
    // Layer 2 below is the STRUCTURAL check of an emitted body against a plan
    // that already fixed a LITERAL divisor; it is not the faithfulness gate
    // deciding a symbolic-divisor claim. Put THAT claim to the gate directly
    // and the gate ADMITS, because both Clean terms are total and equal at
    // every `b`. So the guarantee that actually holds this line is a DOUBLE
    // fault — the planner (layer 1) and the frozen producer (layer 3) — and
    // "three layers" must not be read as "the kernel is one of them".
    let mut env = env_uint();
    define(
        &mut env,
        "remv",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                surface_via("HMod", "hMod", "instHModUInt64", Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );

    // LAYER 1 — the PLANNER. `a % b` never becomes a plan, so no emitter ever
    // runs. The refusal must name the gap and carry options (v7/D3).
    let refusal =
        plan_clean_origin_body(&env, "remv").expect_err("`a % b` must NOT plan at a symbolic b");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a soundness boundary is still user-actionable");
    let note = refusal.note();
    assert!(
        note.contains("TOTAL") && note.contains("PANIC"),
        "the refusal must name the total-vs-panicking gap, not a generic boundary: {note}"
    );
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(note.contains("proof position"), "the option that always works must be offered: {note}");

    // LAYER 2 — the SEALED PLAN, reached by mutating a body whose plan IS
    // valid. `rem7` plans at `Const(7)`; an emitter that substituted the second
    // argument is refused structurally before any reflection.
    let env7 = env_with_rem7();
    let plan7 = plan_clean_origin_body(&env7, "rem7").expect("plannable");
    let refusal = admit_lowering(
        &env7,
        &plan7,
        &emitted_raw("rem7", BinOp::Rem, copy_arg(1), Operand::Copy(Place::local(2)), 1),
    )
    .expect_err("a variable divisor emitted for a literal-divisor plan must refuse");
    assert!(refusal.is_compiler_defect());

    // LAYER 3 — the FROZEN PRODUCER, which is NOT this lane. Written years
    // earlier for the opposite direction, it will not mint a variable divisor
    // at all, so a panicking body has no side B to be compared against.
    let producer = reflect_expr_try(&env, "p0 % p1", 2)
        .err()
        .expect("the FROZEN producer must refuse to mint `p0 % p1`");
    assert!(
        producer.contains("divisor"),
        "the producer's refusal must name the divisor boundary: {producer}"
    );
    // The control that keeps layer 3 from passing for the wrong reason: the
    // positive-literal rendering this lane DOES use must still mint, so the
    // refusal is about the divisor and not about `%`.
    assert!(
        reflect_expr_try(&env, "p0 % 7", 1).is_ok(),
        "`p0 % 7` must mint — otherwise layer 3 measured a ban on `%` itself"
    );
}

#[test]
fn half_6_a_ZERO_DIVISOR_is_refused_and_offered_NO_constant_rewrite() {
    // The `%`-specific asymmetry, and the reason this control is at `%`.
    //
    // For `/` the compiler CAN offer "write the value directly": `a / 0` is
    // definitionally the constant `0` at an OPEN `a`, because `Nat.div`
    // recurses on the DIVISOR. For `%` it cannot: `Nat.mod` goes through the
    // fuel-driven `Nat.modCore`, which recurses on the DIVIDEND, so `a % 0` is
    // STUCK at an open `a` and is NOT definitionally the identity.
    //
    // Both halves are asserted here so the asymmetry is pinned from this file
    // too, not only from `l7_p6`/`l7_p8`: an "improvement" that offered the
    // rewrite uniformly would be telling the user to write a function the
    // kernel does not agree with.
    let mut env = env_uint();
    define(
        &mut env,
        "rem0",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            surface_via("HMod", "hMod", "instHModUInt64", Expr::bvar(0), carrier_lit(0)),
        ),
    );

    let refusal = plan_clean_origin_body(&env, "rem0").expect_err("`a % 0` must NOT plan");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    let note = refusal.note();
    assert!(note.contains("TOTAL") && note.contains("options:"), "{note}");
    assert!(
        !note.contains("definitionally equal to the constant"),
        "`a % 0` must NOT be offered a constant rewrite — the identity does not hold: {note}"
    );

    // The kernel fact the missing option rests on, asserted rather than cited.
    let identity = reflect_expr(&env, "p0", 1);
    assert!(
        check_faithful(&env, "rem0", &identity, &u64_carrier()).is_err(),
        "`a % 0` is NOT definitionally the identity at an OPEN `a` (`Nat.modCore` is \
         fuel-driven and sticks). If this ever ADMITS, the `%` refusal may offer the \
         constant rewrite — and the doc comments on `CleanOriginShape::RawBinOp` and \
         `recognise_raw_binop_expr` must be re-derived, not merely reworded."
    );
}

#[test]
fn half_7_an_emission_at_the_WRONG_WIDTH_is_refused_by_the_KERNEL_ALONE() {
    // THE CASE NO PROBE IN THIS CRATE COVERS — the `control_5::half_8`
    // discipline, which landing 7 never received.
    //
    // `l7_p4`'s width mutation skews only the LITERAL's encoding, which makes
    // the body internally INCONSISTENT and side B's operand reader catches it
    // structurally. This body is internally CONSISTENT at u32: u32 locals, a
    // u32-encoded divisor, a perfectly valid `fn(u32) -> u32` remainder. It
    // recognizes, it agrees with the plan structurally, and it reflects at
    // UInt32 — and it TRUNCATES every value the UInt64 declaration talks about.
    //
    // Only the kernel comparison at the emitted width can see that, so this
    // half is where the kernel is doing work nothing above it can do. The
    // assertion is deliberately on the KERNEL variant: if a future refactor
    // starts catching this structurally that is fine, but it must be a
    // deliberate change with this expectation updated, because a structural
    // catch here would mean the width is being read from the PLAN rather than
    // from the emitted body — the "second place a width can disagree" the shape
    // docs say must not exist.
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("plannable");

    let refusal = admit_lowering(
        &env,
        &plan,
        &emitted_raw_at(
            "rem7",
            BinOp::Rem,
            copy_arg(1),
            Operand::Constant(ConstValue::Uint(7, 32)),
            1,
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
fn half_8_the_OTHER_FAMILY_S_realization_is_refused() {
    // The converse of `l7_p4` row 11, pointed at `%`. `+`/`-`/`*` realize as a
    // marker-authenticated CALL; this family realizes as a bare statement. An
    // emitter that produced the call shape for a `%` declaration emits a body
    // this family's reader does not read at all, and it must refuse BEFORE any
    // reflection happens rather than tunnel into another family's route.
    let env = env_with_rem7();
    let plan = plan_clean_origin_body(&env, "rem7").expect("plannable");

    let body = vf(
        "rem7",
        1,
        locals(2, Ty::u64()),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Call {
                    func: "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add"
                        .to_owned(),
                    args: vec![copy_arg(1), u64_const(7)],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Unreachable,
                    callee_identity: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    );
    let refusal = admit_lowering(&env, &plan, &body)
        .expect_err("the wrapping-call realization is not this family's body");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }), "got {refusal:?}");
}

#[test]
fn half_9_a_NON_PRELUDE_instance_is_a_capability_refusal() {
    // `control_5::half_10`'s boundary, at `HMod`. A user instance that is
    // kernel-REDUCIBLE to the prelude one would even pass defeq; it is refused
    // at RECOGNITION anyway, because tunneling an unknown instance into the
    // internal-error family would tell the user to report a compiler bug that
    // is actually a spelling boundary.
    let mut env = env_uint();
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    define(
        &mut env,
        "myInstHMod",
        Expr::apps(Expr::const_(Name::from_string("HMod"), zero3), [uint64(), uint64(), uint64()]),
        Expr::const_(Name::from_string("instHModUInt64"), vec![]),
    );
    define(
        &mut env,
        "rem_via_my_inst",
        u64_arrows(1),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            surface_via("HMod", "hMod", "myInstHMod", Expr::bvar(0), carrier_lit(7)),
        ),
    );

    let refusal = plan_clean_origin_body(&env, "rem_via_my_inst")
        .expect_err("a non-prelude instance is outside the measured fragment");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a capability refusal, never an internal error");
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(
        note.contains("instHModUInt64"),
        "the refusal must name the prelude instance that IS in the fragment: {note}"
    );
}

#[test]
fn half_10_every_option_is_spelled_in_the_OPERATOR_THAT_WAS_REFUSED() {
    // **A v7/D3 DEFECT, fixed and pinned here.**
    //
    // The refusal's options used to be literal `/` text on BOTH paths, so a
    // user who wrote `a % b` was told to write `a / 3` and
    // `if b == 0 then … else a / b`. Both suggestions are a different function
    // from the one they declared. v7/D3 says a refusal carries the fix; a
    // "fix" that silently changes the program's meaning is a defect, not a fix,
    // and it is worse than "unsupported" because it looks actionable.
    //
    // The `then` arm is the sharpest case. The declaration `a % b` ALREADY
    // returns `a` at `b = 0` (`x % 0 = x`, measured in `l7_p6`), so the
    // meaning-preserving guard is `if b == 0 then a else a % b`. A guard with
    // `then 0` declares something else entirely — and `half_6` measured that
    // `a % 0` is not definitionally the identity, so the kernel will not repair
    // the difference either.
    let env = island(&[
        "def divv (a : UInt64) (b : UInt64) : UInt64 := a / b",
        "def remv (a : UInt64) (b : UInt64) : UInt64 := a % b",
    ]);

    for (name, op, other, then_arm, zero_case) in [
        ("divv", "/", "%", "0", "`x / 0 = 0`"),
        ("remv", "%", "/", "a", "`x % 0 = x`"),
    ] {
        let note = plan_clean_origin_body(&env, name)
            .expect_err("a symbolic divisor must NOT plan")
            .note();

        // 1. every suggested REPLACEMENT is in the operator that was refused.
        assert!(
            note.contains(&format!("`a {op} 3`")),
            "`{name}`: the positive-literal option must be spelled in `{op}`, the operator \
             the user actually wrote: {note}"
        );
        assert!(
            note.contains(&format!("else a {op} b")),
            "`{name}`: the guard option's `else` arm must be spelled in `{op}`: {note}"
        );

        // 2. and the OTHER operator appears nowhere in an option. This is the
        //    half that would have caught the original defect: the old text
        //    passed check 1 for `/` and failed only for `%`.
        let options = note.split("options:").nth(1).expect("v7/D3: the refusal carries options");
        assert!(
            !options.contains(&format!("a {other} 3"))
                && !options.contains(&format!("a {other} b")),
            "`{name}`: an option is spelled in `{other}`, which is NOT the operator that was \
             refused — following it would declare a different function: {options}"
        );

        // 3. the guard's `then` arm is the value the declaration already
        //    denotes at a zero divisor, so the suggested guard PRESERVES the
        //    meaning of what the user wrote.
        assert!(
            note.contains(&format!("if b == 0 then {then_arm} else a {op} b")),
            "`{name}`: the guard's `then` arm must be `{then_arm}` — the value this \
             declaration already returns at a zero divisor ({zero_case}). Any other arm tells \
             the user to write a function the kernel will not identify with theirs: {note}"
        );

        // 4. the sentence closes cleanly. The totality clause is empty on the
        //    out-of-range-numeral path, which used to emit a dangling ", and".
        assert!(
            !note.contains(". ,") && !note.contains(" ,"),
            "`{name}`: the refusal has a dangling clause: {note}"
        );
    }
}

#[test]
fn half_11_the_GATE_IS_NOT_A_LAYER_and_must_never_be_counted_as_one() {
    // **THE MEASURED BLINDNESS, pinned so the next reader cannot assume it
    // away — this half CORRECTS `half_5`'s framing.**
    //
    // `half_5` calls the symbolic-divisor refusal "three independent layers".
    // Read precisely, its layer 2 is the STRUCTURAL check of an emitted body
    // against a plan that already fixed a LITERAL divisor — it is not the gate
    // deciding a symbolic-divisor claim. Put that claim to the gate directly
    // and the gate ADMITS. The real guarantee is a DOUBLE fault: the planner
    // (`recognise_raw_binop_expr`) and the FROZEN producer (`elab_term`).
    //
    // The reason is structural and no gate change can repair it. `check_faithful`
    // compares two CLEAN terms, and BOTH are total: side A is `UInt64.mod`,
    // which is *defined* as the round-trip lowering, so the two are definitionally
    // equal AT EVERY `b`, `b = 0` included. The divergence that matters is
    // Clean(total) vs MIR(panics) — and the MIR never reaches the kernel. So no
    // proposition over these two terms, conditional or otherwise, can see it.
    //
    // CONSEQUENCE, and the reason this is a control rather than a probe: anyone
    // relaxing the planner's divisor rule must replace the guarantee somewhere
    // the MIR is visible. The gate will not catch them, and this half is what
    // says so at the moment they try.
    let env = island(&[
        "def remv (a : UInt64) (b : UInt64) : UInt64 := a % b",
        // The Rust-side lowering a relaxed producer would mint for `p0 % p1`.
        "def remv_lowered (a : UInt64) (b : UInt64) : UInt64 := \
         UInt64.ofNat (Nat.mod (UInt64.toNat a) (UInt64.toNat b))",
        "def wrong (a : UInt64) (b : UInt64) : UInt64 := a",
    ]);
    let carrier = u64_carrier();

    let admitted = check_faithful(&env, "remv", &definition_value(&env, "remv_lowered"), &carrier)
        .expect(
            "MEASURED ADMIT expected. If this now REFUSES, the gate has gained a divisor rule \
             and that is a real capability change: re-derive `half_5`'s layer count, \
             `MirShape::RawBinOp`'s double-fault note, and the campaign finding that the \
             conditional-faithfulness lane is vacuous — do not merely reword them.",
        );
    assert_eq!(
        format!("{:?}", admitted.method()),
        "DefinitionalEquality",
        "the admission must be by DEFEQ — that is the whole point: the two terms are equal at \
         every divisor including zero, so the b=0 divergence is invisible here"
    );

    // THE ANTI-VACUITY CONTROL. The gate is working; it is not stuck at ADMIT.
    assert!(
        check_faithful(&env, "remv", &definition_value(&env, "wrong"), &carrier).is_err(),
        "if `fun a b => a` is admitted for `a % b`, this half measured a broken gate rather \
         than a blind one"
    );

    // AND THE LINE THAT ACTUALLY HOLDS, restated from this file so the two
    // facts are never separated: the PLANNER refuses, and it is load-bearing.
    assert!(
        plan_clean_origin_body(&env, "remv").is_err(),
        "the planner is one of the two faults that actually hold this line — if it stops \
         refusing while the gate still admits, a panicking body is emittable"
    );
}
