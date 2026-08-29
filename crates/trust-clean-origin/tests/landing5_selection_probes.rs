// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f LANDING 5 — the `a == b` / `BEq.beq` condition spelling, measured.**
//!
//! Landing 3 closed its ranked MISS 2 and recorded ONE newly measured absence
//! in the same breath:
//!
//! > `a == b` elaborates to `Eq Bool (BEq.beq {C} (instBEqOfDecidableEq …) a b)
//! > Bool.true`, a Bool-level decision lifted to a proposition, which
//! > `recognise_select_ite` does not read. The `select.eq` row is NOT
//! > unreachable — `a = b` mints exactly its `Eq {C} a b` spelling and plans —
//! > so this is a second spelling, not a regression, and a user writing the
//! > idiomatic `==` gets a refusal where `=` succeeds.
//!
//! This file is that measurement, taken in landing 3's method: **every side A
//! comes from `trust_certify::clean_island::CleanIslandSession::check_all`**,
//! the exact pipeline `clean_origin_mir` drives, never from a hand-built term.
//! Only MUTANTS are hand-built, which is what a mutant is for.
//!
//! # What was measured, and what landed
//!
//! | question | measured verdict | landed? |
//! |---|---|---|
//! | the exact side A for `a == b` | pinned node by node at u8/u16/u32/u64, plus the constant-arm and literal-comparison vocabularies. The decidability instance is `instDecidableEqBool <decision> Bool.true` UNIFORMLY — unlike `<`, which resolves a literal comparison through a Nat-reduced instance | — |
//! | does `a = b` still work? | **yes**, end to end: it plans, it emits the diamond, and `admit_lowering` admits it at all four widths. The refusal this landing writes recommends `=`, and the recommendation is measured rather than asserted | — |
//! | do the three existing routes admit `==`? | **no**, at all four widths, `GateRefusal::Disagreement`. And the kernel says so in its own voice: the island cannot close `theorem … := rfl` between the two `ite`s | — |
//! | can a producer mint the `==` spelling? | **yes** — `trust_spec_elab::admit_select_beq_function` ADMITS against the REAL elaboration at four widths, two arities and the whole operand vocabulary, with nine refused mutations including the `Bool.false` scrutinee | **YES** (side B's producer half) |
//! | can the compiler EMIT it? | **no**, and the blocker is named: the MIR that distinguishes the two spellings needs a `bool` CONSTANT operand, which is a new `materialize::TemplateOperand` PRIMITIVE — a closed match in `rustc_mir_transform`, by landing 4's own design | no — refused, blocker measured |
//! | `a != b` | NEW measured absence: the same tree with `Bool.not` around the decision, and no `Ne` anywhere in the emit lane's comparison vocabulary | no — recorded as a measured MISS |
//!
//! # THE FINDING: the distinction is REAL and it is INVISIBLE IN THE MIR
//!
//! Both spellings denote the same branch condition, so both realize the SAME
//! MIR — one `BinOp::Eq` into a `bool`, one `SwitchInt`. Side B reads that MIR
//! and cannot tell them apart, because there is nothing there to tell apart;
//! but the KERNEL can, and does, because side A's two terms are not
//! definitionally equal. So the gate refuses a body that is correct.
//!
//! There are exactly three ways out and this landing measures all three:
//!
//! 1. **make the MIR distinguish them** — transcribe the `Bool` decision and
//!    its `= Bool.true` lift as two comparisons, so side B reads the tree it
//!    reflects. This is the fix direction the discipline fixes (the EMITTER
//!    moves to meet the reader) and it is the one this landing would have
//!    taken. It needs `TemplateOperand::BoolScalar`, a new realization
//!    PRIMITIVE, and landing 4 made a new primitive a compile error in
//!    `rustc_mir_transform::clean_origin_mir::materialize`'s wildcard-free
//!    match — deliberately. That file is not this lane's to edit.
//! 2. **let side A choose which of two side-B spellings the gate is compared
//!    against** — cheap, crates-only, and REFUSED here. `admit_lowering`'s own
//!    words are *"the table does not see the plan and `trust_types` cannot see
//!    the table: side A's reading and side B's reading remain two
//!    authorships"*. A spelling bit taken from side A is a bit the kernel
//!    cannot refuse, whether it is passed as a parameter or found by trying
//!    both, and it is the double fault `docs/TCB.md` rests on.
//! 3. **refuse, and say so precisely** — which is what ships, with the
//!    producer half landed and kernel-measured so the emitted half is one
//!    template primitive away, and with a v7/D3 refusal that names the second
//!    spelling and the one-character fix.

use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, admit_lowering, check_faithful,
    plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth, SelectOperand};
use trust_types::admissible_body::{
    ArithOperand, SelectCmp, recognize_admissible_body, recognize_select_general,
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

/// Elaborate `sources` and report the REJECTION rather than panicking on it —
/// used where the refusal is the measurement.
fn island_refusal(sources: &[&str]) -> String {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(batch.is_rejected(), "this batch was expected to be REJECTED, and was not");
    format!("{batch:?}")
}

/// The four machine widths this lane carries.
const WIDTHS: [u32; 4] = [8, 16, 32, 64];

fn uint_ty(bits: u32) -> Expr {
    Expr::const_(Name::from_string(&format!("UInt{bits}")), vec![])
}

fn carrier_of(bits: u32) -> Carrier {
    carrier_at(&uint_ty(bits), &Ty::Int { width: bits, signed: false })
        .expect("UIntN -> uN is the exact-width carrier and must be granted")
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

fn body_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("the island registered no value for `{name}`"))
}

/// Uncurry an application spine: `((f a) b)` becomes `(f, [a, b])`.
fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut cursor = expr;
    let mut args = Vec::new();
    while let ExprKind::App(function, argument) = cursor.kind() {
        args.push(&**argument);
        cursor = function;
    }
    args.reverse();
    (cursor, args)
}

/// Peel `arity` lambdas off a definition body.
fn peel(body: &Expr) -> &Expr {
    let mut cursor = body;
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = &**inner;
    }
    cursor
}

/// A constant head with its level list, or `None`.
fn const_head(expr: &Expr) -> Option<(String, Vec<Level>)> {
    match expr.kind() {
        ExprKind::Const(name, levels) => Some((name.to_string(), levels.to_vec())),
        _ => None,
    }
}

fn assert_const(expr: &Expr, name: &str, levels: &[Level], what: &str) {
    let (found, found_levels) =
        const_head(expr).unwrap_or_else(|| panic!("{what}: expected the constant `{name}`"));
    assert_eq!(found, name, "{what}: wrong constant");
    assert_eq!(found_levels.as_slice(), levels, "{what}: wrong level list on `{name}`");
}

// ───────────────────────── side B: mint into a CLONE ─────────────────────────

/// Mint side B into a CLONE of `env` (mirroring `emit.rs`: a check must not
/// mutate the environment it checks) and return the reflected body term.
fn reflect(
    env: &Environment,
    mint: impl FnOnce(&mut Environment, &str) -> Result<trust_spec_elab::Admission, String>,
) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let name = "probe_landing5_reflection";
    mint(&mut scratch, name)?;
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .ok_or_else(|| "the reflected definition carries no value".to_owned())
}

/// Side B through the §6f landing 5 `==` route.
fn reflect_beq(
    env: &Environment,
    arity: usize,
    bits: u32,
    cmp_left: usize,
    cmp_right: SelectOperand,
    then_arm: SelectOperand,
    else_arm: SelectOperand,
) -> Result<Expr, String> {
    let domains: Vec<Domain> = (0..arity).map(|_| machine(bits)).collect();
    reflect(env, |scratch, name| {
        trust_spec_elab::admit_select_beq_function(
            scratch, name, &domains, cmp_left, cmp_right, then_arm, else_arm,
        )
    })
}

/// Side B through the §6f landing 3 GENERAL select route — the PROPOSITIONAL
/// `Eq {C} l r` spelling, unchanged by this landing.
fn reflect_general(
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

/// Assert the kernel ADMITS `side_b` for `side_a`, naming the case.
fn admits(env: &Environment, side_a: &str, side_b: &Expr, carrier: &Carrier, what: &str) {
    check_faithful(env, side_a, side_b, carrier)
        .unwrap_or_else(|refusal| panic!("`{what}` must ADMIT against `{side_a}`: {refusal:?}"));
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

/// Pin that TODAY's planner refuses this def as a capability boundary, and
/// hand back the refusal so its TEXT can be measured too.
fn plan_refusal(env: &Environment, name: &str) -> EmitRefusal {
    let refusal =
        plan_clean_origin_body(env, name).expect_err("this spelling has no row; planning refuses");
    assert!(
        matches!(refusal, EmitRefusal::NotEmittable { .. }),
        "expected today's capability refusal for `{name}`; got {refusal:?}"
    );
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is not a compiler defect");
    refusal
}

fn refusal_text(refusal: &EmitRefusal) -> String {
    match refusal {
        EmitRefusal::NotEmittable { reason, .. } => reason.clone(),
        other => panic!("expected `NotEmittable`, got {other:?}"),
    }
}

// ───────────────── hand-built MUTANTS of side B's `==` term ─────────────────

/// Rebuild the `==` select term with ONE construct changed. Everything the
/// producer decides is reproduced here EXCEPT the named mutation, so the
/// kernel's refusal is attributable to that construct and nothing else.
///
/// Hand-building is legitimate on this side and only on this side: R2/C9's
/// teaching is that a hand-built **side A** measures a producer nothing runs,
/// and side A in every probe below comes from the island. A mutant side B is
/// by definition a term no producer mints.
struct BeqMutation {
    /// Replace the `Bool.true` scrutinee with `Bool.false`, in BOTH the
    /// proposition and the instance — the coherent mutation, which is the hard
    /// one: an incoherent one would be refused by the kernel's typing before
    /// the gate ran and would measure the type checker, not the gate.
    false_scrutinee: bool,
    /// Mint the `BEq` instance as the bare `instBEq{C}` rather than
    /// `instBEqOfDecidableEq {C} instDecidableEq{C}` — a DIFFERENT decision
    /// procedure that side A's recognizer must never conflate with the one the
    /// elaborator synthesizes.
    bare_beq_instance: bool,
}

fn beq_mutant(bits: u32, arity: usize, mutation: &BeqMutation) -> Expr {
    let ty = uint_ty(bits);
    let carrier = format!("UInt{bits}");
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let bvar = |i: usize| Expr::bvar((arity - 1 - i) as u32);
    let scrutinee = Expr::const_(
        Name::from_string(if mutation.false_scrutinee { "Bool.false" } else { "Bool.true" }),
        vec![],
    );
    let instance = if mutation.bare_beq_instance {
        Expr::const_(Name::from_string(&format!("instBEq{carrier}")), vec![])
    } else {
        Expr::apps(
            Expr::const_(Name::from_string("instBEqOfDecidableEq"), vec![zero.clone()]),
            [
                ty.clone(),
                Expr::const_(Name::from_string(&format!("instDecidableEq{carrier}")), vec![]),
            ],
        )
    };
    let decision = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![zero]),
        [ty.clone(), instance, bvar(0), bvar(1)],
    );
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [Expr::const_(Name::from_string("Bool"), vec![]), decision.clone(), scrutinee.clone()],
    );
    let inst = Expr::apps(
        Expr::const_(Name::from_string("instDecidableEqBool"), vec![]),
        [decision, scrutinee],
    );
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, bvar(0), bvar(1)],
    );
    (0..arity).fold(body, |acc, _| Expr::lam(BinderInfo::Default, ty.clone(), acc))
}

// ───────────────── the emitted MIR, in extractor shape ─────────────────

/// The four-block O0 select diamond the emitter builds for a select at `bits`
/// — landing 4's ONE `ComparisonBranch` skeleton, restated here rather than
/// imported, so `l5_p2`'s round trip measures the emitter's contract and not a
/// picture this file also wrote.
fn emitted_diamond(
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

// ═══════ L5-P1 — THE EXACT SIDE A, node by node, at every width ═══════

/// **The measurement landing 3's ledger entry demanded**: *"its own kernel
/// measurement of the `Bool.true` scrutinee"*.
///
/// What the REAL island elaborator mints for `if a == b then a else b`, pinned
/// construct by construct at u8, u16, u32 and u64:
///
/// ```text
/// ite.{1} {C}
///   (Eq.{1} Bool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) #1 #0)
///                Bool.true)
///   (instDecidableEqBool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) #1 #0)
///                        Bool.true)
///   #1 #0
/// ```
///
/// Three things in that tree are decisions rather than noise, and each is
/// pinned:
///
/// 1. **The proposition is at `Bool`, not at the carrier.** `Eq.{1} Bool …` —
///    so the `select.eq` row's `Eq.{1} {C} l r` selector cannot match it, and
///    the row is not "nearly" reachable: it is a different type argument in
///    the first position of the proposition.
/// 2. **The decision term appears TWICE**, identically, in the proposition and
///    inside the instance. The producer builds it once for that reason.
/// 3. **The instance is `instDecidableEqBool`**, uniformly. It does NOT vary
///    with the comparison's operand vocabulary, which is the one respect in
///    which this spelling is SIMPLER than `<`: R2/C9 measured that `a < 10`
///    resolves its decidability through a Nat-reduced `instDecidableNatLt`
///    over a `toNat` projection chain, and the `==` spelling has no such arm
///    because the decision is already at `Bool` before decidability is asked
///    for. Pinned below against a literal comparison at every width.
#[test]
fn l5_p1_the_beq_spelling_is_pinned_node_by_node_at_every_width() {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());

    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let env = island(&[
            &format!(
                "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else b"
            ),
            &format!(
                "def eqlit (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == 0 then a else b"
            ),
            &format!(
                "def eqarm (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then 0 else b"
            ),
        ]);

        // A closure that decomposes one `==` select and returns
        // (comparison right operand, then arm, else arm), having pinned
        // everything structural on the way through.
        let decompose = |name: &str| -> (Expr, Expr, Expr) {
            let body = body_of(&env, name);
            let (head, args) = uncurry(peel(&body));
            assert_const(head, "ite", &[one.clone()], &format!("{name}: the head"));
            assert_eq!(args.len(), 5, "{name}: `ite` takes five arguments");
            assert_const(args[0], &carrier, &[], &format!("{name}: the result type"));

            // (1) the PROPOSITION — `Eq.{1} Bool <decision> Bool.true`.
            let (prop_head, prop_args) = uncurry(args[1]);
            assert_const(prop_head, "Eq", &[one.clone()], &format!("{name}: the proposition"));
            assert_eq!(prop_args.len(), 3, "{name}: `Eq` takes the type and two sides");
            assert_const(
                prop_args[0],
                "Bool",
                &[],
                &format!(
                    "{name}: MEASURED — the `==` proposition is stated at `Bool`, NOT at \
                     `{carrier}`. That is why `select.eq`'s `Eq {{C}} l r` selector cannot \
                     match it"
                ),
            );
            assert_const(
                prop_args[2],
                "Bool.true",
                &[],
                &format!("{name}: the SCRUTINEE the whole spelling turns on"),
            );

            // the DECISION — `BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} inst) l r`.
            let (beq_head, beq_args) = uncurry(prop_args[1]);
            assert_const(beq_head, "BEq.beq", &[zero.clone()], &format!("{name}: the decision"));
            assert_eq!(beq_args.len(), 4, "{name}: `BEq.beq` takes the type, the instance, l, r");
            assert_const(beq_args[0], &carrier, &[], &format!("{name}: the decision's carrier"));
            let (inst_head, inst_args) = uncurry(beq_args[1]);
            assert_const(
                inst_head,
                "instBEqOfDecidableEq",
                &[zero.clone()],
                &format!(
                    "{name}: MEASURED — the `BEq` instance is DERIVED FROM the carrier's \
                     `DecidableEq`, not a primitive `instBEq{carrier}`. A recognizer that \
                     accepted any `BEq` instance would accept a decision procedure that is \
                     not equality at all"
                ),
            );
            assert_eq!(inst_args.len(), 2, "{name}: the derived instance takes the type and inst");
            assert_const(inst_args[0], &carrier, &[], &format!("{name}: the instance's carrier"));
            assert_const(
                inst_args[1],
                &format!("instDecidableEq{carrier}"),
                &[],
                &format!("{name}: the carrier's own decidable equality"),
            );
            // the comparison's LEFT operand is always the first parameter here.
            assert!(
                matches!(beq_args[2].kind(), ExprKind::BVar(1)),
                "{name}: the comparison's left operand is the first parameter"
            );

            // (2) the decision appears AGAIN, identically, inside the instance.
            let (dec_head, dec_args) = uncurry(args[2]);
            assert_const(
                dec_head,
                "instDecidableEqBool",
                &[],
                &format!(
                    "{name}: MEASURED — the decidability instance is `instDecidableEqBool`, \
                     UNIFORMLY. It does not vary with the operand vocabulary the way `<`'s \
                     does (R2/C9's Nat-reduced `instDecidableNatLt`), because the decision \
                     is already at `Bool` before decidability is asked for"
                ),
            );
            assert_eq!(dec_args.len(), 2, "{name}: the Bool instance takes both sides");
            assert_eq!(
                format!("{:?}", dec_args[0]),
                format!("{:?}", prop_args[1]),
                "{name}: the instance's decision term is the proposition's, construct for \
                 construct — which is why the producer builds it ONCE"
            );
            assert_const(dec_args[1], "Bool.true", &[], &format!("{name}: the instance scrutinee"));

            (beq_args[3].clone(), args[3].clone(), args[4].clone())
        };

        // parameter-vs-parameter, parameter arms.
        let (rhs, then_arm, else_arm) = decompose("eqbeq");
        assert!(matches!(rhs.kind(), ExprKind::BVar(0)), "eqbeq: `b` on the comparison's right");
        assert!(matches!(then_arm.kind(), ExprKind::BVar(1)), "eqbeq: the then arm is `a`");
        assert!(matches!(else_arm.kind(), ExprKind::BVar(0)), "eqbeq: the else arm is `b`");

        // parameter-vs-NUMERAL: the numeral is the CARRIER spelling, exactly
        // as landing 3 measured for the arms — one operand vocabulary.
        let (rhs, _, _) = decompose("eqlit");
        let (num_head, num_args) = uncurry(&rhs);
        assert_const(
            num_head,
            &format!("{carrier}.ofNat"),
            &[],
            "eqlit: MEASURED — a literal on the comparison's RIGHT is the CARRIER numeral \
             spelling, which is what `Domain::numeral` mints on side B",
        );
        assert_eq!(num_args.len(), 1, "eqlit: `{{C}}.ofNat` takes one `Nat`");

        // a constant ARM, same vocabulary again.
        let (_, then_arm, _) = decompose("eqarm");
        let (arm_head, _) = uncurry(&then_arm);
        assert_const(
            arm_head,
            &format!("{carrier}.ofNat"),
            &[],
            "eqarm: a constant arm under `==` is the same carrier numeral landing 3 measured \
             under `<`",
        );

        eprintln!(
            "PROBE-ROW | if a == b (u{bits})       | side A: REAL = `ite {carrier} (Eq Bool \
             (BEq.beq …) Bool.true) (instDecidableEqBool …) …` | pinned"
        );
    }
}

// ═══════ L5-P2 — THE BASELINE: `a = b` still works, END TO END ═══════

/// **The refusal this landing writes tells the user to write `=`. That
/// recommendation is measured here, not asserted.**
///
/// v7/D3 makes a refusal with no next step a defect, and a refusal whose next
/// step does not work is worse than none. So the propositional spelling is
/// taken all the way through the pipeline at every width: it PLANS as
/// `Select`, the emitted diamond is RECOGNIZED, and `admit_lowering` — side
/// B's reader, side B's producer and the kernel gate — ADMITS it.
#[test]
fn l5_p2_the_propositional_spelling_still_admits_end_to_end() {
    for bits in WIDTHS {
        let env = island(&[&format!(
            "def eqprop (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := if a = b then a else b"
        )]);
        let carrier = carrier_of(bits);

        // It plans as the pre-landing-3 narrow rung, untouched by this landing.
        let plan = plan_clean_origin_body(&env, "eqprop").expect("`a = b` must plan");
        assert_eq!(
            plan.shape(),
            &CleanOriginShape::Select {
                cmp: SelectCmp::Eq,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
            "u{bits}: `a = b` is the `select.eq` row's own spelling"
        );

        // The FROZEN route's term is the one the island minted, so the gate is
        // a syntactic identity here — which is the point: the row is REACHABLE,
        // and `==`'s refusal is a second spelling rather than a dead row.
        let side_b = reflect(&env, |scratch, name| {
            trust_spec_elab::admit_select_function(
                scratch,
                name,
                &[machine(bits), machine(bits)],
                trust_spec_elab::SelectCmp::Eq,
                0,
                1,
                0,
                1,
            )
        })
        .expect("the frozen select route mints");
        admits(&env, "eqprop", &side_b, &carrier, "the frozen `Eq` route");

        // And the WHOLE round trip: the emitted diamond, read back by side B's
        // own recognizer, reflected, and gated.
        let extracted = emitted_diamond(
            2,
            bits,
            BinOp::Eq,
            0,
            ArithOperand::Param(1),
            ArithOperand::Param(0),
            ArithOperand::Param(1),
        );
        admit_lowering(&env, &plan, &extracted).unwrap_or_else(|refusal| {
            panic!("u{bits}: the `=` round trip must admit: {refusal:?}")
        });

        eprintln!("PROBE-ROW | if a = b  (u{bits})       | plan + emit + gate | ADMIT (baseline)");
    }
}

// ═══════ L5-P3 — THE REFUSAL, and the kernel's own account of it ═══════

/// **Every existing route is refused against `==`, at every width — and the
/// mechanism is not "a producer cannot spell it" but "the two terms are not
/// definitionally equal".**
///
/// Landing 3 recorded the shape of the miss. This measures its mechanism, and
/// the second half is the load-bearing one: the island itself cannot close
///
/// ```text
/// theorem bridge (a b : UInt64) :
///   (if a == b then a else b) = (if a = b then a else b) := rfl
/// ```
///
/// The statement ELABORATES — both sides are well-typed `UInt64` — and `rfl`
/// is rejected with a type mismatch. That is the kernel saying, in its own
/// voice and outside this crate, that the two `ite`s are not defeq. Both are
/// stuck: side A's on `instDecidableEqBool` applied to a neutral decision,
/// side B's on `instDecidableEq{C}` applied to two neutral parameters, and
/// the kernel does not case-split a stuck `Decidable`. So no producer that
/// mints the propositional spelling can ever be admitted for `==`, at any
/// width, and no amount of reducibility changes that.
///
/// # 2026-08-27 — this probe was RED, and the verdict had not moved at all
///
/// It asserted `rejection.contains("BEq.beq")`. At clean pin `79926e80a` the
/// island's message is
///
/// ```text
/// Type mismatch: expected
///   ite UInt64 ((fvar#0 == fvar#1) = Bool.true)
///              (instDecidableEqBool (fvar#0 == fvar#1) Bool.true) fvar#0 fvar#1
/// = ite UInt64 (fvar#0 = fvar#1) (instDecidableEqUInt64 fvar#0 fvar#1) fvar#0 fvar#1,
/// got Decidable.rec ((fvar#0 == fvar#1) = Bool.true) … = Decidable.rec …
/// ```
///
/// — still a `Type mismatch`, still on the same two `ite`s, with no `BEq.beq`
/// in it because clean `6d1663115` (*"`Display for Expr` speaks Lean notation,
/// not spine juxtaposition"*) prints `@BEq.beq {C} inst a b` as `a == b`. The
/// same pin move turned `landing3_selection_probes` `l3_p6` red for the same
/// reason, on `LT.lt`.
///
/// **This is a diagnostic GAIN and it is re-pinned as one, not re-blessed.**
/// The old message was two nested spines a reader had to diff by eye; the new
/// one puts the two `ite`s side by side with the difference legible —
/// `(a == b) = Bool.true` under `instDecidableEqBool` against `a = b` under
/// `instDecidableEqUInt64` — and its `got` half shows both sides stuck as
/// `Decidable.rec` over a neutral scrutinee. That last part is the actual
/// mechanism this doc-comment has asserted in prose since landing 5 and never
/// measured, so the row now measures it.
///
/// **What the row is re-pinned ON matters more than the re-pin.** A message is
/// genuinely this row's subject, so it must assert on text — but it now asserts
/// on the pieces a notation table cannot hide. `instDecidableEqBool`,
/// `instDecidableEqUInt{N}`, `Bool.true` and `Decidable.rec` have no notation
/// entry (the table covers `Eq`, `Ne`, `Iff`, `And`, `Or`, `Not`, the `H*`
/// family, `LE`/`LT`/`GE`/`GT`, `BEq`, `Neg.neg`, `Exists`, `OfNat.ofNat`), and
/// the two DIFFERENT decidability instances are the refusal's whole mechanism:
/// if they ever became the same constant, the spellings would have been
/// identified upstream and all of landing 5 would need re-measuring. The
/// decision term itself is accepted in either spelling, so a printer that goes
/// back to juxtaposition does not turn this row red a second time.
#[test]
fn l5_p3_no_existing_route_admits_the_beq_spelling_and_the_kernel_says_why() {
    for bits in WIDTHS {
        let env = island(&[&format!(
            "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := if a == b then a else b"
        )]);
        let carrier = carrier_of(bits);

        // 1. the FROZEN parameter-select route (`admit_select_function`).
        let frozen = reflect(&env, |scratch, name| {
            trust_spec_elab::admit_select_function(
                scratch,
                name,
                &[machine(bits), machine(bits)],
                trust_spec_elab::SelectCmp::Eq,
                0,
                1,
                0,
                1,
            )
        })
        .expect("the frozen select route mints");
        refused(&env, "eqbeq", &frozen, &carrier, "the frozen `Eq` route against `==`");

        // 2. the FROZEN literal route, at the same comparison.
        let literal = reflect(&env, |scratch, name| {
            trust_spec_elab::admit_select_literal_function(
                scratch,
                name,
                &[machine(bits), machine(bits)],
                trust_spec_elab::SelectCmp::Eq,
                0,
                0,
                0,
                1,
            )
        })
        .expect("the frozen literal route mints");
        refused(&env, "eqbeq", &literal, &carrier, "the frozen literal route against `==`");

        // 3. landing 3's GENERAL route — the newest one, and still refused.
        let general = reflect_general(
            &env,
            2,
            bits,
            trust_spec_elab::SelectCmp::Eq,
            0,
            SelectOperand::Param(1),
            SelectOperand::Param(0),
            SelectOperand::Param(1),
        )
        .expect("the general select route mints");
        refused(&env, "eqbeq", &general, &carrier, "landing 3's general route against `==`");
    }

    // 4. THE KERNEL'S OWN ACCOUNT. Measured outside this crate entirely.
    let rejection = island_refusal(&[
        "theorem bridge (a b : UInt64) : (if a == b then a else b) = (if a = b then a else b) \
         := rfl",
    ]);
    assert!(
        rejection.contains("Type mismatch"),
        "MEASURED: the island rejects the `rfl` bridge between the two spellings with a TYPE \
         MISMATCH — the kernel's own statement that they are not definitionally equal. If this \
         ever starts closing, the whole of landing 5 is superseded and must be re-measured: \
         {rejection}"
    );
    // The rejection must NAME THE DECISION TERM it is stuck on. It is spelled
    // in whichever of the two forms the printer currently uses — `BEq.beq`
    // before clean `6d1663115`, `==` since — and this row does not care which,
    // because the printer is not the subject. See the note below.
    assert!(
        rejection.contains("BEq.beq") || rejection.contains("=="),
        "the rejection must name the decision term it is stuck on: {rejection}"
    );

    // THE PART THAT IS THE SUBJECT, and that no notation table can hide: the
    // two spellings resolve DIFFERENT decidability instances, and that is the
    // whole mechanism of the refusal. `instDecidableEqBool` decides the
    // Bool-level `(a == b) = true`; `instDecidableEqUInt64` decides the
    // propositional `a = b` at the carrier. Neither constant has a notation
    // entry, so neither can be printed away.
    assert!(
        rejection.contains("instDecidableEqBool"),
        "the `==` side must resolve the BOOL decision instance: {rejection}"
    );
    assert!(
        rejection.contains("instDecidableEqUInt64"),
        "the `=` side must resolve the CARRIER equality instance — if both sides now name the \
         same instance, the two spellings have been identified somewhere upstream and the \
         whole of landing 5 must be re-measured: {rejection}"
    );
    assert!(
        rejection.contains("Bool.true"),
        "the `==` side is the Bool decision LIFTED to a proposition, and the lift is what the \
         `select.eq` row does not read: {rejection}"
    );

    // WHY it does not close, in the kernel's own output rather than in this
    // file's prose: both sides reduce to a `Decidable.rec` STUCK on a neutral
    // scrutinee. The doc-comment above has asserted this since landing 5 and
    // never measured it; the notation-aware message now shows it.
    assert!(
        rejection.contains("Decidable.rec"),
        "the mismatch must bottom out in a STUCK `Decidable.rec` — that, not a missing \
         producer, is why no reducibility setting can ever close this bridge: {rejection}"
    );
    eprintln!(
        "PROBE-ROW | the `rfl` bridge          | side A: REAL | REJECTED by the island — the \
         two `ite`s are not defeq, measured in the kernel's own voice"
    );
}

// ═══════ L5-P4 — THE PRODUCER ARM: ADMIT, with nine refused mutations ═══════

/// **`trust_spec_elab::admit_select_beq_function` ADMITS against the REAL
/// elaboration**, across the whole vocabulary the route is stated over, with
/// every ADMIT paired against mutations the kernel must refuse.
///
/// The coverage: four widths × {parameter comparison, literal comparison} ×
/// {parameter arms, constant then-arm, constant else-arm, both constant} ×
/// {arity 1, arity 2}. The mutations, all at u64 unless noted:
///
/// 1. **swapped arms** — the polarity trap every select route documents;
/// 2. **the wrong constant** in a constant arm;
/// 3. **a PARAMETER arm where a constant arm was elaborated**;
/// 4. **the comparison's operands swapped** (`b == a` for `a == b`);
/// 5. **a width skew** — the u32 mint against the u64 declaration;
/// 6. **the PROPOSITIONAL spelling** — `Eq {C} a b`, i.e. exactly what every
///    pre-landing-5 route mints (this is `l5_p3` restated as a mutation of the
///    new route, so the two routes are measured against each other);
/// 7. **`Bool.false` for `Bool.true`**, coherently in both positions — the
///    ledger's named demand, and the mutation that changes the function while
///    leaving every arm, index and width correct;
/// 8. **a bare `instBEq{C}` instance** for the derived
///    `instBEqOfDecidableEq {C} instDecidableEq{C}` — a different decision
///    procedure in the same position;
/// 9. **the `!=` side A** against the `==` mint — `Bool.not` must not be
///    absorbed silently.
#[test]
fn l5_p4_the_beq_producer_admits_against_the_real_elaboration() {
    for bits in WIDTHS {
        let env = island(&[
            &format!(
                "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else b"
            ),
            &format!(
                "def eqlit (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == 0 then a else b"
            ),
            &format!(
                "def eqthen (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then 0 else b"
            ),
            &format!(
                "def eqelse (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else 7"
            ),
            &format!(
                "def eqboth (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then 1 else 2"
            ),
            &format!("def eqone (a : UInt{bits}) : UInt{bits} := if a == 3 then 4 else a"),
        ]);
        let carrier = carrier_of(bits);
        let p0 = SelectOperand::Param(0);
        let p1 = SelectOperand::Param(1);

        // ── the ADMITs, over the whole operand vocabulary ──────────────────
        for (name, arity, cmp_right, then_arm, else_arm) in [
            ("eqbeq", 2, p1, p0, p1),
            ("eqlit", 2, SelectOperand::Literal(0), p0, p1),
            ("eqthen", 2, p1, SelectOperand::Literal(0), p1),
            ("eqelse", 2, p1, p0, SelectOperand::Literal(7)),
            ("eqboth", 2, p1, SelectOperand::Literal(1), SelectOperand::Literal(2)),
            ("eqone", 1, SelectOperand::Literal(3), SelectOperand::Literal(4), p0),
        ] {
            let side_b = reflect_beq(&env, arity, bits, 0, cmp_right, then_arm, else_arm)
                .unwrap_or_else(|e| panic!("u{bits} `{name}`: the `==` route must mint: {e}"));
            admits(
                &env,
                name,
                &side_b,
                &carrier,
                &format!("u{bits} `{name}` through the `==` route"),
            );
        }

        // ── the mutations that travel with the width ──────────────────────
        // 1. swapped arms.
        let swapped = reflect_beq(&env, 2, bits, 0, p1, p1, p0).expect("mints");
        refused(&env, "eqbeq", &swapped, &carrier, "swapped arms");
        // 4. the comparison's operands swapped.
        let flipped = reflect_beq(&env, 2, bits, 1, p0, p0, p1).expect("mints");
        refused(&env, "eqbeq", &flipped, &carrier, "`b == a` for `a == b`");
        // 6. the PROPOSITIONAL spelling, minted by the general route.
        let propositional =
            reflect_general(&env, 2, bits, trust_spec_elab::SelectCmp::Eq, 0, p1, p0, p1)
                .expect("mints");
        refused(&env, "eqbeq", &propositional, &carrier, "the propositional `Eq {C} a b` spelling");
        // 7. the `Bool.false` scrutinee — the ledger's named demand.
        let false_scrutinee =
            beq_mutant(bits, 2, &BeqMutation { false_scrutinee: true, bare_beq_instance: false });
        refused(&env, "eqbeq", &false_scrutinee, &carrier, "`Bool.false` for `Bool.true`");
        // 8. a bare `instBEq{C}` for the derived instance.
        let bare_instance =
            beq_mutant(bits, 2, &BeqMutation { false_scrutinee: false, bare_beq_instance: true });
        refused(&env, "eqbeq", &bare_instance, &carrier, "a bare `instBEq{C}` instance");
        // …and the FAITHFUL rebuild of the same hand-built shape ADMITs, so
        // the two mutants above are attributable to their one construct and
        // not to hand-building.
        let faithful =
            beq_mutant(bits, 2, &BeqMutation { false_scrutinee: false, bare_beq_instance: false });
        admits(&env, "eqbeq", &faithful, &carrier, "the hand-built FAITHFUL control");

        // 2 / 3. the constant-arm mutations, against the constant-arm side A.
        let wrong_value =
            reflect_beq(&env, 2, bits, 0, p1, SelectOperand::Literal(1), p1).expect("mints");
        refused(&env, "eqthen", &wrong_value, &carrier, "the wrong constant in the then arm");
        let param_for_const = reflect_beq(&env, 2, bits, 0, p1, p0, p1).expect("mints");
        refused(&env, "eqthen", &param_for_const, &carrier, "a parameter arm for a constant arm");
    }

    // 5. THE WIDTH SKEW. A u32 mint against the u64 declaration and back.
    let env = island(&[
        "def eqbeq (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
        "def eqbeq32 (a : UInt32) (b : UInt32) : UInt32 := if a == b then a else b",
    ]);
    let narrow = reflect_beq(
        &env,
        2,
        32,
        0,
        SelectOperand::Param(1),
        SelectOperand::Param(0),
        SelectOperand::Param(1),
    )
    .expect("mints");
    refused(&env, "eqbeq", &narrow, &carrier_of(64), "the u32 mint against the u64 declaration");
    let wide = reflect_beq(
        &env,
        2,
        64,
        0,
        SelectOperand::Param(1),
        SelectOperand::Param(0),
        SelectOperand::Param(1),
    )
    .expect("mints");
    refused(&env, "eqbeq32", &wide, &carrier_of(32), "the u64 mint against the u32 declaration");

    // 9. the `!=` side A against the `==` mint.
    let env = island(&["def neqbeq (a : UInt64) (b : UInt64) : UInt64 := if a != b then a else b"]);
    let positive = reflect_beq(
        &env,
        2,
        64,
        0,
        SelectOperand::Param(1),
        SelectOperand::Param(0),
        SelectOperand::Param(1),
    )
    .expect("mints");
    refused(&env, "neqbeq", &positive, &carrier_of(64), "the `==` mint against a `!=` side A");
}

// ═══════ L5-P5 — THE ANTI-DRIFT CONTROL over the whole overlap ═══════

/// **Two builders of one term can only drift** — l3_p4's rule, applied to the
/// route this landing adds.
///
/// `admit_select_beq_function` is NOT a variant of the general route: it is a
/// fourth construction of the same `ite` tree with a different condition. So
/// what must be pinned is not equality (the terms differ, deliberately) but
/// **that they differ in EXACTLY two positions**: `ite`'s proposition and its
/// decidability instance. The result type, both arms and the argument order
/// must be construct-for-construct identical, at every width, every arity and
/// every operand assignment — because those are the positions where a second
/// builder would silently disagree with the first, and where a disagreement
/// would be a wrong binary rather than a refusal.
///
/// 4 widths × 2 arities × 5 operand assignments = **40 term comparisons**,
/// standing.
#[test]
fn l5_p5_the_beq_route_differs_from_the_general_route_in_exactly_two_positions() {
    let env = island(&["def anchor (a : UInt64) : UInt64 := a"]);
    let p0 = SelectOperand::Param(0);
    let p1 = SelectOperand::Param(1);
    let mut compared = 0usize;

    for bits in WIDTHS {
        for arity in [1usize, 2] {
            let assignments: Vec<(SelectOperand, SelectOperand, SelectOperand)> = if arity == 1 {
                vec![
                    (SelectOperand::Literal(0), p0, p0),
                    (SelectOperand::Literal(3), SelectOperand::Literal(4), p0),
                    (SelectOperand::Literal(9), p0, SelectOperand::Literal(1)),
                    (
                        SelectOperand::Literal(2),
                        SelectOperand::Literal(5),
                        SelectOperand::Literal(6),
                    ),
                    (SelectOperand::Literal(7), p0, p0),
                ]
            } else {
                vec![
                    (p1, p0, p1),
                    (p1, SelectOperand::Literal(0), p1),
                    (p1, p0, SelectOperand::Literal(7)),
                    (SelectOperand::Literal(4), p0, p1),
                    (
                        SelectOperand::Literal(1),
                        SelectOperand::Literal(2),
                        SelectOperand::Literal(3),
                    ),
                ]
            };
            for (cmp_right, then_arm, else_arm) in assignments {
                let beq = reflect_beq(&env, arity, bits, 0, cmp_right, then_arm, else_arm)
                    .expect("the `==` route mints");
                let general = reflect_general(
                    &env,
                    arity,
                    bits,
                    trust_spec_elab::SelectCmp::Eq,
                    0,
                    cmp_right,
                    then_arm,
                    else_arm,
                )
                .expect("the general route mints");

                let (beq_head, beq_args) = uncurry(peel(&beq));
                let (gen_head, gen_args) = uncurry(peel(&general));
                let case = format!("u{bits}/arity {arity}/{cmp_right:?}/{then_arm:?}/{else_arm:?}");

                assert_eq!(
                    format!("{beq_head:?}"),
                    format!("{gen_head:?}"),
                    "{case}: both routes must build the SAME `ite` head"
                );
                assert_eq!(beq_args.len(), 5, "{case}: `ite` takes five arguments");
                assert_eq!(gen_args.len(), 5, "{case}: `ite` takes five arguments");
                for position in [0usize, 3, 4] {
                    assert_eq!(
                        format!("{:?}", beq_args[position]),
                        format!("{:?}", gen_args[position]),
                        "{case}: `ite` argument {position} (the result type and the two arms) \
                         must be construct-for-construct IDENTICAL across the two routes — a \
                         disagreement here is a wrong binary, not a refusal"
                    );
                }
                for position in [1usize, 2] {
                    assert_ne!(
                        format!("{:?}", beq_args[position]),
                        format!("{:?}", gen_args[position]),
                        "{case}: `ite` argument {position} is the CONDITION, and the two \
                         spellings must differ there — if they ever agree, the `==` route has \
                         collapsed into the propositional one and `l5_p4`'s ADMITs are \
                         measuring the wrong thing"
                    );
                }
                // The lambda depth is the arity in both, from the same input.
                assert_eq!(
                    lambda_depth(&beq),
                    arity,
                    "{case}: the `==` route binds one lambda per parameter"
                );
                assert_eq!(lambda_depth(&general), arity, "{case}: …and so does the general one");
                compared += 1;
            }
        }
    }
    assert_eq!(compared, 40, "the overlap this control stands over must not shrink silently");
}

fn lambda_depth(expr: &Expr) -> usize {
    let mut depth = 0;
    let mut cursor = expr;
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        depth += 1;
        cursor = &**inner;
    }
    depth
}

// ═══════ L5-P6 — THE EMITTED HALF IS OUT OF REACH, and the refusal says so ═══════

/// **The planner still refuses `==`, and this landing does not pretend
/// otherwise. What changed is the REFUSAL.**
///
/// Before this landing a user who wrote `if a == b` got the generic
/// out-of-fragment prose, which names fifteen rows and four options and does
/// not mention that changing one character to `=` succeeds. That is a v7/D3
/// defect: *"we state the rules but if somebody doesn't follow the rules, then
/// provide feedback via the compiler on how to fix the situation (provide
/// options)"*. After it, side A RECOGNIZES the spelling and says so.
///
/// The refusal is a REFUSAL and nothing else: it selects no row, plans no
/// shape and emits no byte. The recognizer that produces it is a diagnostic
/// reader, and `l5_p6` pins both halves — the text, and that the plan is still
/// an error.
///
/// It also pins the E6 containment: the `==` spelling changes nothing in the
/// kernel-import direction, because there is no emitted body for it at all.
///
/// # SUPERSEDED IN PART by §6f landing 6 — the SUBJECT moved, the CONTRACT did not
///
/// Landing 6 gave `==` its own two-step MIR realization and its own
/// `select.beq` row, so the two `==` fixtures this probe was written over now
/// PLAN (`landing6_selection_probes::l6_p2` takes them to the gate). What
/// remains refused, and is what this probe now measures, is the OTHER half of
/// landing 5's recognizer: `!=`, whose blocker moved but did not clear, and an
/// `==` whose OPERANDS are outside the shared select vocabulary. The v7/D3
/// contract itself is untouched — the refusal must still name the operator, the
/// kernel tree, the boundary and the options, and must still not fall through
/// to the generic fifteen-row prose — so those assertions are kept verbatim and
/// only the fixtures they run over changed.
#[test]
fn l5_p6_the_planner_refuses_and_the_refusal_names_the_second_spelling() {
    for bits in WIDTHS {
        let env = island(&[
            // `!=` — the spelling landing 6 measured and left unserved.
            &format!(
                "def neqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a != b then a else b"
            ),
            // `==` with a COMPUTED operand: the operator is emittable since
            // landing 6, this operand is not (l3_p5's elaborator normal form).
            &format!(
                "def eqcomputed (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a + 1 == b then a else b"
            ),
        ]);
        for name in ["neqbeq", "eqcomputed"] {
            let text = refusal_text(&plan_refusal(&env, name));
            for fragment in [
                // it must NAME the spelling it found …
                "BEq.beq",
                "Bool.true",
                // … and it must stay a MEASURED boundary statement, not a rule.
                "v7/D2",
                "options:",
            ] {
                assert!(
                    text.contains(fragment),
                    "u{bits} `{name}`: the refusal must contain {fragment:?}; got:\n{text}"
                );
            }
            // The generic fragment prose must NOT be what these users see:
            // the whole point is that this shape has a specific diagnosis.
            assert!(
                !text.contains("no selection row for"),
                "u{bits} `{name}`: a recognized second spelling must not fall through to the \
                 generic missing-row text; got:\n{text}"
            );
        }
        // …and the two spellings get DIFFERENT diagnoses, which is the half a
        // single shared string would quietly lose.
        assert!(
            refusal_text(&plan_refusal(&env, "neqbeq")).contains("`!=`"),
            "u{bits}: the `!=` refusal names its own operator"
        );
        assert!(
            refusal_text(&plan_refusal(&env, "eqcomputed")).contains("`==`"),
            "u{bits}: …and the out-of-fragment `==` names its own"
        );
    }

    // E6 containment. Landing 5 pinned this against the diamond the `==` shape
    // WOULD emit if it had a row; landing 6 gave it a row and a DIFFERENT
    // (two-step) realization, so what this half now pins is the constant-arm
    // ONE-step diamond — landing 3's boundary, restated here because landing 5
    // added a producer that could tempt someone to widen the import direction.
    // The two-step body's own containment is `l6_p3`.
    let would_be = emitted_diamond(
        2,
        64,
        BinOp::Eq,
        0,
        ArithOperand::Param(1),
        ArithOperand::Param(0),
        ArithOperand::Const(7),
    );
    assert!(
        recognize_admissible_body(&would_be).is_none(),
        "the E6 kernel-import direction must stay blind to a constant-arm diamond — landing 3's \
         measurement, restated here because landing 5 adds a producer that could tempt someone \
         to widen it"
    );
    assert!(
        recognize_select_general(&would_be).is_some(),
        "…while the CALL-lane reader still reads it, so the containment is a statement about \
         the import direction and not about the shape"
    );
}

// ═══════ L5-P7 — `a != b`: the NEW measured absence ═══════

/// **A third spelling, measured and recorded rather than guessed at.**
///
/// `a != b` elaborates to the SAME tree as `a == b` with a `Bool.not` wrapped
/// around the decision:
///
/// ```text
/// Eq.{1} Bool (Bool.not (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r))
///             Bool.true
/// ```
///
/// It is a separate demand from `==` and not a flag on it, for a reason the
/// tree makes plain: the emit lane's comparison vocabulary
/// (`trust_types::admissible_body::SelectCmp`) is `{Lt, Le, Eq}` and has **no
/// `Ne`**, so even the MIR realization is absent — where `==` at least
/// realizes the same diamond `=` does. Admitting `!=` would need a comparison
/// variant, its `BinOp::Ne` realization, its polarity in the `SwitchInt`, and
/// its own controls. Recorded as a MISS with that blocker named.
#[test]
fn l5_p7_the_not_equal_spelling_is_a_third_tree_with_no_comparison_at_all() {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    for bits in WIDTHS {
        let carrier = format!("UInt{bits}");
        let env = island(&[&format!(
            "def neqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := if a != b then a else b"
        )]);
        let body = body_of(&env, "neqbeq");
        let (head, args) = uncurry(peel(&body));
        assert_const(head, "ite", &[one.clone()], "the `!=` head");
        let (prop_head, prop_args) = uncurry(args[1]);
        assert_const(prop_head, "Eq", &[one.clone()], "the `!=` proposition");
        assert_const(prop_args[0], "Bool", &[], "the `!=` proposition is at `Bool` too");
        assert_const(prop_args[2], "Bool.true", &[], "the scrutinee is still `Bool.true`");
        let (not_head, not_args) = uncurry(prop_args[1]);
        assert_const(
            not_head,
            "Bool.not",
            &[],
            "MEASURED: `!=` is `==` with a `Bool.not` around the decision — the negation lives \
             in the DECISION, not in the scrutinee, so it cannot be reached by flipping \
             `Bool.true` to `Bool.false`",
        );
        assert_eq!(not_args.len(), 1, "`Bool.not` takes one argument");
        let (beq_head, _) = uncurry(not_args[0]);
        assert_const(beq_head, "BEq.beq", &[zero.clone()], "…and it wraps the same decision");
        assert!(!carrier.is_empty());

        // Nothing plans it, and the refusal names it as the negated spelling.
        let text = refusal_text(&plan_refusal(&env, "neqbeq"));
        assert!(
            text.contains("`!=`"),
            "u{bits}: the `!=` refusal must name the operator it found; got:\n{text}"
        );
    }
    eprintln!(
        "PROBE-ROW | if a != b                 | side A: REAL = `Eq Bool (Bool.not (BEq.beq …)) \
         Bool.true` | MISS (no `Ne` in the emit lane's comparison vocabulary at all)"
    );
}
