// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 11 (well-founded recursion, TYPECLASS SPELLING) — the
//! planted-violation battery for the widened R2 guard recogniser.**
//!
//! `control_8` is the R2 mutation battery for the F LAYER: it varies side B and
//! watches the gate refuse. This file varies SIDE A's SPELLING and watches the
//! RECOGNISER (`emit::recognise_wf_nat_rec`, reached through the real
//! `plan_clean_origin_body`) decide — because that is the component that was
//! measured wrong.
//!
//! # What was wrong, stated exactly
//!
//! The R2 recogniser read the guard as `Nat.lt 0 n` / `Nat.decLt 0 n` and the
//! decrease as `Nat.sub n 1` / `Nat.pred n`. The elaborator mints NONE of those
//! for the surface text the recogniser's own refusal advertises (`if h : 0 < n`
//! … `n - 1`): it mints `@LT.lt.{0} Nat instLTNat 0 n`, `instDecidableNatLt 0 n`
//! and `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat n 1`. Every hand-built probe
//! was green while the real lane refused — the C9 teaching, restated on R2.
//!
//! # The rule the widening must NOT become
//!
//! "Accept any `LT`/`HSub` at `Nat`." A typeclass application denotes whatever
//! its INSTANCE denotes, and the instances are not interchangeable:
//! `Classical.Order.instLT Nat instLENat` unfolds to `0 ≤ n ∧ ¬ n ≤ 0`, not to
//! `Nat.le 1 n` (`clean-kernel/src/env/order_lemmas_succ.rs` records that exact
//! mis-resolution as a landed defect). So the widening is "exactly two names
//! per position, each measured δ-equal to the one the emitted bignum operation
//! realises", and every OTHER near-miss must still be refused.
//!
//! **Each test below plants ONE such near-miss and asserts the refusal NAMES
//! ITS OWN BOUNDARY.** Asserting the boundary text — not merely "some refusal"
//! — is what makes each test sensitive to exactly one mutation: relaxing a
//! different check leaves the body refused, but by a DIFFERENT message, and the
//! assertion still fires. Every planted near-miss is a REAL kernel-checked
//! declaration; where the kernel refuses the near-miss outright, that is said
//! rather than hidden (see the universe-level row, which is a premise pin and
//! not a recogniser pin, and says so).
//!
//! # HONESTY RULE, inherited from `control_7`/`control_8`
//!
//! Every ADMIT is paired with a refused mutation at the same layer, and the
//! recogniser is FROZEN against this file: if a verdict here is not the one the
//! lane wants, the fix is `emit.rs`, never an edit to these assertions.
//!
//! # RECONCILED 2026-08-25 — the constant-minuend row was measuring a verdict
//! # the compiler stopped returning two days before this file landed
//!
//! `control_11_a_minuend_that_is_not_the_parameter_is_refused` asserted a
//! REFUSAL carrying *"outside this fragment's vocabulary"*. It was red on
//! arrival, and the diagnosis is **capability gain, not lost refusal** — R2's
//! minuend boundary still fires, measured; what changed is that a SECOND lane
//! reaches the same body with a different, faithful claim.
//!
//! `if h : 0 < n then n + f (1 - 1) else 0` DENOTES the identity: `1 - 1` is
//! `0` (kernel `is_def_eq`), so `f 0 = 0` and `f n = n + f 0 = n`. R2 refuses
//! it — correctly, because reading the self-call as `n - 1` would emit the
//! TRIANGULAR function — and `plan_clean_origin_body`'s
//! `recognise_inductive_projection` fallback then proves the whole function
//! equal to parameter 0 by kernel-checked structural induction. The emitted
//! `_0 = move _1` is what the declaration computes, and `admit_lowering`
//! re-earns that verdict as `FaithfulnessMethod::StructuralInduction`.
//!
//! The row is now split in two, so the file measures both halves:
//!
//! * `..._a_constant_minuend_that_reduces_to_zero_plans_as_the_identity` pins
//!   the new truth AND the kernel reduction that is the reason for it,
//!   including the contrast that it is NOT the triangular function;
//! * `..._is_refused_when_no_projection_can_rescue_it` keeps the adversarial
//!   case — same constant minuend, zero arm `1`, so the function is `n + 1`
//!   and no projection can rescue it. R2's refusal stands there and carries
//!   the `is_param(minuend)` mutation sensitivity the old row was written for.
//!
//! Its message assertion was stale too, and independently: commit
//! `3362e4d2ae` (2026-08-22) moved the `-` reading into the shared
//! `read_nat_sub`, so a non-parameter minuend gets its OWN v7/D3 sentence
//! rather than the vocabulary catch-all. The `MyNat`-carrier row still lands
//! on the catch-all — `read_nat_sub` does not fire at a foreign carrier — so
//! the two boundaries remain distinguishable by message, which is what this
//! battery needs.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, EmitRefusal, FaithfulnessMethod, admit_lowering,
    plan_clean_origin_body,
};
use trust_types::admissible_body::RecBodyExpr;
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

// ───────────────────────── kernel-term helpers ─────────────────────────
// Deliberately control_8's helpers, verbatim in shape: the two files must not
// drift about what "the island's WF lowering" is.

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn lvl0() -> Level {
    Level::zero()
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

fn three_zero() -> Vec<Level> {
    vec![lvl0(), lvl0(), lvl0()]
}

fn zero() -> Expr {
    cnst("Nat.zero")
}

/// Succ-tree numeral `Nat.succ^k Nat.zero`.
fn nat_num(k: u64) -> Expr {
    let mut e = zero();
    for _ in 0..k {
        e = Expr::app(cnst("Nat.succ"), e);
    }
    e
}

/// `@OfNat.ofNat.{0} Nat k (instOfNatNat k)` — the SURFACE numeral, which is
/// what the elaborator writes for a literal.
fn surface_num(k: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![lvl0()]),
        [nat(), Expr::nat_lit(k), Expr::app(cnst("instOfNatNat"), Expr::nat_lit(k))],
    )
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.add"), [a, b])
}

fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.lt"), [a, b])
}

/// `(y : Nat) → Nat.lt y X → Nat`, with `X` seen from under `y`.
///
/// Left in the DELTA spelling on purpose: `recognise_wf_nat_rec` reads past the
/// recursive slot's type without inspecting it, so varying it here would vary
/// something the component under test does not read. Its typeclass spelling is
/// measured on the kernel side, in `r2_wf_equation_probes` w10.
fn rec_ty(x_under_y: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), Expr::arrow(nat_lt(Expr::bvar(0), x_under_y), nat()))
}

/// `fun (n : Nat) => @WellFounded.fix.{1,1} Nat (fun _ => Nat) Nat.lt Nat.lt_wf F n`
/// — the eta-expanded spelling `r2_wf_equation_probes` w1 pins.
fn wf_body(f: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("WellFounded.fix"), vec![lvl1(), lvl1()]),
            [
                nat(),
                Expr::lam(BinderInfo::Default, nat(), nat()),
                cnst("Nat.lt"),
                cnst("Nat.lt_wf"),
                f,
                Expr::bvar(0),
            ],
        ),
    )
}

/// `@Nat.le.refl 1 : Nat.le 1 1 ≡ Nat.lt 0 1` — the side condition `Nat.sub_lt`
/// needs for a decrease by one.
fn one_pos() -> Expr {
    Expr::app(cnst("Nat.le.refl"), nat_num(1))
}

/// `Nat.le.step (Nat.le.refl 1) : Nat.le 1 2 ≡ Nat.lt 0 2` — the side condition
/// for a decrease by two.
fn two_pos() -> Expr {
    Expr::apps(cnst("Nat.le.step"), [nat_num(1), nat_num(1), one_pos()])
}

/// The functional, with the guard's TWO components and both branch values open:
///
/// ```text
/// fun (x : Nat) (rec : (y : Nat) → Nat.lt y x → Nat) =>
///   @dite.{1} Nat COND DEC (fun (h : COND) => THEN) (fun (_ : Not COND) => ELSE)
/// ```
///
/// `cond`/`dec` are built in the scope `[x = bvar 1, rec = bvar 0]` — the same
/// depth as the `dite` arguments and as BOTH branch binders' types; `then_call`
/// in `[x = bvar 2, rec = bvar 1, h = bvar 0]`, `else_value` in `[x, rec, _]`.
fn wf_f(cond: Expr, dec: Expr, then_call: Expr, else_value: Expr) -> Expr {
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
                    cond.clone(),
                    dec,
                    Expr::lam(BinderInfo::Default, cond.clone(), then_call),
                    Expr::lam(BinderInfo::Default, Expr::app(cnst("Not"), cond), else_value),
                ],
            ),
        ),
    )
}

/// `Nat.add x (rec ARG PRF)` — the honest nonzero branch, in `[x, rec, h]`.
fn call_rec(arg: Expr, prf: Expr) -> Expr {
    add(Expr::bvar(2), Expr::apps(Expr::bvar(1), [arg, prf]))
}

/// `Nat.sub_lt x k h <0 < k>` — the decrease proof, in `[x, rec, h]`.
fn sub_lt(k: Expr, k_pos: Expr) -> Expr {
    Expr::apps(cnst("Nat.sub_lt"), [Expr::bvar(2), k, Expr::bvar(0), k_pos])
}

// ──────────────── the two spellings of each guard component ────────────────

/// `Nat.lt 0 x` — the delta-unfolded guard.
fn guard_delta() -> Expr {
    nat_lt(zero(), Expr::bvar(1))
}

/// `@LT.lt.{levels} <alpha> <instance> <lower> x` — the typeclass guard, with
/// every axis the recogniser pins left OPEN so a near-miss can vary exactly one.
fn guard_tc_at(levels: Vec<Level>, alpha: Expr, instance: Expr, lower: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), levels),
        [alpha, instance, lower, Expr::bvar(1)],
    )
}

/// `@LT.lt.{0} Nat instLTNat 0 x` — the prelude typeclass guard.
fn guard_tc() -> Expr {
    guard_tc_at(vec![lvl0()], nat(), cnst("instLTNat"), zero())
}

/// `Nat.decLt 0 x` — the delta-unfolded decidability instance.
fn dec_delta() -> Expr {
    Expr::apps(cnst("Nat.decLt"), [zero(), Expr::bvar(1)])
}

/// `instDecidableNatLt 0 x` — the typeclass wrapper, whose VALUE is `Nat.decLt`.
fn dec_tc() -> Expr {
    Expr::apps(cnst("instDecidableNatLt"), [zero(), Expr::bvar(1)])
}

/// `Nat.sub x 1` — the delta-unfolded decrease, in `[x, rec, h]`.
fn sub_delta() -> Expr {
    Expr::apps(cnst("Nat.sub"), [Expr::bvar(2), nat_num(1)])
}

/// `@HSub.hSub.{levels} <t1> <t2> <t3> <instance> <minuend> <subtrahend>` —
/// the typeclass decrease, with every pinned axis open.
fn hsub_at(
    levels: Vec<Level>,
    t1: Expr,
    t2: Expr,
    t3: Expr,
    instance: Expr,
    minuend: Expr,
    subtrahend: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("HSub.hSub"), levels),
        [t1, t2, t3, instance, minuend, subtrahend],
    )
}

/// `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat x 1` — the prelude spelling, in
/// `[x, rec, h]`.
fn sub_tc() -> Expr {
    hsub_at(three_zero(), nat(), nat(), nat(), cnst("instHSubNat"), Expr::bvar(2), nat_num(1))
}

// ──────────────────────── environment plumbing ────────────────────────

fn try_define(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .map_err(|refusal| format!("{refusal:?}"))
}

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    try_define(env, name, type_, value)
        .unwrap_or_else(|refusal| panic!("`{name}` must kernel-check as written: {refusal}"));
}

fn nat_to_nat() -> Expr {
    Expr::arrow(nat(), nat())
}

/// Install a `Nat -> Nat` well-founded def with the given functional, and
/// return the planner's verdict on it. Every test below goes through THIS —
/// the real production entry point — never through a hand-built double.
fn plan_of(env: &mut Environment, name: &str, f: Expr) -> Result<CleanOriginShape, EmitRefusal> {
    plan_full_of(env, name, f).map(|plan| plan.shape().clone())
}

/// [`plan_of`] keeping the WHOLE plan, so the minuend row can put the emitted
/// body through the real `admit_lowering` rather than stopping at the label.
fn plan_full_of(
    env: &mut Environment,
    name: &str,
    f: Expr,
) -> Result<CleanOriginPlan, EmitRefusal> {
    define(env, name, nat_to_nat(), wf_body(f));
    plan_clean_origin_body(env, name)
}

/// `trust_bignum::Nat` in the spelling EXTRACTION produces — `Ty::Adt`, never
/// the carrier-decision `Ty::BignumNat`. That independence is the frozen-R
/// argument (`trust_types::model`'s note on the variant), so the fixture must
/// use the extractor's spelling, exactly as `control_8` does.
fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

/// `fn f(n: Nat) -> Nat { n }` in the shape `trust_mir_extract::extract_function`
/// reports it: one block, `_0 = move _1`, `return`. This is the `OperandCopy`
/// skeleton `materialize::body_template` builds for BOTH projection rungs —
/// `Projection` and `InductiveProjection` share one row, one template and one
/// emitted body (`materialize.rs`'s `MirShape::OperandCopy` arm).
///
/// Hand-built rather than taken from the template, on `control_3`'s stated
/// discipline: side B must not be produced by the same code the assertion is
/// about.
fn emitted_unary_projection(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("crate::m::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: (0..2).map(|index| LocalDecl { index, ty: nat_adt(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
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

/// The shape `countdownSum` must read to, in the vocabulary both sides use.
fn countdown_shape() -> CleanOriginShape {
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

/// The premise every row rests on: the typeclass names are in the PRODUCTION
/// prelude this crate links. Asserted rather than assumed, the `w0` discipline.
fn assert_prelude_carries_the_typeclass_spelling(env: &Environment) {
    for name in [
        "LT",
        "LT.mk",
        "LT.lt",
        "instLTNat",
        "instDecidableNatLt",
        "Nat.decLt",
        "HSub",
        "HSub.mk",
        "HSub.hSub",
        "instHSubNat",
        "Nat.sub",
        "Nat.sub_lt",
        "Decidable",
        "OfNat.ofNat",
        "instOfNatNat",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the emittable WF fragment's typeclass spelling rests on `{name}`, and \
             `with_prelude` does not carry it — every verdict below would be about a \
             different environment than the compiler's"
        );
    }
}

// ═══════════════ THE ADMIT — the spelling the elaborator mints ═══════════════

/// **The elaborator's spelling plans, and plans to the SAME shape as the
/// hand-built one.** This is the fix, observed at the production entry point.
///
/// Three independent mutations turn this red, one per widened position: revert
/// `is_zero_lt_param` to `Nat.lt`-only, revert the decidability arm to
/// `Nat.decLt`-only, or revert `read_wf_value` to its two predecessor
/// spellings. Any one of them makes `cdsTypeclass` refuse.
///
/// The paired control is the last assertion: a wrong ELSE branch in the SAME
/// typeclass spelling must plan to a DIFFERENT shape, so the shape comparison
/// above it is a decision rather than a tautology.
#[test]
fn control_11_the_full_elaborator_spelling_plans_to_the_same_shape() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let honest_step = || call_rec(sub_delta(), sub_lt(nat_num(1), one_pos()));
    let delta =
        plan_of(&mut env, "cdsDelta", wf_f(guard_delta(), dec_delta(), honest_step(), zero()))
            .expect("the hand-built delta-unfolded side A must plan");
    assert_eq!(delta, countdown_shape());

    let typeclass_step = || call_rec(sub_tc(), sub_lt(nat_num(1), one_pos()));
    let typeclass =
        plan_of(&mut env, "cdsTypeclass", wf_f(guard_tc(), dec_tc(), typeclass_step(), zero()))
            .unwrap_or_else(|refusal| {
                panic!(
                    "THE MEASURED DEFECT, IF THIS FIRES: the recogniser refuses the spelling the \
             elaborator actually mints for `if h : 0 < n then n + f (n - 1) else 0` — the \
             exact surface text its own refusal advertises as the emittable fragment. \
             Widen `emit.rs`, never this control. got: {}",
                    refusal.note()
                )
            });
    assert_eq!(
        typeclass, delta,
        "both spellings of ONE function must read to ONE shape; a recogniser that reads \
         them differently has invented a distinction the kernel does not make"
    );

    // The two side-A bodies really are one function, so the shape agreement is
    // not two different denotations wearing one label.
    let tc = TypeChecker::new(&env);
    let at_four = |name: &str| Expr::app(cnst(name), nat_num(4));
    assert!(
        tc.is_def_eq(&at_four("cdsDelta"), &at_four("cdsTypeclass")),
        "MEASURED: the two spellings compute the same value — the widening admitted a \
         δ-alias, not a second function"
    );
    drop(tc);

    // CONTROL: the shape comparison is a DECISION.
    let wrong_else = plan_of(
        &mut env,
        "cdsTypeclassWrongElse",
        wf_f(guard_tc(), dec_tc(), typeclass_step(), nat_num(1)),
    )
    .expect("the wrong-else sibling is still inside the fragment");
    assert_ne!(
        wrong_else, delta,
        "CONTROL: if a wrong else-branch reads to the same shape, the equality above is \
         comparing nothing"
    );
}

/// The SURFACE numeral, split out from the row above so a change in how `Nat`
/// literals elaborate cannot take the main admit down with it: the elaborator
/// writes the subtrahend `1` as `@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)`, and
/// the recogniser's numeral reader must see that as the literal 1.
///
/// Failing mutation: drop the `OfNat.ofNat` arm from `read_nat_numeral`, or
/// narrow it to reject the surface instance. The row then refuses with the
/// decrease-by-one boundary.
#[test]
fn control_11_the_surface_numeral_subtrahend_plans() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let surface_sub = hsub_at(
        three_zero(),
        nat(),
        nat(),
        nat(),
        cnst("instHSubNat"),
        Expr::bvar(2),
        surface_num(1),
    );
    let surface_one_pos = Expr::app(cnst("Nat.le.refl"), surface_num(1));
    let surface_step = call_rec(surface_sub, sub_lt(surface_num(1), surface_one_pos));
    let shape =
        plan_of(&mut env, "cdsSurfaceNumeral", wf_f(guard_tc(), dec_tc(), surface_step, zero()))
            .unwrap_or_else(|refusal| {
                panic!(
                    "the recogniser must read the SURFACE numeral the elaborator writes for `1`; \
             if the kernel refused the declaration instead, `OfNat.ofNat Nat 1 \
             (instOfNatNat 1)` is not the `Nat` this fixture assumes and \
             `r2_wf_equation_probes` w10's numeral row is where to re-measure. got: {}",
                    refusal.note()
                )
            });
    assert_eq!(shape, countdown_shape());
}

// ═════════════ THE NEAR-MISSES — one planted violation per check ═════════════

/// A FOREIGN `LT Nat` instance must be refused, even though the kernel cannot
/// tell it from the prelude one.
///
/// `foreignLtNat` is the ETA-EXPANDED twin of `instLTNat`'s own value, so it is
/// DEFEQ to it: typing accepts the whole declaration and the guard denotes
/// exactly `Nat.lt 0 x`. Only the BY-NAME discipline refuses it, which is the
/// point — a widening that read "any `LT` at `Nat`" would also admit
/// `Classical.Order.instLT Nat instLENat`, whose unfolding is `0 ≤ n ∧ ¬ n ≤ 0`
/// and which the elaborator was measured resolving to under `import Init`.
///
/// Failing mutation: delete the `instLTNat` name test from `is_zero_lt_param`.
/// The guard then passes, the `Nat.decLt` instance passes, and the body plans —
/// so `expect_err` fires.
#[test]
fn control_11_a_foreign_lt_instance_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let eta_nat_lt = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), nat_lt(Expr::bvar(1), Expr::bvar(0))),
    );
    define(
        &mut env,
        "foreignLtNat",
        Expr::app(Expr::const_(Name::from_string("LT"), vec![lvl0()]), nat()),
        Expr::apps(Expr::const_(Name::from_string("LT.mk"), vec![lvl0()]), [nat(), eta_nat_lt]),
    );

    let refusal = plan_of(
        &mut env,
        "cdsForeignLt",
        wf_f(
            guard_tc_at(vec![lvl0()], nat(), cnst("foreignLtNat"), zero()),
            // The DELTA decidability instance: `Decidable (Nat.lt 0 x)` is defeq
            // to `Decidable (@LT.lt Nat foreignLtNat 0 x)`, so the near-miss is
            // a real kernel-checked declaration and the refusal is a decision.
            dec_delta(),
            call_rec(sub_delta(), sub_lt(nat_num(1), one_pos())),
            zero(),
        ),
    )
    .expect_err("a guard through a NON-prelude `LT Nat` instance is outside the fragment");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is a capability refusal");
    // RECONCILED 2026-08-26 against the CURRENT `emit.rs`: the guard refusal is
    // now `format!("{}. The emitted body's zero test decides exactly `0 < n` on
    // the recursion's own MEASURE parameter, …", wf_guard_hint(guard, measure))`
    // — R3a made "the parameter" ambiguous, so the text names which one — and
    // `wf_guard_hint`'s `LT.lt` fall-through names the INSTANCE by name. Both
    // halves are asserted — the envelope says WHICH check refused, the hint says
    // which boundary inside it.
    assert!(
        refusal
            .note()
            .contains("zero test decides exactly `0 < n` on the recursion's own measure parameter"),
        "the refusal must be the GUARD refusal — if it names another boundary, a different \
         check is doing this work and this test is no longer sensitive to the instance \
         read. got: {}",
        refusal.note()
    );
    assert!(
        refusal
            .note()
            .contains("through an ordering instance other than the prelude's `instLTNat`"),
        "the guard refusal must name the ORDERING-INSTANCE boundary specifically; got: {}",
        refusal.note()
    );
}

/// A non-`Nat` type argument in the typeclass guard must be refused.
///
/// `MyNat` is a reducible alias of `Nat`, so `@LT.lt.{0} MyNat instLTNat 0 x`
/// TYPE-CHECKS (the instance slot wants `LT MyNat`, which δ-reduces to
/// `LT Nat`) and denotes the same proposition. The recogniser still refuses,
/// because it reads the carrier syntactically: a type argument it has not
/// measured is an order it has not measured.
///
/// Failing mutation: delete the `is_nat_const_expr(alpha)` test from
/// `is_zero_lt_param`'s `LT.lt` branch. The guard then passes and the body
/// plans, so `expect_err` fires.
///
/// WHAT THIS ROW CANNOT DO, said rather than smoothed over. `wf_guard_hint`'s
/// `LT.lt` arm reaches its final sentence — the one naming `instLTNat` — for
/// BOTH a foreign instance and a foreign carrier, because it inspects the
/// operands and then falls through. So this row's message is byte-identical to
/// the foreign-instance row's, and the assertion below can only witness that the
/// GUARD refused, not that the CARRIER check is what refused. Its sensitivity
/// comes from the planted violation flipping REFUSE to ADMIT, which `expect_err`
/// catches; it does not come from message discrimination. Making the hint name
/// the carrier is an `emit.rs` change and would strengthen this row — it is not
/// this file's to make.
#[test]
fn control_11_a_non_nat_carrier_in_the_guard_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);
    define(&mut env, "MyNat", Expr::sort(lvl1()), nat());

    let refusal = plan_of(
        &mut env,
        "cdsAliasCarrierGuard",
        wf_f(
            guard_tc_at(vec![lvl0()], cnst("MyNat"), cnst("instLTNat"), zero()),
            dec_delta(),
            call_rec(sub_delta(), sub_lt(nat_num(1), one_pos())),
            zero(),
        ),
    )
    .expect_err("a guard at a type argument other than the bare `Nat` is outside the fragment");
    assert!(
        refusal
            .note()
            .contains("zero test decides exactly `0 < n` on the recursion's own measure parameter"),
        "the refusal must be the GUARD refusal; got: {}",
        refusal.note()
    );
}

/// A NON-ZERO lower bound must be refused: the emitted body's zero test decides
/// `0 < n` and nothing else.
///
/// The near-miss is a real recursion — `if h : 1 < n then n + f 1 else 0` — and
/// it kernel-checks, because `h : Nat.lt 1 x` is exactly the proof the slot
/// `rec 1 _` wants (`Nat.lt 1 x ≡ Nat.le 2 x` on both sides).
///
/// Failing mutation: relax `is_zero_lt_param`'s
/// `read_wf_numeral(lower) == Some(NatReading::Fits(0))` to accept any numeral.
/// The guard then passes, the DECIDABILITY read refuses instead (its own lower
/// bound is still pinned at 0), and the refusal text changes — which is exactly
/// what the assertion below catches. Asserting the boundary TEXT rather than
/// "some refusal" is what keeps this test sensitive to one mutation.
#[test]
fn control_11_a_non_zero_lower_bound_in_the_guard_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let one_lt_x = guard_tc_at(vec![lvl0()], nat(), cnst("instLTNat"), nat_num(1));
    let refusal = plan_of(
        &mut env,
        "cdsLowerBoundOne",
        wf_f(
            one_lt_x,
            Expr::apps(cnst("instDecidableNatLt"), [nat_num(1), Expr::bvar(1)]),
            // `rec 1 h` — the recursion the guard actually licenses.
            call_rec(nat_num(1), Expr::bvar(0)),
            zero(),
        ),
    )
    .expect_err("a guard at a non-zero lower bound is outside the fragment");
    // RECONCILED 2026-08-24: `wf_guard_hint` now distinguishes "the bound is not
    // 0" from "the bound is spelled in a way this lane does not read", and
    // `nat_num(1)` IS read (`describe_unread_nat_spelling` returns `None` for a
    // numeral it could read), so this near-miss lands on the bound sentence and
    // on no other. That is the discrimination this row needs: relaxing the
    // decidability read instead leaves a DIFFERENT message and this fires.
    assert!(
        refusal.note().contains("tests the parameter against a bound other than `0`"),
        "the refusal must name the LOWER-BOUND boundary; got: {}",
        refusal.note()
    );
}

/// A FOREIGN decidability instance must be refused, even when its value is
/// literally `Nat.decLt`.
///
/// `foreignDecNatLt` is declared at the typeclass goal shape and DEFINED as the
/// bare `Nat.decLt`, so the declaration kernel-checks and the instance decides
/// the very proposition the emitted `Nat::is_zero` realises. It is still
/// refused: the two admitted names are the two the lane MEASURED, and a third
/// name is a third thing to measure.
///
/// Failing mutation: relax `dec_name_ok` to accept any constant head. The body
/// then plans.
#[test]
fn control_11_a_foreign_decidability_instance_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    // `(a b : Nat) → Decidable (@LT.lt.{0} Nat instLTNat a b) := Nat.decLt`
    let dec_goal = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            nat(),
            Expr::app(
                cnst("Decidable"),
                Expr::apps(
                    Expr::const_(Name::from_string("LT.lt"), vec![lvl0()]),
                    [nat(), cnst("instLTNat"), Expr::bvar(1), Expr::bvar(0)],
                ),
            ),
        ),
    );
    define(&mut env, "foreignDecNatLt", dec_goal, cnst("Nat.decLt"));

    let refusal = plan_of(
        &mut env,
        "cdsForeignDec",
        wf_f(
            guard_tc(),
            Expr::apps(cnst("foreignDecNatLt"), [zero(), Expr::bvar(1)]),
            call_rec(sub_delta(), sub_lt(nat_num(1), one_pos())),
            zero(),
        ),
    )
    .expect_err("a third decidability-instance name is outside the measured fragment");
    assert!(
        // RECONCILED 2026-08-24: the message interpolates the observed head
        // between "instance is" and "not the prelude's", so the assertion must
        // start after the `{}` slot.
        refusal.note().contains("not the prelude's `0 < n` decision"),
        "the refusal must name the DECIDABILITY-INSTANCE boundary; got: {}",
        refusal.note()
    );
}

/// A FOREIGN `HSub Nat Nat Nat` instance must be refused, even though it is
/// defeq to the prelude one.
///
/// `predHSubNat`'s operation is `fun a _ => Nat.pred a`, so
/// `@HSub.hSub … predHSubNat x 1` reduces to `Nat.pred x`, which
/// `r2_wf_equation_probes` w6/b′ measured defeq to `Nat.sub x 1` — the decrease
/// proof therefore type-checks in the slot and the whole declaration is a real
/// kernel verdict. Typing cannot separate this from the prelude instance; only
/// the by-name read can, and it must, because the emitted `Nat::sub(&n, &1)`
/// realises `Nat.sub` and nothing else.
///
/// Failing mutation: delete the `instHSubNat` name test from `read_wf_value`'s
/// `HSub.hSub` arm. The arm then reads the decrease as `Pred` and the body
/// plans.
#[test]
fn control_11_a_foreign_hsub_instance_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let pred_op = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("Nat.pred"), Expr::bvar(1))),
    );
    define(
        &mut env,
        "predHSubNat",
        Expr::apps(Expr::const_(Name::from_string("HSub"), three_zero()), [nat(), nat(), nat()]),
        Expr::apps(
            Expr::const_(Name::from_string("HSub.mk"), three_zero()),
            [nat(), nat(), nat(), pred_op],
        ),
    );

    let foreign_sub =
        hsub_at(three_zero(), nat(), nat(), nat(), cnst("predHSubNat"), Expr::bvar(2), nat_num(1));
    let refusal = plan_of(
        &mut env,
        "cdsForeignHSub",
        wf_f(guard_tc(), dec_tc(), call_rec(foreign_sub, sub_lt(nat_num(1), one_pos())), zero()),
    )
    .expect_err("a decrease through a NON-prelude `HSub Nat` instance is outside the fragment");
    assert!(
        // RECONCILED 2026-08-24 against the CURRENT `read_wf_value` HSub arm,
        // whose text is "its `-` at `Nat` routes through an instance other than
        // the prelude's `instHSubNat`". The distinguishing half — "routes through
        // an instance other than the prelude's" — is what separates this row from
        // the generic vocabulary refusal the non-`Nat`-carrier row lands on.
        refusal
            .note()
            .contains("at `Nat` routes through an instance other than the prelude's `instHSubNat`"),
        "the refusal must name the HSUB-INSTANCE boundary — if it names the generic \
         vocabulary boundary instead, the arm did not fire and this test is measuring \
         something else. got: {}",
        refusal.note()
    );
}

/// A non-`Nat` type argument in the typeclass subtraction must be refused.
///
/// Same `MyNat` alias trick as the guard row: `@HSub.hSub.{0,0,0} MyNat MyNat
/// MyNat instHSubNat x 1` type-checks (the instance slot wants
/// `HSub MyNat MyNat MyNat`, which δ-reduces to `HSub Nat Nat Nat`) and denotes
/// `Nat.sub x 1`. The arm does not fire, so the body falls to the generic
/// vocabulary refusal — which is the fail-closed answer.
///
/// Failing mutation: delete the three `is_nat_const_expr` tests from the
/// `HSub.hSub` arm's guard condition. The arm then fires, the prelude instance
/// name passes, and the body plans.
#[test]
fn control_11_a_non_nat_carrier_in_the_subtraction_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);
    define(&mut env, "MyNat", Expr::sort(lvl1()), nat());

    let alias_sub = hsub_at(
        three_zero(),
        cnst("MyNat"),
        cnst("MyNat"),
        cnst("MyNat"),
        cnst("instHSubNat"),
        Expr::bvar(2),
        nat_num(1),
    );
    let refusal = plan_of(
        &mut env,
        "cdsAliasCarrierSub",
        wf_f(guard_tc(), dec_tc(), call_rec(alias_sub, sub_lt(nat_num(1), one_pos())), zero()),
    )
    .expect_err("a decrease at a carrier other than the bare `Nat` is outside the fragment");
    assert!(
        refusal.note().contains("outside this fragment's vocabulary"),
        "the refusal must be the fail-closed vocabulary boundary; got: {}",
        refusal.note()
    );
}

/// `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat 1 1` — the CONSTANT minuend, in
/// `[x, rec, h]`. `h : Nat.lt 0 x` is exactly the proof `rec (1 - 1) _` wants,
/// because `Nat.lt (1 - 1) x` reduces to `Nat.lt 0 x`.
fn const_minuend_sub() -> Expr {
    hsub_at(three_zero(), nat(), nat(), nat(), cnst("instHSubNat"), nat_num(1), nat_num(1))
}

/// **A minuend that is not the recursion's own parameter is refused BY R2 —
/// and where the whole function is nonetheless provably a projection, the
/// INDUCTIVE-PROJECTION lane plans it, faithfully.**
///
/// # WHAT CHANGED HERE, 2026-08-25, and the evidence for it
///
/// Until today this row asserted that `plan_clean_origin_body` REFUSES
/// `if h : 0 < n then n + f (1 - 1) else 0`, with a note containing *"outside
/// this fragment's vocabulary"*. **Both halves of that assertion were stale on
/// the day this file landed** (2026-08-24), for two INDEPENDENT reasons, each
/// measured rather than argued:
///
/// 1. **The message moved, and improved.** Commit `3362e4d2ae` (2026-08-22)
///    routed the `-` reading through the shared `read_nat_sub`, so a
///    non-parameter minuend no longer falls through to the vocabulary
///    catch-all: it gets its OWN refusal — *"its self-call argument subtracts
///    from something other than the recursion's own parameter"* — which names
///    the boundary instead of listing the vocabulary. That is the v7/D3
///    direction, and the sibling row below pins the new text.
///
/// 2. **The verdict changed, because the DENOTATION was never what the old
///    prose said.** `1 - 1` is `0` under `Nat.sub` (kernel: `is_def_eq` TRUE,
///    asserted below), so this declaration computes `f 0 = 0` and, for
///    `n > 0`, `f n = n + f 0 = n`. **It DENOTES the identity.** Measured at
///    the kernel, `cdsConstMinuend k` is `is_def_eq` to `k` for every
///    `k ∈ 0..=4`, and is NOT `is_def_eq` to `3`/`6`/`10` at `2`/`3`/`4` —
///    i.e. it is not the triangular function. R2's boundary is therefore
///    RIGHT to refuse `rec_arg: Pred`, which WOULD be triangular and WOULD be
///    a wrong binary; the old prose's conclusion ("a WRONG BINARY, not a
///    missed capability") was correct about `Pred` and wrong about the body.
///    The inductive-projection fallback then proves the whole function equal
///    to parameter 0 by a kernel-checked, axiom-audited structural induction,
///    and the plan is `InductiveProjection { projected: 0 }` — a different
///    claim from the one R2 refused, on a different lane, re-earned by the
///    gate below.
///
/// **The refusal did not stop firing. A second lane proved something the first
/// lane never claimed**, and the emitted `_0 = move _1` is exactly what side A
/// denotes. That is why this row now pins the plan AND puts it through the real
/// `admit_lowering`: a plan that promised what the gate refuses would be a
/// planner defect even though it is fail-closed, and the `StructuralInduction`
/// verdict asserted below is what rules that out.
///
/// HONESTY RULE pairing: the ADMIT here is paired with
/// `control_11_a_minuend_that_is_not_the_parameter_is_refused_when_no_projection_can_rescue_it`,
/// which is the SAME constant minuend with a zero arm no projection can match —
/// the R2 refusal stands there, and that row carries the mutation sensitivity
/// this one used to carry. WHAT THIS ROW CANNOT DO: at arity 1 there is no
/// second parameter, so it cannot inject a wrong-projection emitter mutation;
/// that mutation is `control_3::half_2`'s, on a two-parameter definition.
#[test]
fn control_11_a_constant_minuend_that_reduces_to_zero_plans_as_the_identity() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let plan = plan_full_of(
        &mut env,
        "cdsConstMinuend",
        wf_f(guard_delta(), dec_delta(), call_rec(const_minuend_sub(), Expr::bvar(0)), zero()),
    )
    .unwrap_or_else(|refusal| {
        panic!(
            "R2 refuses this body — correctly, it does not descend on `n` — but the \
             inductive-projection fallback proves it equal to parameter 0 and the plan \
             stands. If this now refuses, the FALLBACK regressed, not the boundary. got: {}",
            refusal.note()
        )
    });
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::InductiveProjection { projected: 0 },
        "the second lane's verdict is a PROJECTION, never `rec_arg: Pred` — reading this \
         body as a decrease by one would emit the triangular function, which the kernel \
         evidence below shows it is not"
    );

    // ── THE KERNEL EVIDENCE, in this file, so the claim above is measured ──
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&const_minuend_sub(), &nat_num(0)),
        "MEASURED PREMISE: `1 - 1` must BE `0` at the kernel; if it is not, this whole row \
         is about a different term"
    );
    let at = |k: u64| Expr::app(cnst("cdsConstMinuend"), nat_num(k));
    for k in 0..=4u64 {
        assert!(
            tc.is_def_eq(&at(k), &nat_num(k)),
            "MEASURED: `cdsConstMinuend {k}` must reduce to `{k}` — the projection plan is \
             faithful only if the declaration denotes the identity"
        );
    }
    // …and the CONTRAST that makes the row a decision: it is NOT the function a
    // `Pred` reading would emit (`f n = n + f (n-1)`, the triangular numbers).
    for (k, triangular) in [(2u64, 3u64), (3, 6), (4, 10)] {
        assert!(
            !tc.is_def_eq(&at(k), &nat_num(triangular)),
            "CONTROL: `cdsConstMinuend {k}` must NOT be `{triangular}`. If it were, the R2 \
             boundary would be refusing a body it should read as `Pred`, and the identity \
             claim above would be false"
        );
    }
    drop(tc);

    // ── THE GATE, end to end: a plan is not permission to emit ──
    let admitted = admit_lowering(&env, &plan, &emitted_unary_projection("cdsConstMinuend"))
        .unwrap_or_else(|refusal| {
            panic!(
                "PLANNER DEFECT IF THIS FIRES: the planner promised a projection the gate \
                 then refuses. Fail-closed, but a plan must not promise what the gate will \
                 reject — fix `emit.rs`, not this assertion. got: {refusal:?}"
            )
        });
    assert_eq!(
        admitted.method(),
        FaithfulnessMethod::StructuralInduction,
        "the WHOLE-TERM `WellFounded.fix` is STUCK under reduction (`Nat.lt_wf` is a proof, \
         so `Acc.rec` has no constructor to fire on at an open `n`), so the only honest \
         route to this verdict is the real induction proof the gate re-checks and audits. \
         A `DefinitionalEquality` here would mean the gate stopped comparing what it says \
         it compares"
    );
}

/// **The paired refusal: the SAME constant minuend, refused, where no
/// projection can rescue it.** This is the row that carries the mutation
/// sensitivity, and it exists because the row above admits.
///
/// The only change from `cdsConstMinuend` is the zero arm, `1` instead of `0`.
/// The body still recurses at the constant `1 - 1`, so R2's minuend check is
/// hit identically — but now `f 0 = 1` and `f n = n + 1`, which is no
/// parameter of anything, so the inductive-projection fallback is TRIED and
/// FAILS and the original R2 refusal is what the caller gets. That the fallback
/// does not rescue an arbitrary body is itself the measurement here.
///
/// Failing mutation: replace the `HSub.hSub`/`read_nat_sub` arm's
/// `is_param(minuend)` test with `true`. The body then plans as
/// `WellFoundedNatRec { zero_value: NatConst(1), …, rec_arg: Pred }`, which
/// denotes `1, 2, 4, 7, …` for a declaration that computes `1, 2, 3, 4, …` —
/// a WRONG BINARY — and `expect_err` fires.
#[test]
fn control_11_a_minuend_that_is_not_the_parameter_is_refused_when_no_projection_can_rescue_it() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let refusal = plan_of(
        &mut env,
        "cdsConstMinuendOffset",
        wf_f(guard_delta(), dec_delta(), call_rec(const_minuend_sub(), Expr::bvar(0)), nat_num(1)),
    )
    .expect_err(
        "a self-call at a constant argument is outside R2's fragment, and `fun n => n + 1` \
         is not a projection, so nothing rescues it",
    );
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is a capability refusal");
    // RECONCILED 2026-08-25 against the CURRENT `read_wf_value`: since
    // `3362e4d2ae` the non-parameter minuend has its OWN sentence rather than
    // falling through to the vocabulary catch-all.
    //
    // RECONCILED AGAIN 2026-08-27 (R3b), and this time the LAYER moved, not
    // just the sentence. `read_wf_value` no longer refuses a non-parameter
    // minuend at all — it reads `1 - 1` as an ordinary `Sub(1, 1)`, because a
    // general truncated `-` is what subtractive Euclid's step map is written
    // in. What refuses this body now is the fragment belt
    // `rec_args[measure_index] != Pred`, one layer later.
    //
    // THE MUTATION SENSITIVITY IS UNCHANGED, which is the only reason this
    // reconciliation is legitimate. The failing mutation named above —
    // replacing the `Pred` canonicalisation's `is_param(minuend)` test with
    // `true` — still makes `1 - 1` read as `Pred`, still plans the triangular
    // function, and still fails the `expect_err` above. What this row now pins
    // is the belt rather than the reader, i.e. the layer that is actually
    // load-bearing after R3b; and it gained a second sensitivity for free,
    // since deleting the belt fails it too.
    assert!(
        refusal.note().contains("DECREASING argument is not `n - 1`"),
        "the refusal must name the DECREASE-BY-ONE boundary at the SELF-CALL's decreasing \
         argument — if it names the generic vocabulary boundary instead, neither the `-` \
         reader nor the belt fired and this test is measuring something else. got: {}",
        refusal.note()
    );
    assert!(
        refusal.note().contains("self-call"),
        "…and must place the boundary at the SELF-CALL, not at a branch value; got: {}",
        refusal.note()
    );
    // The general `-` really did become readable — otherwise the paragraph
    // above is a story rather than a description. Same decrease (`x - 1`, so
    // the belt is satisfied) but a ZERO ARM that subtracts from something that
    // is not the parameter: before R3b that arm was a refusal, and it is now
    // ordinary arithmetic.
    let general = plan_of(
        &mut Environment::with_prelude(),
        "cdsGeneralSub",
        wf_f(
            guard_delta(),
            dec_delta(),
            call_rec(sub_delta(), sub_lt(nat_num(1), one_pos())),
            const_minuend_sub(),
        ),
    )
    .unwrap_or_else(|refusal| {
        panic!(
            "R3b reads a general truncated `-`; if this refuses, the widening did not land \
             and the reconciliation above is describing code that does not exist. got: {}",
            refusal.note()
        )
    });
    assert_eq!(
        general,
        CleanOriginShape::WellFoundedNatRec {
            zero_value: RecBodyExpr::Sub(
                Box::new(RecBodyExpr::NatConst(1)),
                Box::new(RecBodyExpr::NatConst(1)),
            ),
            nonzero_value: RecBodyExpr::Add(
                Box::new(RecBodyExpr::Decreasing),
                Box::new(RecBodyExpr::Rec),
            ),
            rec_args: vec![RecBodyExpr::Pred],
            measure_index: 0,
            lowering: trust_clean_origin::WfLowering::OnParameter,
        },
        "…and it must read as `Sub`, NOT be pre-reduced to `0` by the reader: the value of \
         `1 - 1` is the KERNEL's decision at the gate, never this reader's"
    );

    // The declaration really is `fun n => n + 1`, so the fallback's failure is a
    // DECISION about this body and not a timeout or a rail.
    let tc = TypeChecker::new(&env);
    for k in 0..=3u64 {
        let at_k = Expr::app(cnst("cdsConstMinuendOffset"), nat_num(k));
        assert!(
            tc.is_def_eq(&at_k, &nat_num(k + 1)),
            "MEASURED: `cdsConstMinuendOffset {k}` must reduce to `{}` — if it were `{k}` \
             this would be a projection after all and the refusal would be a capability \
             loss rather than a boundary",
            k + 1
        );
        assert!(
            !tc.is_def_eq(&at_k, &nat_num(k)),
            "CONTROL: it must NOT be the identity, or the projection lane would have \
             rescued it and this row would measure nothing"
        );
    }
}

/// A subtrahend other than the literal `1` must be refused.
///
/// `x - 2` with `Nat.sub_lt x 2 h 0<2` is well-typed, genuinely decreasing and
/// terminating — probe w7/d3's shape — so nothing but the numeral read stands
/// between it and an emitted `Nat::sub(&n, &1)` that computes a different
/// function.
///
/// Failing mutation: widen the `Pred` canonicalisation's `subtrahend_is_one`
/// test to accept any numeral. `x - 2` then reads as `Pred`, the belt below
/// sees the predecessor it wants, and the body plans as a decrease by one.
///
/// R3b MOVED THE LAYER, not the property. `read_wf_value` now reads `x - 2` as
/// an ordinary `Sub(Decreasing, 2)` instead of refusing it, and the refusal
/// comes from `check_wf_fragment`'s `rec_args[measure_index] != Pred`. The
/// mutation above is still exactly what this row is sensitive to, and deleting
/// the belt now fails it too — one row, two guards.
#[test]
fn control_11_a_subtrahend_other_than_one_is_refused() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let two_back =
        hsub_at(three_zero(), nat(), nat(), nat(), cnst("instHSubNat"), Expr::bvar(2), nat_num(2));
    let refusal = plan_of(
        &mut env,
        "cdsTwoBack",
        wf_f(guard_tc(), dec_tc(), call_rec(two_back, sub_lt(nat_num(2), two_pos())), zero()),
    )
    .expect_err("a decrease by two is outside the fragment");
    assert!(
        refusal.note().contains("DECREASING argument is not `n - 1`"),
        "the refusal must name the DECREASE-BY-ONE boundary — if it names the vocabulary \
         boundary instead, the `HSub.hSub` arm did not fire and this test is measuring \
         something else. got: {}",
        refusal.note()
    );
    // …and it must be a CAPABILITY refusal, not a compiler defect: `x - 2` is
    // a perfectly good definition that this compiler cannot emit yet.
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is a capability refusal");
}

// ══════════ THE UNIVERSE-LEVEL AXIS — a PREMISE pin, not a recogniser pin ══════════

/// **HONEST ROW.** The recogniser pins `LT.lt` at exactly one zero level and
/// `HSub.hSub` at exactly three, and neither pin is reachable from a
/// kernel-checked declaration: `LT.{u} : Type u → Type u` and
/// `HSub.{u,v,w} : Type u → Type v → Type w → Type _`, so over `Nat : Type 0`
/// any other level list simply does not TYPE — and `plan_clean_origin_body`
/// only ever sees bodies that entered through a full kernel check
/// (`declaration_verification`, its first act).
///
/// So this test does NOT exercise the recogniser, and pretending otherwise
/// would be the "test that cannot fail" this battery exists to avoid. It pins
/// the PREMISE that makes those two checks belt-and-braces: each ill-levelled
/// spelling is refused by the kernel, and the same body at the correct levels
/// is ACCEPTED — the pairing is what makes each refusal attributable to the
/// level list rather than to a malformed fixture.
///
/// Failing mutation: any prelude change that makes one of these spellings type
/// (a differently-parameterised `LT`/`HSub`, or kernel cumulativity at `Sort`).
/// That is exactly the moment the recogniser's level pins stop being redundant
/// and start being load-bearing, and the moment someone needs to be told.
#[test]
fn control_11_universe_level_near_misses_never_kernel_check() {
    let mut env = Environment::with_prelude();
    assert_prelude_carries_the_typeclass_spelling(&env);

    let honest_then = |sub: Expr| call_rec(sub, sub_lt(nat_num(1), one_pos()));

    // ── the guard's level list ──
    let guard_body = |levels: Vec<Level>| {
        wf_body(wf_f(
            guard_tc_at(levels, nat(), cnst("instLTNat"), zero()),
            dec_delta(),
            honest_then(sub_delta()),
            zero(),
        ))
    };
    try_define(&mut env, "lvlGuardOk", nat_to_nat(), guard_body(vec![lvl0()])).expect(
        "POSITIVE CONTROL: the guard at ONE zero level is the spelling that types — if \
         this fails, every refusal below is about a malformed fixture, not about levels",
    );
    for (name, levels) in [
        ("lvlGuardNone", Vec::new()),
        ("lvlGuardTwo", vec![lvl0(), lvl0()]),
        ("lvlGuardOne", vec![lvl1()]),
    ] {
        assert!(
            try_define(&mut env, name, nat_to_nat(), guard_body(levels)).is_err(),
            "`LT.lt` at the wrong level list must be refused BY THE KERNEL ({name}); it \
             was accepted, so the recogniser's level pin is now load-bearing and needs a \
             real planted-violation row of its own"
        );
    }

    // ── the subtraction's level list ──
    let sub_body = |levels: Vec<Level>| {
        wf_body(wf_f(
            guard_delta(),
            dec_delta(),
            honest_then(hsub_at(
                levels,
                nat(),
                nat(),
                nat(),
                cnst("instHSubNat"),
                Expr::bvar(2),
                nat_num(1),
            )),
            zero(),
        ))
    };
    try_define(&mut env, "lvlSubOk", nat_to_nat(), sub_body(three_zero())).expect(
        "POSITIVE CONTROL: the subtraction at THREE zero levels is the spelling that \
         types",
    );
    for (name, levels) in [
        ("lvlSubTwo", vec![lvl0(), lvl0()]),
        ("lvlSubFour", vec![lvl0(), lvl0(), lvl0(), lvl0()]),
        ("lvlSubNonZero", vec![lvl0(), lvl0(), lvl1()]),
    ] {
        assert!(
            try_define(&mut env, name, nat_to_nat(), sub_body(levels)).is_err(),
            "`HSub.hSub` at the wrong level list must be refused BY THE KERNEL ({name}); \
             it was accepted, so the recogniser's level pin is now load-bearing and needs \
             a real planted-violation row of its own"
        );
    }

    // …and the two POSITIVE controls really are inside the fragment, so the
    // pairing above compares a plannable body against an unbuildable one.
    for name in ["lvlGuardOk", "lvlSubOk"] {
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|refusal| panic!("`{name}` must plan: {}", refusal.note()));
        assert_eq!(plan.shape(), &countdown_shape());
    }
}
