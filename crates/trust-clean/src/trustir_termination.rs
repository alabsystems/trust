// trust-clean/trustir_termination.rs — LOOP RANKING/TERMINATION theory ported onto the
// trust-ir denotation (Lane T of the MirSem teardown toward "Clean kernel as sole trust
// root").
//
// WHY THIS EXISTS.
// `trustir_anchor.rs` relocated the loop PARTIAL-correctness theory (the Hoare while-rule
// `Trust.TrustIr.loopInvariantRule`, its `Brk`/`O`/`S` variants, the per-function instances
// and the postcondition discharges) off the bespoke `Trust.MirSem` model onto the Clean
// denotation keyed to trust-ir's universal IR syntax. TERMINATION did not move: the §6
// via-trustir gates either carried no termination clause at all (the single-loop path rode
// the MirSem outer gate) or called `crate::mirsem::loop_total_correct_witness` IN-PATH (the
// cond-update path's explicitly-commented MirSem residue). This module ports the ENTIRE
// ranking/termination meta-theory — `loopRankTerminates`, the composed `loopTotalCorrect`,
// and the pure Int/Nat rank-lemma suite they instantiate through (`loopRankDecrease`,
// `countdownRankDecrease`, `toNatMono` + its three sub-lemmas, `strideRankDecrease`) —
// onto the trust-ir denotation (`Trust.TrustIr.execLoop` / `evalCond` / `evalBody`, and the
// SELECT layer `execLoopS` / `execS`), byte-for-byte from the committed `Trust.MirSem`
// proofs, registered under `Trust.TrustIr.*` names ONLY (the trust-ir env's zero-MirSem
// separation is load-bearing: no registered decl here references any `Trust.MirSem.*`
// constant).
//
// WHAT IS REGISTERED (all kernel-checked, every decl's axiom residue EMPTY — i.e. the
// axiom closure ⊆ {propext, Quot.sound, Classical.choice}, modulo exactly 3):
//
//   * `Trust.TrustIr.natLeTrans` — raw `Nat.le` transitivity (the well-founded descent's
//     chaining lemma). Port of `Trust.MirSem.nat_le_trans`.
//   * Per LOOP LAYER (base `evalBody`/`execLoop`, and SELECT `execS`/`execLoopS`):
//       - `guardFalseStable[S]` — a false guard stays false under any remaining fuel.
//       - `boundedHalt[S]` — well-founded descent: if the rank strictly drops on every
//         guarded step, the loop halts within any fuel ≥ the start rank.
//       - `loopRankTerminates[S]` — `boundedHalt` at fuel `R e` (`Nat.le.refl`).
//       - `loopTotalCorrect[S]` — the COMPOSED total-correctness theorem: `And.intro` of
//         `loopInvariantRule[S]` (partial: invariant at the halting state) and
//         `loopRankTerminates[S]` (termination) at the SHARED fuel `R e`.
//     Ports of `Trust.MirSem.{guardFalseStable, boundedHalt, loopRankTerminates,
//     loopTotalCorrect}` with `eval_cond ↦ evalCond`, `exec ↦ evalBody | execS`,
//     `exec_loop ↦ execLoop | execLoopS`.
//   * The DENOTATION-INDEPENDENT pure Int/Nat rank-lemma suite — `loopRankDecrease`
//     (`a < b → toNat(b-(a+1)) < toNat(b-a)`), `countdownRankDecrease` (`0 < i →
//     toNat(i-1) < toNat(i)`), `toNatMono` (`a ≤ b → toNat a ≤ toNat b`) with its three
//     sub-lemmas (`ofNatLeOfNatOfLe`, `leOfOfNatLeOfNat`, `negSuccNotNonNeg`), and
//     `strideRankDecrease` (`a < b → 1 ≤ k → toNat(b-(a+k)) < toNat(b-a)`). The
//     name-independent TYPE/PROOF builders are REUSED from `mirsem.rs` (`pub(crate)`,
//     logic byte-identical); where a MirSem proof references another lemma BY ITS
//     `Trust.MirSem.*` NAME, a name-parametric variant lives HERE (same term modulo the
//     constant name), so the registered `Trust.TrustIr.*` decls cross-reference each other
//     by `Trust.TrustIr.*` names only.
//
// PER-FUNCTION INSTANTIATION (the wired teardown increment):
//   * `check_loop_total_correct_instance(lp: &IrLoop)` — synthesizes the ranking from the
//     certified invariant CLASS exactly as `mirsem::synthesize_counter_ranking` does
//     (counter/accumulator/relational: `R := λ e. toNat(n − i)`; countdown: `toNat(i)`;
//     `≤`-guarded: `toNat((n+1) − i)`; stride k ≥ 1: `toNat(n − i)` with the
//     `strideRankDecrease` step), builds the CONCRETE kernel decrease proof, applies
//     `Trust.TrustIr.loopTotalCorrect`, `check_type`s the per-function conclusion
//     `∀ e, I e → And (I (execLoop e cond body (R e))) (evalCond (execLoop …) cond =
//     false)`, registers it, and audits the residue. ProvenModulo3 IFF the residue is
//     empty. FAIL-CLOSED everywhere: an unrecognized class/guard proposes no ranking; a
//     WRONG ranking's decrease proof does not retype ⇒ KernelRejected — never a guess.
//   * `check_cond_update_total_correct_instance(lp: &IrCondUpdateLoop)` — the SELECT-layer
//     analogue over `execLoopS` for the `max_scan` shape (`while i < n { m := Sel(i>m) i m;
//     i := i+1 }`): ranking `toNat(n − i)` from the `Lt` guard; the `Sel` statement leaves
//     `i`/`n` untouched so the SAME `loopRankDecrease` step retypes through `execS`.
//     Applied via `Trust.TrustIr.loopTotalCorrectS`. This is the instance that ELIMINATES
//     the in-path MirSem termination residue from `prove.rs`'s
//     `cond_update_fully_faithful_via_trustir` clause (e).
//
// SOUNDNESS DISCIPLINE (house rules, non-negotiable):
//   * modulo exactly 3 — every registration in this module re-audits `env.axiom_deps` and
//     FAILS (Err / KernelRejected) on any non-empty residue;
//   * fail-closed — unsupported classes decline, wrong rankings are kernel-rejected;
//   * ADDITIVE — no existing `trustir_anchor` registration or `mirsem` logic is altered
//     (the only sibling edits are `pub(crate)` visibility); `vc_refute.rs` untouched;
//   * NO new axiom, NO free constants — every fact is PROVEN (the whole suite is
//     `Declaration::Theorem`, kernel-checked here before registration).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Declaration, Environment, Expr, Level, LevelVec, Name, TypeChecker,
};

use crate::trustir_anchor::{
    IrCond, IrCondUpdateLoop, IrLoop, IrLoopInvariant, IrOperand, RefinementVerdict, TRUSTIR_COND,
    TRUSTIR_EVAL_BODY, TRUSTIR_EVAL_COND, TRUSTIR_EXEC_LOOP, TRUSTIR_EXEC_LOOP_S, TRUSTIR_EXEC_S,
    TRUSTIR_LOOP_INVARIANT_RULE, TRUSTIR_LOOP_INVARIANT_RULE_S, TRUSTIR_SSTMT, TRUSTIR_STMT,
    TrustIrCmpOp,
};

// ---------------------------------------------------------------------------
// Canonical Clean names — Trust.TrustIr.* ONLY (never Trust.MirSem.*)
// ---------------------------------------------------------------------------

/// Raw `Nat.le` transitivity `∀ a b c, Nat.le a b → Nat.le b c → Nat.le a c` — the
/// descent-chaining lemma `boundedHalt` rests on. Port of `Trust.MirSem.nat_le_trans`.
pub const TRUSTIR_NAT_LE_TRANS: &str = "Trust.TrustIr.natLeTrans";

/// Guard-FALSE stability on the BASE loop layer: `∀ cond body n e, evalCond e cond = false
/// → evalCond (execLoop e cond body n) cond = false`. Port of `Trust.MirSem.guardFalseStable`.
pub const TRUSTIR_GUARD_FALSE_STABLE: &str = "Trust.TrustIr.guardFalseStable";
/// Well-founded BOUNDED-HALT on the BASE layer: `∀ R cond body, decrease → ∀ k e,
/// Nat.le (R e) k → evalCond (execLoop e cond body k) cond = false`. Port of
/// `Trust.MirSem.boundedHalt`.
pub const TRUSTIR_BOUNDED_HALT: &str = "Trust.TrustIr.boundedHalt";
/// The ranking→termination while-rule on the BASE layer: `∀ R cond body, decrease →
/// ∀ e, evalCond (execLoop e cond body (R e)) cond = false`. Port of
/// `Trust.MirSem.loopRankTerminates`.
pub const TRUSTIR_LOOP_RANK_TERMINATES: &str = "Trust.TrustIr.loopRankTerminates";
/// The COMPOSED TOTAL-CORRECTNESS while-theorem on the BASE layer:
/// `∀ I R cond body, pres → decrease → ∀ e, I e →
///    And (I (execLoop e cond body (R e))) (evalCond (execLoop …) cond = false)`.
/// Port of `Trust.MirSem.loopTotalCorrect` (the `And.intro` of `loopInvariantRule` at fuel
/// `R e` with `loopRankTerminates` at the same `e`).
pub const TRUSTIR_LOOP_TOTAL_CORRECT: &str = "Trust.TrustIr.loopTotalCorrect";

/// Guard-FALSE stability on the SELECT layer (`execS`/`execLoopS`, `List SStmt` bodies).
pub const TRUSTIR_GUARD_FALSE_STABLE_S: &str = "Trust.TrustIr.guardFalseStableS";
/// Well-founded BOUNDED-HALT on the SELECT layer.
pub const TRUSTIR_BOUNDED_HALT_S: &str = "Trust.TrustIr.boundedHaltS";
/// The ranking→termination while-rule on the SELECT layer.
pub const TRUSTIR_LOOP_RANK_TERMINATES_S: &str = "Trust.TrustIr.loopRankTerminatesS";
/// The COMPOSED TOTAL-CORRECTNESS while-theorem on the SELECT layer (composes
/// `loopInvariantRuleS` with `loopRankTerminatesS`).
pub const TRUSTIR_LOOP_TOTAL_CORRECT_S: &str = "Trust.TrustIr.loopTotalCorrectS";

/// The pure counter decrease lemma `∀ (a b : Int), Int.lt a b →
/// Nat.lt (Int.toNat (Int.sub b (Int.add a 1))) (Int.toNat (Int.sub b a))`.
/// DENOTATION-INDEPENDENT (pure Int/Nat). Port of `Trust.MirSem.loopRankDecrease`.
pub const TRUSTIR_LOOP_RANK_DECREASE: &str = "Trust.TrustIr.loopRankDecrease";
/// The countdown decrease lemma `∀ (i : Int), Int.lt 0 i → Nat.lt (toNat (i-1)) (toNat i)`.
/// Port of `Trust.MirSem.countdownRankDecrease`.
pub const TRUSTIR_COUNTDOWN_RANK_DECREASE: &str = "Trust.TrustIr.countdownRankDecrease";
/// `Int.toNat` monotonicity `∀ (a b : Int), Int.le a b → Nat.le (toNat a) (toNat b)`.
/// Port of `Trust.MirSem.toNatMono`.
pub const TRUSTIR_TONAT_MONO: &str = "Trust.TrustIr.toNatMono";
/// Sub-lemma: the forward `ofNat` cast `∀ m p, Nat.le m p → Int.le (ofNat m) (ofNat p)`.
/// Port of `Trust.MirSem.ofNatLeOfNatOfLe`.
pub const TRUSTIR_OFNAT_LE_OFNAT_OF_LE: &str = "Trust.TrustIr.ofNatLeOfNatOfLe";
/// Sub-lemma: the converse `ofNat` cast `∀ m p, Int.le (ofNat m) (ofNat p) → Nat.le m p`.
/// Port of `Trust.MirSem.leOfOfNatLeOfNat`.
pub const TRUSTIR_LE_OF_OFNAT_LE_OFNAT: &str = "Trust.TrustIr.leOfOfNatLeOfNat";
/// Sub-lemma: `∀ q, Int.NonNeg (Int.negSucc q) → False`. Port of
/// `Trust.MirSem.negSuccNotNonNeg`.
pub const TRUSTIR_NEGSUCC_NOT_NONNEG: &str = "Trust.TrustIr.negSuccNotNonNeg";
/// The STRIDE decrease lemma `∀ (a b k : Int), Int.lt a b → Int.le 1 k →
/// Nat.lt (toNat (b-(a+k))) (toNat (b-a))`. Port of `Trust.MirSem.strideRankDecrease`.
pub const TRUSTIR_STRIDE_RANK_DECREASE: &str = "Trust.TrustIr.strideRankDecrease";

// ---------------------------------------------------------------------------
// Loop-layer descriptor — ONE set of ported builders serves both the BASE
// (`evalBody`/`execLoop`) and SELECT (`execS`/`execLoopS`) layers.
// ---------------------------------------------------------------------------

/// The constants a loop layer's termination theory is stated over. The proof TERMS are
/// byte-identical across layers (the MirSem proofs never inspect the statement type);
/// only the denotation constants differ.
struct LoopLayer {
    /// The body executor `Env → List <elem> → Env` (`evalBody` | `execS`).
    exec: &'static str,
    /// The fuel-indexed loop fixpoint (`execLoop` | `execLoopS`).
    exec_loop: &'static str,
    /// The body-statement element type (`Stmt` | `SStmt`).
    body_elem_ty: &'static str,
    /// The layer's Hoare while-rule (`loopInvariantRule` | `loopInvariantRuleS`) —
    /// ALREADY registered by `trustir_anchor::trustir_env`.
    loop_invariant_rule: &'static str,
    /// This module's guard-false-stability lemma name for the layer.
    guard_false_stable: &'static str,
    /// This module's bounded-halt lemma name for the layer.
    bounded_halt: &'static str,
    /// This module's ranking→termination theorem name for the layer.
    loop_rank_terminates: &'static str,
    /// This module's composed total-correctness theorem name for the layer.
    loop_total_correct: &'static str,
}

/// The BASE loop layer (flat `Stmt` bodies — counter/countdown/stride/accumulator loops).
const BASE_LAYER: LoopLayer = LoopLayer {
    exec: TRUSTIR_EVAL_BODY,
    exec_loop: TRUSTIR_EXEC_LOOP,
    body_elem_ty: TRUSTIR_STMT,
    loop_invariant_rule: TRUSTIR_LOOP_INVARIANT_RULE,
    guard_false_stable: TRUSTIR_GUARD_FALSE_STABLE,
    bounded_halt: TRUSTIR_BOUNDED_HALT,
    loop_rank_terminates: TRUSTIR_LOOP_RANK_TERMINATES,
    loop_total_correct: TRUSTIR_LOOP_TOTAL_CORRECT,
};

/// The SELECT loop layer (`SStmt` bodies with the conditional-update `Sel` — `max_scan`).
const SELECT_LAYER: LoopLayer = LoopLayer {
    exec: TRUSTIR_EXEC_S,
    exec_loop: TRUSTIR_EXEC_LOOP_S,
    body_elem_ty: TRUSTIR_SSTMT,
    loop_invariant_rule: TRUSTIR_LOOP_INVARIANT_RULE_S,
    guard_false_stable: TRUSTIR_GUARD_FALSE_STABLE_S,
    bounded_halt: TRUSTIR_BOUNDED_HALT_S,
    loop_rank_terminates: TRUSTIR_LOOP_RANK_TERMINATES_S,
    loop_total_correct: TRUSTIR_LOOP_TOTAL_CORRECT_S,
};

// ---------------------------------------------------------------------------
// Small Expr helpers (local copies of the tiny mirsem/trustir_anchor spellings,
// BYTE-IDENTICAL term shapes; kept local so the sibling modules stay untouched
// beyond visibility).
// ---------------------------------------------------------------------------

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

fn int_ty() -> Expr {
    cst("Int")
}

/// `Env = Nat → Int` — identical to `trustir_anchor::env_ty` / `mirsem::env_ty`.
fn env_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), cst("Nat"), int_ty())
}

/// The `Env → Prop` invariant signature.
fn env_pred_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), env_ty(), Expr::prop())
}

/// The `Env → Nat` ranking signature.
fn env_to_nat_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), env_ty(), cst("Nat"))
}

/// The closed `Int` literal — identical to `trustir_anchor::int_lit` / `mirsem::int_lit`.
fn int_lit(n: i128) -> Expr {
    // Trust: EXACT ENCODING (2026-07-24) — see `clean_ground::int_lit_to_expr`. The
    // former `as u64` was `n mod 2^64`, a truncation that made the map non-injective
    // and caused a demonstrated LIVE FALSE ACCEPT. `nat_lit_u128` is a drop-in:
    // `BigNat::from_limbs` normalizes a trailing zero limb back to `Small`, so every
    // `k <= u64::MAX` encodes byte-identically and only the previously-truncated
    // literals change. Keeping this in lockstep is what the byte-identity claim above
    // asserts — it is now TRUE again for the full `i128` range.
    if n >= 0 {
        Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(n.unsigned_abs()))
    } else {
        Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(n.unsigned_abs() - 1))
    }
}

/// `Int.ofNat 1` in the canonical `Int.ofNat (Nat.succ Nat.zero)` form (identical to
/// `mirsem::int_one` / `trustir_anchor::int_one`).
fn int_one() -> Expr {
    Expr::app(cst("Int.ofNat"), Expr::app(cst("Nat.succ"), cst("Nat.zero")))
}

/// `Nat.succ e`.
fn nat_succ(e: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e)
}

/// Raw `@Nat.le a b : Prop`.
fn nat_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
}

/// Raw `@Nat.lt a b : Prop` (def-eq to `Nat.le (Nat.succ a) b`).
fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
}

/// `@Int.ofNat n`.
fn int_ofnat(n: Expr) -> Expr {
    Expr::app(cst("Int.ofNat"), n)
}

/// `@Int.le a b`.
fn int_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Int.le"), [a, b])
}

/// `@congrArg α β a b f h : @Eq β (f a) (f b)`.
fn congr_arg(alpha: Expr, beta: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [alpha, beta, a, b, f, h],
    )
}

/// `@Eq.symm α a b h : @Eq α b a` (α : Sort 1).
fn eq_symm_int(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b, h],
    )
}

/// `@Eq.trans α a b c hab hbc : @Eq α a c` (α : Sort 1).
fn eq_trans_int(a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b, c, hab, hbc],
    )
}

/// `@Eq Bool b Bool.true` — the guard-TRUE equality.
fn eq_bool_true(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), b, cst("Bool.true")],
    )
}

/// `@Eq Bool b Bool.false` — the guard-FALSE predicate.
fn eq_bool_false(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), b, cst("Bool.false")],
    )
}

/// `@Int.add_le_add_right a b hab c : Int.le (Int.add a c) (Int.add b c)` — identical to
/// `mirsem::add_le_add_right` / `trustir_anchor::add_le_add_right_ir`.
fn add_le_add_right(a: Expr, b: Expr, hab: Expr, c: Expr) -> Expr {
    Expr::apps(cst("Int.add_le_add_right"), [a, b, hab, c])
}

/// `evalCond e cond : Bool` (SHARED by both layers — the guard denotation never forks).
fn eval_cond_app_t(e: Expr, cond: Expr) -> Expr {
    Expr::apps(cst(TRUSTIR_EVAL_COND), [e, cond])
}

/// `<layer.exec> e body : Env`.
fn exec_app_t(layer: &LoopLayer, e: Expr, body: Expr) -> Expr {
    Expr::apps(cst(layer.exec), [e, body])
}

/// `<layer.exec_loop> e cond body fuel : Env`.
fn exec_loop_app_t(layer: &LoopLayer, e: Expr, cond: Expr, body: Expr, fuel: Expr) -> Expr {
    Expr::apps(cst(layer.exec_loop), [e, cond, body, fuel])
}

/// `List <layer.body_elem_ty>` as a kernel type.
fn list_body_ty(layer: &LoopLayer) -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), cst(layer.body_elem_ty))
}

/// The loop-HALTED predicate `evalCond (<exec_loop> e cond body fuel) cond = false`.
/// Port of `mirsem::loop_halts_prop`.
fn loop_halts_prop_t(layer: &LoopLayer, e: Expr, cond: Expr, body: Expr, fuel: Expr) -> Expr {
    let looped = exec_loop_app_t(layer, e, cond.clone(), body, fuel);
    eq_bool_false(eval_cond_app_t(looped, cond))
}

/// The RANK-DECREASE hypothesis `∀ (e : Env), evalCond e cond = true →
/// Nat.lt (R (<exec> e body)) (R e)`. Port of `mirsem::decrease_hyp_type`.
fn decrease_hyp_type_t(layer: &LoopLayer, r_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // ∀ (e:Env), (evalCond e cond = true) → Nat.lt (R (<exec> e body)) (R e)
    //   dom (under ∀ e): e=0, refs +1.
    let guard = eval_cond_app_t(Expr::bvar(0), lift(cond_ref, 1));
    let dom = eq_bool_true(guard);
    //   cod (under ∀ e + 1 arrow): e=1, refs +2.
    let r_e = Expr::app(lift(r_ref, 2), Expr::bvar(1));
    let r_step = Expr::app(lift(r_ref, 2), exec_app_t(layer, Expr::bvar(1), lift(body_ref, 2)));
    let cod = nat_lt(r_step, r_e);
    Expr::pi(bd(), env_ty(), Expr::pi(bd(), dom, cod))
}

/// The PRESERVATION hypothesis `∀ (e : Env), I e → evalCond e cond = true →
/// I (<exec> e body)`. Port of `mirsem::preservation_hyp_type` /
/// `trustir_anchor::preservation_hyp_type_ir` (layer-parametric).
fn preservation_hyp_type_t(
    layer: &LoopLayer,
    i_ref: &Expr,
    cond_ref: &Expr,
    body_ref: &Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // 1st arrow domain: I e   (e=0; refs +1)
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    // 2nd arrow domain: evalCond e cond = true   (e=1; refs +2)
    let dom2 = eq_bool_true(eval_cond_app_t(Expr::bvar(1), lift(cond_ref, 2)));
    // codomain: I (<exec> e body)   (e=2; refs +3)
    let cod = Expr::app(lift(i_ref, 3), exec_app_t(layer, Expr::bvar(2), lift(body_ref, 3)));
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

// ---------------------------------------------------------------------------
// Registration helper — check_type + add_decl + EMPTY-residue audit (fail-closed).
// ---------------------------------------------------------------------------

/// `check_type` a `(type, proof)`, register it as a `Declaration::Theorem` (idempotent on
/// `name`), and AUDIT the axiom residue: registration FAILS unless the decl's axiom
/// closure is ⊆ the 3 foundational axioms (empty residue). Mirrors
/// `mirsem::register_checked_theorem` + the house per-decl `axiom_deps` gate.
fn register_checked_theorem_t(
    env: &mut Environment,
    name_str: &str,
    ty: Expr,
    proof: Expr,
) -> Result<(), String> {
    let name = Name::from_string(name_str);
    if env.get_const(&name).is_none() {
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&proof, &ty).map_err(|e| format!("{name_str} check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: proof,
        })
        .map_err(|e| format!("add_decl({name_str}): {e:?}"))?;
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => Ok(()),
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            Err(format!("{name_str} axiom residue: {names:?}"))
        }
        None => Err(format!("{name_str} decl not found after registration")),
    }
}

// ---------------------------------------------------------------------------
// `Trust.TrustIr.natLeTrans` — port of `mirsem::register_nat_le_trans` (the type/proof
// there are built inline, so the byte-identical builders live here under the TrustIr name).
// ---------------------------------------------------------------------------

/// Register `Trust.TrustIr.natLeTrans : ∀ (a b c : Nat), Nat.le a b → Nat.le b c →
/// Nat.le a c` (idempotent) — RAW `Nat.le` transitivity via `Nat.le.rec` on the SECOND
/// premise. Byte-identical proof term to `Trust.MirSem.nat_le_trans`.
fn register_nat_le_trans_t(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    let nat = cst("Nat");

    // TYPE: ∀ a b c, Nat.le a b → Nat.le b c → Nat.le a c
    let ty = {
        // inside ∀a∀b∀c: c=0,b=1,a=2
        let hab = nat_le(Expr::bvar(2), Expr::bvar(1));
        // after `hab →` : c=1,b=2,a=3
        let hbc = nat_le(Expr::bvar(2), Expr::bvar(1));
        // after `hbc →` : c=2,b=3,a=4
        let concl = nat_le(Expr::bvar(4), Expr::bvar(2));
        let arrows = Expr::pi(bd(), hab, Expr::pi(bd(), hbc, concl));
        Expr::pi(
            bd(),
            nat.clone(),
            Expr::pi(bd(), nat.clone(), Expr::pi(bd(), nat.clone(), arrows)),
        )
    };

    // PROOF: λ a b c hab hbc. @Nat.le.rec b motive refl_minor step_minor c hbc
    //   depth inside `λ a λ b λ c λ hab λ hbc`: hbc=0, hab=1, c=2, b=3, a=4.
    let val = {
        let le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // motive : λ (m:Nat)(_ : Nat.le b m). Nat.le a m
        let motive = {
            // domain `Nat.le b m`: under `λ m` only ⇒ m=0, b=4 (hbc=1,hab=2,c=3,b=4,a=5).
            let le_bm_dom = nat_le(Expr::bvar(4), Expr::bvar(0));
            // codomain `Nat.le a m`: under `λ m λ (_:Nat.le b m)` ⇒ m=1, a=6.
            let le_am = nat_le(Expr::bvar(6), Expr::bvar(1));
            Expr::lam(bd(), nat.clone(), Expr::lam(bd(), le_bm_dom, le_am))
        };
        // refl_minor : motive b (Nat.le.refl b) ≡ Nat.le a b = hab (at proof-body depth: hab=1).
        let refl_minor = Expr::bvar(1);
        // step_minor : λ (m:Nat)(h:Nat.le b m)(ih:Nat.le a m). @Nat.le.step a m ih
        //   inside `λ m λ h λ ih`: ih=0,h=1,m=2,hbc=3,hab=4,c=5,b=6,a=7.
        let step_minor = {
            // dom1 `Nat.le b m` (under λm): m=0, b=4.
            let dom_h = nat_le(Expr::bvar(4), Expr::bvar(0));
            // dom2 `Nat.le a m` (under λm λh): m=1, a=6.
            let dom_ih = nat_le(Expr::bvar(6), Expr::bvar(1));
            // body `@Nat.le.step a m ih` (under λm λh λih): ih=0,m=2,a=7.
            let stepped = Expr::apps(le_step, [Expr::bvar(7), Expr::bvar(2), Expr::bvar(0)]);
            Expr::lam(bd(), nat.clone(), Expr::lam(bd(), dom_h, Expr::lam(bd(), dom_ih, stepped)))
        };
        // @Nat.le.rec b motive refl_minor step_minor c hbc   (b=3, c=2, hbc=0).
        let rec_app = Expr::apps(
            le_rec,
            [Expr::bvar(3), motive, refl_minor, step_minor, Expr::bvar(2), Expr::bvar(0)],
        );
        Expr::lam(
            bd(),
            nat.clone(),
            Expr::lam(
                bd(),
                nat.clone(),
                Expr::lam(
                    bd(),
                    nat.clone(),
                    Expr::lam(
                        bd(),
                        nat_le(Expr::bvar(2), Expr::bvar(1)), // hab : Nat.le a b
                        Expr::lam(bd(), nat_le(Expr::bvar(2), Expr::bvar(1)), rec_app), // hbc
                    ),
                ),
            ),
        )
    };

    register_checked_theorem_t(env, TRUSTIR_NAT_LE_TRANS, ty, val)
}

// ---------------------------------------------------------------------------
// guardFalseStable[S] — port of `mirsem::register_guard_false_stable` onto a layer.
// ---------------------------------------------------------------------------

/// The `guardFalseStable` TYPE for `layer`: `∀ (cond : Cond)(body : List <elem>)(n : Nat)
/// (e : Env), evalCond e cond = false → evalCond (<exec_loop> e cond body n) cond = false`.
fn guard_false_stable_type_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    // inside ∀cond∀body∀n∀e: e=0,n=1,body=2,cond=3
    let hf = eq_bool_false(eval_cond_app_t(Expr::bvar(0), Expr::bvar(3)));
    // after `hf →`: e=1,n=2,body=3,cond=4
    let concl =
        loop_halts_prop_t(layer, Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), Expr::bvar(2));
    let after = Expr::pi(bd(), hf, concl);
    Expr::pi(
        bd(),
        cst(TRUSTIR_COND),
        Expr::pi(bd(), list_body, Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), after))),
    )
}

/// The `guardFalseStable` PROOF for `layer` — `Nat.rec` on `n`; the succ case transports
/// the goal along `hf` (`@Eq.rec` at `a := false`, `b := the guard`, via `Eq.symm hf`) so
/// the stepped env `Bool.rec … false ≡ e` collapses to the IH. Byte-identical term
/// structure to `mirsem::register_guard_false_stable`'s proof (with `eval_cond ↦ evalCond`,
/// `exec ↦ <layer.exec>`, `exec_loop ↦ <layer.exec_loop>`).
fn guard_false_stable_proof_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

    // motive (under `λ cond λ body λ n`): n=0,body=1,cond=2; then `∀ e` ⇒ e=0,n=1,body=2,cond=3.
    let motive = {
        let hf = eq_bool_false(eval_cond_app_t(Expr::bvar(0), Expr::bvar(3)));
        // after `hf →`: e=1,n=2,body=3,cond=4
        let concl =
            loop_halts_prop_t(layer, Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), Expr::bvar(2));
        let quant_e = Expr::pi(bd(), env_ty(), Expr::pi(bd(), hf, concl));
        Expr::lam(bd(), cst("Nat"), quant_e)
    };

    // zero_case : λ e hf. hf   (`<exec_loop> e cond body 0 ≡ e`).
    //   (no-λn convention) the `hf_ty` DOMAIN sits under `λ cond λ body λ e` ⇒ e=0,body=1,cond=2.
    let zero_case = {
        let hf_ty = eq_bool_false(eval_cond_app_t(Expr::bvar(0), Expr::bvar(2)));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), hf_ty, Expr::bvar(0)))
    };

    // succ_case : λ (m:Nat)(ih : motive m)(e:Env)(hf : evalCond e cond = false). <transport>
    //   inside `λ cond λ body λ m λ ih λ e λ hf`: hf=0,e=1,ih=2,m=3,body=4,cond=5.
    let succ_case = {
        // ih : motive m  (built after `λ m`, before `λ ih`): m=0,body=1,cond=2.
        let ih_ty = {
            // ∀ e, evalCond e cond = false → evalCond (<exec_loop> e cond body m) cond = false
            // under `∀ e`: e=0,m=1,body=2,cond=3
            let hf = eq_bool_false(eval_cond_app_t(Expr::bvar(0), Expr::bvar(3)));
            // after `hf →`: e=1,m=2,body=3,cond=4
            let concl = loop_halts_prop_t(
                layer,
                Expr::bvar(1),
                Expr::bvar(4),
                Expr::bvar(3),
                Expr::bvar(2),
            );
            Expr::pi(bd(), env_ty(), Expr::pi(bd(), hf, concl))
        };

        // @Eq.rec.{0,1} : {α}{a}{motive} → motive a refl → {b} → (h : a = b) → motive b h.
        // Transport the goal along `Eq.symm hf : false = (evalCond e cond)`; the base
        // `M false ≡ evalCond (<exec_loop> e cond body m) cond = false = ih e hf`.
        let eq_rec = Expr::const_(
            Name::from_string("Eq.rec"),
            vec![Level::zero(), Level::succ(Level::zero())],
        );
        // guard `g := evalCond e cond` at succ_case body depth (e=1,cond=5).
        let guard = eval_cond_app_t(Expr::bvar(1), Expr::bvar(5));
        // motive M : λ (x:Bool)(_ : false = x).
        //   evalCond (<exec_loop> (Bool.rec (λ_.Env) e (<exec> e body) x) cond body m) cond = false
        //   inside succ body (hf=0,e=1,ih=2,m=3,body=4,cond=5) then `λ x λ heq`:
        //   heq=0,x=1,hf=2,e=3,ih=4,m=5,body=6,cond=7.
        let m_motive = {
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            // domain `false = x` (under `λ x` only): x=0.
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), cst("Bool.false"), Expr::bvar(0)],
            );
            // codomain (under `λ x λ heq`): heq=0,x=1,hf=2,e=3,ih=4,m=5,body=6,cond=7.
            let exec_body = exec_app_t(layer, Expr::bvar(3), Expr::bvar(6));
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod =
                loop_halts_prop_t(layer, stepped, Expr::bvar(7), Expr::bvar(6), Expr::bvar(5));
            Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), eq_dom, cod))
        };
        // base : M false ≡ evalCond (<exec_loop> e cond body m) cond = false = ih e hf
        //   at succ body depth: ih=2,e=1,hf=0.
        let base = Expr::apps(Expr::bvar(2), [Expr::bvar(1), Expr::bvar(0)]);
        // Eq.symm {Bool} {g} {false} hf : false = g.
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]);
        let hf_sym =
            Expr::apps(eq_symm, [cst("Bool"), guard.clone(), cst("Bool.false"), Expr::bvar(0)]);
        // @Eq.rec Bool false M base g hf_sym : M g ≡ GOAL.
        let applied =
            Expr::apps(eq_rec, [cst("Bool"), cst("Bool.false"), m_motive, base, guard, hf_sym]);

        Expr::lam(
            bd(),
            cst("Nat"), // m
            Expr::lam(
                bd(),
                ih_ty, // ih
                Expr::lam(
                    bd(),
                    env_ty(), // e
                    Expr::lam(
                        bd(),
                        // hf : evalCond e cond = false (inside λ m λ ih λ e: e=0,body=3,cond=4)
                        eq_bool_false(eval_cond_app_t(Expr::bvar(0), Expr::bvar(4))),
                        applied,
                    ),
                ),
            ),
        )
    };

    // λ cond body n. @Nat.rec.{0} motive zero_case succ_case n
    //   motive/cases built UNDER `λ cond λ body` (no λ n) ⇒ lift each by 1; scrutinee n=0.
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        cst(TRUSTIR_COND),
        Expr::lam(bd(), list_body, Expr::lam(bd(), cst("Nat"), rec_applied)),
    )
}

// ---------------------------------------------------------------------------
// boundedHalt[S] — port of `mirsem::bounded_halt_{type,proof}` onto a layer.
// ---------------------------------------------------------------------------

/// The BOUNDED-HALT lemma TYPE for `layer`: `∀ (R : Env→Nat)(cond)(body), decrease →
/// ∀ (k : Nat)(e : Env), Nat.le (R e) k → evalCond (<exec_loop> e cond body k) cond = false`.
fn bounded_halt_type_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    // inside `∀ R ∀ cond ∀ body`: body=0,cond=1,R=2.
    let decrease = decrease_hyp_type_t(layer, &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ k e, Nat.le (R e) k → loop_halts e cond body k
    //   inside `∀ R ∀ cond ∀ body (decrease→) ∀ k ∀ e`: e=0,k=1,decrease=2,body=3,cond=4,R=5.
    let r_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
    let le_hyp = nat_le(r_e, Expr::bvar(1));
    // loop_halts e cond body k (under one more arrow): e=1,k=2,decrease=3,body=4,cond=5,R=6.
    let halts =
        loop_halts_prop_t(layer, Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let arrow = Expr::pi(bd(), le_hyp, halts);
    let body_e = Expr::pi(bd(), env_ty(), arrow);
    let body_k = Expr::pi(bd(), cst("Nat"), body_e);
    let after_decrease = Expr::pi(bd(), decrease, body_k);
    Expr::pi(
        bd(),
        env_to_nat_ty(),
        Expr::pi(bd(), cst(TRUSTIR_COND), Expr::pi(bd(), list_body, after_decrease)),
    )
}

/// The BOUNDED-HALT lemma PROOF for `layer` — well-founded descent by `Nat.rec` on the
/// fuel bound `k`. Byte-identical term structure to `mirsem::bounded_halt_proof` (with
/// `nat_le_trans ↦ natLeTrans`, `guardFalseStable ↦ <layer.guard_false_stable>`).
fn bounded_halt_proof_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    let bool_rec0 = || Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let bool_rec1 =
        || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = || Expr::lam(bd(), cst("Bool"), env_ty());
    let eq_refl_bool = |b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), b],
        )
    };

    // depth inside `λ R λ cond λ body λ decrease`: decrease=0,body=1,cond=2,R=3.

    // motive P : Nat → Prop = λ k. ∀ e, Nat.le (R e) k → loop_halts e cond body k
    //   under `λ R..λ decrease λ k`: k=0,decrease=1,body=2,cond=3,R=4; then `∀ e`:
    //   e=0,k=1,decrease=2,body=3,cond=4,R=5.
    let motive = {
        let r_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        let le_hyp = nat_le(r_e, Expr::bvar(1));
        // loop_halts (under one more arrow): e=1,k=2,decrease=3,body=4,cond=5,R=6
        let halts =
            loop_halts_prop_t(layer, Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let arrow = Expr::pi(bd(), le_hyp, halts);
        Expr::lam(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), arrow))
    };

    // zero_case : ∀ e, Nat.le (R e) 0 → loop_halts e cond body 0
    //   loop_halts e cond body 0 ≡ (evalCond e cond = false).
    //   λ e (hk : Nat.le (R e) 0). @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g)
    //   under `λ R..λ decrease λ e λ hk`: hk=0,e=1,decrease=2,body=3,cond=4,R=5.
    let zero_case = {
        let guard = eval_cond_app_t(Expr::bvar(1), Expr::bvar(4)); // g = evalCond e cond
        // mg : Bool → Prop = λ b. (g = b) → (g = false)
        //   under `..λ e λ hk λ b`: b=0,hk=1,e=2,decrease=3,body=4,cond=5,R=6.
        let mg = {
            let g_inner = eval_cond_app_t(Expr::bvar(2), Expr::bvar(5));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_inner, Expr::bvar(0)],
            );
            // cod: g = false (under λ b + arrow): b=1,hk=2,e=3 ⇒ g at e=3,cond=6.
            let g_cod = eval_cond_app_t(Expr::bvar(3), Expr::bvar(6));
            let cod = eq_bool_false(g_cod);
            Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), eq_dom, cod))
        };
        // false_arm : (g = false) → (g = false) = λ h. h
        let false_arm = {
            let g_dom = eval_cond_app_t(Expr::bvar(1), Expr::bvar(4));
            Expr::lam(bd(), eq_bool_false(g_dom), Expr::bvar(0))
        };
        // true_arm : (g = true) → (g = false)
        //   from ht:g=true, `decrease e ht : Nat.le (succ (R(<exec> e body))) (R e)`;
        //   natLeTrans … hk : Nat.le (succ …) 0; Nat.not_succ_le_zero … : False; False.elim.
        //   under `..λ e λ hk λ ht`: ht=0,hk=1,e=2,decrease=3,body=4,cond=5,R=6.
        let true_arm = {
            // the `λ ht` DOMAIN sits under `λ e λ hk` (BEFORE λ ht): e=1,cond=4.
            let g_dom = eval_cond_app_t(Expr::bvar(1), Expr::bvar(4));
            let eq_true = eq_bool_true(g_dom);
            // body under `λ ht`: ht=0,hk=1,e=2,decrease=3,body=4,cond=5,R=6.
            let r_exec = {
                let exec = exec_app_t(layer, Expr::bvar(2), Expr::bvar(4)); // <exec> e body
                Expr::app(Expr::bvar(6), exec) // R (<exec> e body)
            };
            // decrease e ht : Nat.lt (R (<exec> e body)) (R e) ≡ Nat.le (succ …) (R e)
            let dec_app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(0)]);
            let r_e = Expr::app(Expr::bvar(6), Expr::bvar(2)); // R e
            // natLeTrans (succ r_exec) (R e) 0 dec_app hk
            let trans = Expr::apps(
                cst(TRUSTIR_NAT_LE_TRANS),
                [
                    nat_succ(r_exec.clone()),
                    r_e,
                    Expr::nat_lit(0),
                    dec_app,
                    Expr::bvar(1), // hk
                ],
            );
            // Nat.not_succ_le_zero r_exec trans : False
            let false_pf = Expr::apps(
                Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                [r_exec, trans],
            );
            // @False.elim.{0} (g = false) false_pf
            let g_false_goal = eq_bool_false(eval_cond_app_t(Expr::bvar(2), Expr::bvar(5)));
            let false_elim = Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [g_false_goal, false_pf],
            );
            Expr::lam(bd(), eq_true, false_elim)
        };
        // @Bool.rec.{0} mg false_arm true_arm g (Eq.refl Bool g)
        let ghelper = Expr::apps(bool_rec0(), [mg, false_arm, true_arm, guard.clone()]);
        let applied = Expr::app(ghelper, eq_refl_bool(guard));
        // λ e (hk : Nat.le (R e) 0). applied   (hk under λ e: e=0,R=4)
        let hk_ty = nat_le(Expr::app(Expr::bvar(4), Expr::bvar(0)), Expr::nat_lit(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), hk_ty, applied))
    };

    // succ_case : λ (k':Nat)(ih : P k')(e : Env)(hk : Nat.le (R e) (succ k')).
    //   GOAL ≡ evalCond (<exec_loop> (Bool.rec (λ_.Env) e (<exec> e body) g) cond body k')
    //          cond = false, closed by @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g).
    //   under `λ R..λ decrease λ k' λ ih λ e λ hk`: hk=0,e=1,ih=2,k'=3,decrease=4,body=5,cond=6,R=7.
    let succ_case = {
        // ih : P k'  (after `λ k'`, before `λ ih`): k'=0,decrease=1,body=2,cond=3,R=4.
        let ih_ty = {
            // ∀ e, Nat.le (R e) k' → loop_halts e cond body k'
            // under `∀ e`: e=0,k'=1,decrease=2,body=3,cond=4,R=5
            let le_hyp = nat_le(Expr::app(Expr::bvar(5), Expr::bvar(0)), Expr::bvar(1));
            // loop_halts (under arrow): e=1,k'=2,decrease=3,body=4,cond=5,R=6
            let halts = loop_halts_prop_t(
                layer,
                Expr::bvar(1),
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(2),
            );
            Expr::pi(bd(), env_ty(), Expr::pi(bd(), le_hyp, halts))
        };

        let guard = eval_cond_app_t(Expr::bvar(1), Expr::bvar(6)); // g (e=1,cond=6)

        // mg : Bool → Prop = λ b. (g = b) →
        //   evalCond (<exec_loop> (Bool.rec (λ_.Env) e (<exec> e body) b) cond body k') cond = false
        //   under `..λ hk λ b`: b=0,hk=1,e=2,ih=3,k'=4,decrease=5,body=6,cond=7,R=8.
        let mg = {
            let g_inner = eval_cond_app_t(Expr::bvar(2), Expr::bvar(7));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_inner, Expr::bvar(0)],
            );
            // cod (under λ b + arrow): b=1,hk=2,e=3,ih=4,k'=5,decrease=6,body=7,cond=8,R=9.
            let exec_body = exec_app_t(layer, Expr::bvar(3), Expr::bvar(7));
            let stepped =
                Expr::apps(bool_rec1(), [env_motive(), Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod =
                loop_halts_prop_t(layer, stepped, Expr::bvar(8), Expr::bvar(7), Expr::bvar(5));
            Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), eq_dom, cod))
        };

        // false_arm : (g = false) → evalCond (<exec_loop> e cond body k') cond = false
        //   = λ hf. <guard_false_stable> cond body k' e hf.
        //   under `..λ hk λ hf`: hf=0,hk=1,e=2,ih=3,k'=4,decrease=5,body=6,cond=7,R=8.
        let false_arm = {
            let g_dom = eval_cond_app_t(Expr::bvar(1), Expr::bvar(6)); // BEFORE λ hf: e=1,cond=6
            let dom_ty = eq_bool_false(g_dom);
            let gfs = Expr::apps(
                cst(layer.guard_false_stable),
                [
                    Expr::bvar(7), // cond
                    Expr::bvar(6), // body
                    Expr::bvar(4), // k'
                    Expr::bvar(2), // e
                    Expr::bvar(0), // hf
                ],
            );
            Expr::lam(bd(), dom_ty, gfs)
        };

        // true_arm : (g = true) → evalCond (<exec_loop> (<exec> e body) cond body k') cond = false
        //   bound: decrease e ht; natLeTrans …; Nat.le_of_succ_le_succ …; ih (<exec> e body) bound.
        //   under `..λ hk λ ht`: ht=0,hk=1,e=2,ih=3,k'=4,decrease=5,body=6,cond=7,R=8.
        let true_arm = {
            let g_dom = eval_cond_app_t(Expr::bvar(1), Expr::bvar(6)); // BEFORE λ ht
            let dom_ty = eq_bool_true(g_dom);
            let exec_eb = exec_app_t(layer, Expr::bvar(2), Expr::bvar(6)); // <exec> e body
            let r_exec = Expr::app(Expr::bvar(8), exec_eb.clone()); // R (<exec> e body)
            let r_e = Expr::app(Expr::bvar(8), Expr::bvar(2)); // R e
            let dec_app = Expr::apps(Expr::bvar(5), [Expr::bvar(2), Expr::bvar(0)]); // decrease e ht
            // natLeTrans (succ r_exec) (R e) (succ k') dec_app hk
            let trans = Expr::apps(
                cst(TRUSTIR_NAT_LE_TRANS),
                [
                    nat_succ(r_exec.clone()),
                    r_e,
                    nat_succ(Expr::bvar(4)), // succ k'
                    dec_app,
                    Expr::bvar(1), // hk
                ],
            );
            // Nat.le_of_succ_le_succ r_exec k' trans : Nat.le r_exec k'
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [r_exec, Expr::bvar(4), trans],
            );
            // ih (<exec> e body) bound
            let ih_app = Expr::apps(Expr::bvar(3), [exec_eb, bound]);
            Expr::lam(bd(), dom_ty, ih_app)
        };

        // @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g)
        let ghelper = Expr::apps(bool_rec0(), [mg, false_arm, true_arm, guard.clone()]);
        let applied = Expr::app(ghelper, eq_refl_bool(guard));

        // λ k' (ih : P k') (e : Env) (hk : Nat.le (R e) (succ k')). applied
        //   hk under `λ k' λ ih λ e`: e=0,ih=1,k'=2,decrease=3,body=4,cond=5,R=6.
        let hk_ty = nat_le(Expr::app(Expr::bvar(6), Expr::bvar(0)), nat_succ(Expr::bvar(2)));
        Expr::lam(
            bd(),
            cst("Nat"), // k'
            Expr::lam(
                bd(),
                ih_ty,                                                      // ih
                Expr::lam(bd(), env_ty(), Expr::lam(bd(), hk_ty, applied)), // e, hk
            ),
        )
    };

    // λ R cond body decrease k. @Nat.rec.{0} motive zero_case succ_case k
    //   motive/zero/succ built UNDER `λ decrease` (no λ k) ⇒ lift by 1; scrutinee k=0.
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_to_nat_ty(),
        Expr::lam(
            bd(),
            cst(TRUSTIR_COND),
            Expr::lam(
                bd(),
                list_body,
                Expr::lam(
                    bd(),
                    decrease_hyp_type_t(layer, &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

// ---------------------------------------------------------------------------
// loopRankTerminates[S] — port of `mirsem::loop_rank_terminates_{type,proof}`.
// ---------------------------------------------------------------------------

/// The TERMINATION while-rule TYPE for `layer`: `∀ (R : Env→Nat)(cond)(body), decrease →
/// ∀ e, evalCond (<exec_loop> e cond body (R e)) cond = false`.
fn loop_rank_terminates_type_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    // inside `∀ R ∀ cond ∀ body`: body=0,cond=1,R=2.
    let decrease = decrease_hyp_type_t(layer, &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ e, evalCond (<exec_loop> e cond body (R e)) cond = false
    //   inside `∀ R ∀ cond ∀ body (decrease→) ∀ e`: e=0,decrease=1,body=2,cond=3,R=4.
    let fuel = Expr::app(Expr::bvar(4), Expr::bvar(0)); // (R e)
    let halts = loop_halts_prop_t(layer, Expr::bvar(0), Expr::bvar(3), Expr::bvar(2), fuel);
    let body_e = Expr::pi(bd(), env_ty(), halts);
    let after_decrease = Expr::pi(bd(), decrease, body_e);
    Expr::pi(
        bd(),
        env_to_nat_ty(),
        Expr::pi(bd(), cst(TRUSTIR_COND), Expr::pi(bd(), list_body, after_decrease)),
    )
}

/// The TERMINATION while-rule PROOF for `layer`: instantiate `boundedHalt`'s fuel bound
/// at the rank itself — `λ R cond body decrease e.
///   <bounded_halt> R cond body decrease (R e) e (Nat.le.refl (R e))`.
fn loop_rank_terminates_proof_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    // under `λ R λ cond λ body λ decrease λ e`: e=0,decrease=1,body=2,cond=3,R=4.
    let r_e = Expr::app(Expr::bvar(4), Expr::bvar(0)); // R e
    let le_refl = Expr::apps(Expr::const_(Name::from_string("Nat.le.refl"), vec![]), [r_e.clone()]); // Nat.le.refl (R e) : Nat.le (R e) (R e)
    let bh = Expr::apps(
        cst(layer.bounded_halt),
        [
            Expr::bvar(4), // R
            Expr::bvar(3), // cond
            Expr::bvar(2), // body
            Expr::bvar(1), // decrease
            r_e,           // k := R e
            Expr::bvar(0), // e
            le_refl,       // Nat.le (R e) (R e)
        ],
    );
    Expr::lam(
        bd(),
        env_to_nat_ty(),
        Expr::lam(
            bd(),
            cst(TRUSTIR_COND),
            Expr::lam(
                bd(),
                list_body,
                Expr::lam(
                    bd(),
                    decrease_hyp_type_t(layer, &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), env_ty(), bh),
                ),
            ),
        ),
    )
}

// ---------------------------------------------------------------------------
// loopTotalCorrect[S] — port of `mirsem::loop_total_correct_{conjuncts,type,proof}`.
// ---------------------------------------------------------------------------

/// Build the conjuncts `(R_e, A, B)` of the composed total-correctness conclusion at the
/// 8-binder-deep scope `hI=0, e=1, decrease=2, pres=3, body=4, cond=5, R=6, I=7`:
/// `A = I (<exec_loop> e cond body (R e))` (invariant at the halting state),
/// `B = evalCond (<exec_loop> …) cond = false` (the loop halted), both at the SHARED
/// fuel `R e`. Port of `mirsem::loop_total_correct_conjuncts`.
fn loop_total_correct_conjuncts_t(layer: &LoopLayer) -> (Expr, Expr, Expr) {
    // R e : Nat  (R=6, e=1 at this depth).
    let r_e = Expr::app(Expr::bvar(6), Expr::bvar(1));
    // <exec_loop> e cond body (R e)   (e=1, cond=5, body=4)
    let looped = exec_loop_app_t(layer, Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), r_e.clone());
    // A = I (<exec_loop> …)   (I=7)
    let a = Expr::app(Expr::bvar(7), looped);
    // B = evalCond (<exec_loop> …) cond = false
    let b = loop_halts_prop_t(layer, Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), r_e.clone());
    (r_e, a, b)
}

/// The COMPOSED TOTAL-CORRECTNESS theorem TYPE for `layer`:
/// `∀ I R cond body, pres → decrease → ∀ e, I e → And A B` (see
/// [`loop_total_correct_conjuncts_t`]). Port of `mirsem::loop_total_correct_type`.
fn loop_total_correct_type_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    let (_r_e, a, b) = loop_total_correct_conjuncts_t(layer);
    let concl = Expr::apps(cst("And"), [a, b]);
    // inside `∀ I ∀ R ∀ cond ∀ body`: body=0, cond=1, R=2, I=3.
    let pres = preservation_hyp_type_t(layer, &Expr::bvar(3), &Expr::bvar(1), &Expr::bvar(0));
    // after the `pres →` arrow everything +1: body=1, cond=2, R=3, I=4.
    let decrease = decrease_hyp_type_t(layer, &Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1));
    // hI : I e   (e=0 inside `∀ e`, I=6 there)
    let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
    let after_hi = Expr::pi(bd(), i_e, concl);
    let body_e = Expr::pi(bd(), env_ty(), after_hi);
    let after_decrease = Expr::pi(bd(), decrease, body_e);
    let after_pres = Expr::pi(bd(), pres, after_decrease);
    Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(
            bd(),
            env_to_nat_ty(),
            Expr::pi(bd(), cst(TRUSTIR_COND), Expr::pi(bd(), list_body, after_pres)),
        ),
    )
}

/// The COMPOSED TOTAL-CORRECTNESS theorem PROOF for `layer`: `And.intro` of the layer's
/// while-rule (partial, at fuel `R e`) and its rank-termination rule (at the same `e`).
/// `λ I R cond body pres decrease e hI. And.intro A B
///    (<loop_invariant_rule> I cond body pres (R e) e hI)
///    (<loop_rank_terminates> R cond body decrease e)`.
/// Port of `mirsem::loop_total_correct_proof`.
fn loop_total_correct_proof_t(layer: &LoopLayer) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_body = list_body_ty(layer);
    // depth in the body (under λ I λ R λ cond λ body λ pres λ decrease λ e λ hI):
    //   hI=0, e=1, decrease=2, pres=3, body=4, cond=5, R=6, I=7.
    let (r_e, a, b) = loop_total_correct_conjuncts_t(layer);
    // (a) <loop_invariant_rule> I cond body pres (R e) e hI : I (<exec_loop> e cond body (R e))
    let inv_app = Expr::apps(
        cst(layer.loop_invariant_rule),
        [
            Expr::bvar(7), // I
            Expr::bvar(5), // cond
            Expr::bvar(4), // body
            Expr::bvar(3), // pres
            r_e,           // n := R e
            Expr::bvar(1), // e
            Expr::bvar(0), // hI
        ],
    );
    // (b) <loop_rank_terminates> R cond body decrease e
    let term_app = Expr::apps(
        cst(layer.loop_rank_terminates),
        [
            Expr::bvar(6), // R
            Expr::bvar(5), // cond
            Expr::bvar(4), // body
            Expr::bvar(2), // decrease
            Expr::bvar(1), // e
        ],
    );
    // And.intro A B (a) (b)
    let intro = Expr::apps(cst("And.intro"), [a, b, inv_app, term_app]);
    // hI : I e   (e=0 inside `∀ e`, I=6 there)
    let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            env_to_nat_ty(),
            Expr::lam(
                bd(),
                cst(TRUSTIR_COND),
                Expr::lam(
                    bd(),
                    list_body,
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_t(
                            layer,
                            &Expr::bvar(3),
                            &Expr::bvar(1),
                            &Expr::bvar(0),
                        ),
                        Expr::lam(
                            bd(),
                            decrease_hyp_type_t(
                                layer,
                                &Expr::bvar(3),
                                &Expr::bvar(2),
                                &Expr::bvar(1),
                            ),
                            Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, intro)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Register one layer's ENTIRE termination stack (guardFalseStable → boundedHalt →
/// loopRankTerminates → loopTotalCorrect), each kernel-checked with an EMPTY axiom
/// residue. Requires the layer's `stepLoop[S]`/`execLoop[S]`/`loopInvariantRule[S]`
/// (provided by `trustir_anchor::trustir_env`) and `natLeTrans` (registered first here).
fn register_layer_termination_t(env: &mut Environment, layer: &LoopLayer) -> Result<(), String> {
    register_checked_theorem_t(
        env,
        layer.guard_false_stable,
        guard_false_stable_type_t(layer),
        guard_false_stable_proof_t(layer),
    )?;
    register_checked_theorem_t(
        env,
        layer.bounded_halt,
        bounded_halt_type_t(layer),
        bounded_halt_proof_t(layer),
    )?;
    register_checked_theorem_t(
        env,
        layer.loop_rank_terminates,
        loop_rank_terminates_type_t(layer),
        loop_rank_terminates_proof_t(layer),
    )?;
    register_checked_theorem_t(
        env,
        layer.loop_total_correct,
        loop_total_correct_type_t(layer),
        loop_total_correct_proof_t(layer),
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The pure Int/Nat rank-lemma suite under Trust.TrustIr.* names. The TYPE builders and
// the name-INDEPENDENT proof builders are reused from `mirsem.rs` (`pub(crate)`, logic
// byte-identical). Proofs that cross-reference a sibling lemma BY NAME get a
// name-parametric variant HERE (same term modulo the constant name), so no registered
// decl mentions any `Trust.MirSem.*` constant.
// ---------------------------------------------------------------------------

/// Name-parametric port of `mirsem::countdown_rank_decrease_proof` — the `loopRankDecrease`
/// reference is `lrd` (here: [`TRUSTIR_LOOP_RANK_DECREASE`]). See mirsem for the full
/// derivation (`Eq.subst` along `Int.add_zero` over `loopRankDecrease 0 i h`).
fn countdown_rank_decrease_proof_named(lrd: &str) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ (i : Int) λ (h : Int.lt 0 i)`: h=0, i=1.
    let i = || Expr::bvar(1);
    let h = || Expr::bvar(0);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let sub = |a: Expr, b: Expr| Expr::apps(cst("Int.sub"), [a, b]);
    let i_minus_1 = sub(i(), int_one());
    let sub_i_0 = sub(i(), int_lit(0));
    // raw := <lrd> 0 i h : Nat.lt (toNat(i-(0+1))) (toNat(i-0)).
    let raw = Expr::apps(cst(lrd), [int_lit(0), i(), h()]);
    // motive := λ (y : Int). Nat.lt (toNat(i-1)) (toNat y)   (i-1 lifted by 1 under `λ y`).
    let motive =
        Expr::lam(bd(), int_ty(), nat_lt(to_nat(i_minus_1.clone().lift(1)), to_nat(Expr::bvar(0))));
    // h0 := Int.add_zero i : Int.add i 0 = i  (used at def-eq type `Int.sub i 0 = i`).
    let h0 = Expr::app(cst("Int.add_zero"), i());
    // @Eq.subst Int motive (Int.sub i 0) i h0 raw : Nat.lt (toNat(i-1)) (toNat i).
    let body = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), motive, sub_i_0, i(), h0, raw],
    );
    let h_ty = Expr::apps(cst("Int.lt"), [int_lit(0), Expr::bvar(0)]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), h_ty, body))
}

/// Name-parametric port of `mirsem::le_of_ofnat_le_ofnat_proof` — the forward-cast
/// reference is `fwd_cast` (here: [`TRUSTIR_OFNAT_LE_OFNAT_OF_LE`]).
fn le_of_ofnat_le_ofnat_proof_named(fwd_cast: &str) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `λ (m : Nat) λ (p : Nat) λ (h : Int.le (ofNat m)(ofNat p))`: h=0, p=1, m=2.
    let m = || Expr::bvar(2);
    let p = || Expr::bvar(1);
    let succ = |x: Expr| Expr::app(cst("Nat.succ"), x);

    // disc := Nat.le_or_lt m p : Or (Nat.le m p) (Nat.le (succ p) m).
    let lhs_prop = || nat_le(m(), p());
    let rhs_prop = || nat_le(succ(p()), m());
    let disc = Expr::apps(cst("Nat.le_or_lt"), [m(), p()]);

    // motive : λ (_ : Or …). Nat.le m p  (constant; under `λ _or`: m=3, p=2).
    let or_ty = Expr::apps(cst("Or"), [lhs_prop(), rhs_prop()]);
    let motive = Expr::lam(bd(), or_ty, nat_le(Expr::bvar(3), Expr::bvar(2)));

    // inl_minor : λ (hle : Nat.le m p). hle.
    let inl_minor = {
        let hle_ty = nat_le(m(), p());
        Expr::lam(bd(), hle_ty, Expr::bvar(0))
    };

    // inr_minor : λ (hlt : Nat.le (succ p) m). False.elim (Int.lt_irrefl … chain)
    //   under `λ hlt` (on top of h,p,m): hlt=0, h=1, p=2, m=3.
    let inr_minor = {
        let m = || Expr::bvar(3);
        let p = || Expr::bvar(2);
        let h = || Expr::bvar(1);
        let hlt = || Expr::bvar(0);
        let of_succ_p = || int_ofnat(succ(p()));
        let of_m = || int_ofnat(m());
        let of_p = || int_ofnat(p());
        let fwd = Expr::apps(cst(fwd_cast), [succ(p()), m(), hlt()]);
        let chain = Expr::apps(cst("Int.le_trans"), [of_succ_p(), of_m(), of_p(), fwd, h()]);
        // Int.lt_irrefl (ofNat p) : Not (Int.lt (ofNat p)(ofNat p)); chain retypes def-eq.
        let bad = Expr::app(Expr::app(cst("Int.lt_irrefl"), of_p()), chain);
        let false_elim = Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [nat_le(m(), p()), bad],
        );
        // hlt binder type `Nat.le (succ p) m` BEFORE `λ hlt`: p=bvar(1), m=bvar(2).
        let hlt_ty = nat_le(succ(Expr::bvar(1)), Expr::bvar(2));
        Expr::lam(bd(), hlt_ty, false_elim)
    };

    // @Or.rec (Nat.le m p) (Nat.le (succ p) m) motive inl_minor inr_minor disc : Nat.le m p.
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Or.rec"), vec![]),
        [lhs_prop(), rhs_prop(), motive, inl_minor, inr_minor, disc],
    );
    let h_binder_ty = int_le(int_ofnat(Expr::bvar(1)), int_ofnat(Expr::bvar(0)));
    Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), h_binder_ty, rec_app)))
}

/// Name-parametric port of `mirsem::tonat_vacuous_arrow` — the arrow inhabitant
/// `Int.le (ofNat m)(negSucc q) → Nat.le m Nat.zero`, refuting the hypothesis via
/// `fwd_cast` (the forward `ofNat` cast) and `negsucc_lemma` (`negSucc q` is not NonNeg).
fn tonat_vacuous_arrow_named(fwd_cast: &str, negsucc_lemma: &str, m: Expr, q: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let negsucc = |x: Expr| Expr::app(cst("Int.negSucc"), x);
    let subnatnat = |a: Expr, b: Expr| Expr::apps(cst("Int.subNatNat"), [a, b]);
    let succ = |x: Expr| Expr::app(cst("Nat.succ"), x);
    // Under `λ hbad`: hbad=0, m/q lifted by 1.
    let m1 = || m.clone().lift(1);
    let q1 = || q.clone().lift(1);

    // h1 : Int.le (ofNat 0)(ofNat m).
    let h1 =
        Expr::apps(cst(fwd_cast), [cst("Nat.zero"), m1(), Expr::app(cst("Nat.zero_le"), m1())]);
    // h2 : Int.le (ofNat 0)(negSucc q)  (≡ NonNeg (subNatNat 0 (succ q))).
    let h2 = Expr::apps(
        cst("Int.le_trans"),
        [
            int_ofnat(cst("Nat.zero")),
            int_ofnat(m1()),
            negsucc(q1()),
            h1,
            Expr::bvar(0), // hbad
        ],
    );
    // e : Int.subNatNat 0 (succ q) = Int.negSucc q.
    let e = Expr::app(cst("Int.subNatNat_zero_succ"), q1());
    // nn : Int.NonNeg (negSucc q).
    let nonneg_motive = Expr::lam(bd(), int_ty(), Expr::app(cst("Int.NonNeg"), Expr::bvar(0)));
    let nn = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), nonneg_motive, subnatnat(cst("Nat.zero"), succ(q1())), negsucc(q1()), e, h2],
    );
    // bad : False := <negsucc_lemma> q nn.
    let bad = Expr::apps(cst(negsucc_lemma), [q1(), nn]);
    // out : Nat.le m 0 := @False.elim (Nat.le m 0) bad.
    let out = Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [nat_le(m1(), cst("Nat.zero")), bad],
    );
    // hbad binder type `Int.le (ofNat m)(negSucc q)` at depth BEFORE λ hbad (m,q unlifted).
    let hbad_ty = int_le(int_ofnat(m), negsucc(q));
    Expr::lam(bd(), hbad_ty, out)
}

/// Name-parametric port of `mirsem::tonat_vacuous_term` — the inner `Int.rec` `negSucc`
/// minor `λ (q : Nat). <vacuous arrow at q=0, m=2>`.
fn tonat_vacuous_term_named(fwd_cast: &str, negsucc_lemma: &str) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    Expr::lam(
        bd(),
        cst("Nat"),
        tonat_vacuous_arrow_named(fwd_cast, negsucc_lemma, Expr::bvar(2), Expr::bvar(0)),
    )
}

/// Name-parametric port of `mirsem::to_nat_mono_proof` — the converse-cast reference is
/// `le_of_cast` (here: [`TRUSTIR_LE_OF_OFNAT_LE_OFNAT`]); the vacuous branch references
/// `fwd_cast`/`negsucc_lemma`. Outer `@Int.rec.{0}` on `a`, inner on `b`; see mirsem.
fn to_nat_mono_proof_named(le_of_cast: &str, fwd_cast: &str, negsucc_lemma: &str) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let negsucc = |x: Expr| Expr::app(cst("Int.negSucc"), x);

    // Outer motive Ma := λ (x : Int). Int.le x b → Nat.le (toNat x)(toNat b)
    //   under `λ (a : Int) λ (b : Int)`: b=0, a=1; then under `λ x`: x=0, b=1.
    let outer_motive = {
        let dom = int_le(Expr::bvar(0), Expr::bvar(1));
        // cod is UNDER the Pi's (anonymous) domain binder: that binder=0, x=1, b=2.
        let cod = nat_le(to_nat(Expr::bvar(1)), to_nat(Expr::bvar(2)));
        Expr::lam(bd(), int_ty(), Expr::pi(bd(), dom, cod))
    };

    // ofNat minor : λ (m : Nat) λ (hle : Int.le (ofNat m) b). <inner Int.rec on b> hle
    //   under `λ m λ hle` (on top of b,a): hle=0, m=1, b=2, a=3.
    let ofnat_minor = {
        let hle = || Expr::bvar(0);

        // Inner motive Mb := λ (y : Int). Int.le (ofNat m) y → Nat.le m (toNat y)
        //   under `λ y` (on top of hle,m,b,a): y=0, m=2.
        let inner_motive = {
            let dom = int_le(int_ofnat(Expr::bvar(2)), Expr::bvar(0));
            // cod UNDER the Pi's domain binder: that binder=0, y=1, m=3.
            let cod = nat_le(Expr::bvar(3), to_nat(Expr::bvar(1)));
            Expr::lam(bd(), int_ty(), Expr::pi(bd(), dom, cod))
        };

        // inner ofNat minor : λ (p : Nat). <le_of_cast> m p
        //   under `λ p` (on top of hle,m,b,a): p=0, m=2.
        let inner_ofnat_minor = Expr::lam(
            bd(),
            cst("Nat"),
            Expr::apps(cst(le_of_cast), [Expr::bvar(2), Expr::bvar(0)]),
        );

        // inner negSucc minor — the VACUOUS branch (`Int.le (ofNat m)(negSucc q)` refuted).
        let inner_negsucc_minor = tonat_vacuous_term_named(fwd_cast, negsucc_lemma);

        // @Int.rec.{0} inner_motive inner_ofnat_minor inner_negsucc_minor b, applied to hle.
        let inner_rec = Expr::apps(
            Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            [inner_motive, inner_ofnat_minor, inner_negsucc_minor, Expr::bvar(2)],
        );
        let applied = Expr::app(inner_rec, hle());
        // hle binder type `Int.le (ofNat m) b` under `λ m` (before λ hle): m=0, b=1.
        let hle_ty = int_le(int_ofnat(Expr::bvar(0)), Expr::bvar(1));
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), hle_ty, applied))
    };

    // negSucc minor : λ (m : Nat) λ (_ : Int.le (negSucc m) b). Nat.zero_le (toNat b)
    //   under `λ m λ _h` (on top of b,a): _h=0, m=1, b=2, a=3.
    let negsucc_minor = {
        let zero_le = Expr::app(cst("Nat.zero_le"), to_nat(Expr::bvar(2)));
        let h_ty = int_le(negsucc(Expr::bvar(0)), Expr::bvar(1)); // under λ m: m=0, b=1.
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), h_ty, zero_le))
    };

    // @Int.rec.{0} outer_motive ofnat_minor negsucc_minor a.
    let outer_rec = Expr::apps(
        Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
        [outer_motive, ofnat_minor, negsucc_minor, Expr::bvar(1)],
    );
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), outer_rec))
}

/// Name-parametric port of `mirsem::stride_rank_decrease_proof` — `lrd` is the counter
/// decrease lemma ([`TRUSTIR_LOOP_RANK_DECREASE`]), `mono` the `toNat` monotonicity lemma
/// ([`TRUSTIR_TONAT_MONO`]). See mirsem for the derivation chain
/// (`loopRankDecrease` + subtraction-antitone via `toNatMono` + `Nat.lt_of_le_of_lt`).
fn stride_rank_decrease_proof_named(lrd: &str, mono: &str) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Under `λ a λ b λ k λ (hlt : Int.lt a b) λ (hk : Int.le 1 k)`: hk=0, hlt=1, k=2, b=3, a=4.
    let a = || Expr::bvar(4);
    let b = || Expr::bvar(3);
    let k = || Expr::bvar(2);
    let hlt = || Expr::bvar(1);
    let hk = || Expr::bvar(0);
    let to_nat = |x: Expr| Expr::app(cst("Int.toNat"), x);
    let sub = |x: Expr, y: Expr| Expr::apps(cst("Int.sub"), [x, y]);
    let add = |x: Expr, y: Expr| Expr::apps(cst("Int.add"), [x, y]);
    let neg = |x: Expr| Expr::app(cst("Int.neg"), x);
    let a1 = || add(a(), int_one()); // a + 1
    let ak = || add(a(), k()); // a + k
    let sub_b_a1 = || sub(b(), a1()); // b - (a+1)
    let sub_b_ak = || sub(b(), ak()); // b - (a+k)
    let sub_b_a = || sub(b(), a()); // b - a

    // raw := <lrd> a b hlt : Nat.lt (toNat(b-(a+1))) (toNat(b-a)).
    let raw = Expr::apps(cst(lrd), [a(), b(), hlt()]);

    // hadd := Int.add_le_add_left 1 k hk a : Int.le (a+1)(a+k).
    let hadd = Expr::apps(cst("Int.add_le_add_left"), [int_one(), k(), hk(), a()]);

    // E : ((b-(a+1)) - (b-(a+k))) = ((a+k) - (a+1)).
    let e1 = Expr::apps(cst("Int.add_sub_add_left"), [neg(ak()), neg(a1()), b()]);
    let neg_neg_ak = Expr::app(cst("Int.neg_neg"), ak()); // neg(neg(a+k)) = a+k
    let add_fn = {
        // λ (t : Int). Int.add (neg(a+1)) t   under `λ t`: t=0, a lifted (bvar 4 → 5).
        let a_l = Expr::bvar(5);
        let body = add(neg(add(a_l, int_one())), Expr::bvar(0));
        Expr::lam(bd(), int_ty(), body)
    };
    let e2 = congr_arg(int_ty(), int_ty(), neg(neg(ak())), ak(), add_fn, neg_neg_ak);
    let e3 = Expr::apps(cst("Int.add_comm"), [neg(a1()), ak()]);

    let lhs = || sub(sub_b_a1(), sub_b_ak()); // (b-(a+1)) - (b-(a+k))
    let mid1 = || sub(neg(a1()), neg(ak())); // neg(a+1) - neg(a+k)
    let mid2 = || add(neg(a1()), ak()); // neg(a+1) + (a+k)
    let rhs = || sub(ak(), a1()); // (a+k) - (a+1)
    let e23 = eq_trans_int(mid1(), mid2(), rhs(), e2, e3);
    let e_full = eq_trans_int(lhs(), mid1(), rhs(), e1, e23);

    // hsub := @Eq.subst Int NonNeg rhs lhs (Eq.symm E) hadd : Int.le (b-(a+k)) (b-(a+1)).
    let nonneg_motive = Expr::lam(bd(), int_ty(), Expr::app(cst("Int.NonNeg"), Expr::bvar(0)));
    let e_sym = eq_symm_int(lhs(), rhs(), e_full);
    let hsub = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![Level::succ(Level::zero())]),
        [int_ty(), nonneg_motive, rhs(), lhs(), e_sym, hadd],
    );

    // mono := <mono> (b-(a+k)) (b-(a+1)) hsub : Nat.le (toNat(b-(a+k))) (toNat(b-(a+1))).
    let mono_app = Expr::apps(cst(mono), [sub_b_ak(), sub_b_a1(), hsub]);

    // out := Nat.lt_of_le_of_lt (toNat(b-(a+k))) (toNat(b-(a+1))) (toNat(b-a)) mono raw.
    let out = Expr::apps(
        cst("Nat.lt_of_le_of_lt"),
        [to_nat(sub_b_ak()), to_nat(sub_b_a1()), to_nat(sub_b_a()), mono_app, raw],
    );

    // Binder types (evaluated at their OWN depth):
    //   hlt : Int.lt a b   under `λ a λ b λ k`: a=2, b=1.
    let hlt_ty = Expr::apps(cst("Int.lt"), [Expr::bvar(2), Expr::bvar(1)]);
    //   hk : Int.le 1 k    under `λ a λ b λ k λ hlt`: k=1.
    let hk_ty = int_le(int_one(), Expr::bvar(1));
    Expr::lam(
        bd(),
        int_ty(),
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), hlt_ty, Expr::lam(bd(), hk_ty, out))),
        ),
    )
}

/// Register the WHOLE pure Int/Nat rank-lemma suite under `Trust.TrustIr.*` names, each
/// with an EMPTY axiom residue. Requires the constructive Int-order lemma suite
/// (`init_int_ord_lemmas`, already loaded by `trustir_anchor::trustir_env`).
fn register_rank_lemma_suite_t(env: &mut Environment) -> Result<(), String> {
    // The counter decrease lemma (a < b → toNat(b-(a+1)) < toNat(b-a)) — the mirsem
    // type/proof builders are name-independent (prelude constants only) and reused.
    register_checked_theorem_t(
        env,
        TRUSTIR_LOOP_RANK_DECREASE,
        crate::mirsem::loop_rank_decrease_type(),
        crate::mirsem::loop_rank_decrease_proof(),
    )?;
    // The countdown decrease lemma (0 < i → toNat(i-1) < toNat(i)) — references the
    // counter lemma by name ⇒ name-parametric proof.
    register_checked_theorem_t(
        env,
        TRUSTIR_COUNTDOWN_RANK_DECREASE,
        crate::mirsem::countdown_rank_decrease_type(),
        countdown_rank_decrease_proof_named(TRUSTIR_LOOP_RANK_DECREASE),
    )?;
    // toNatMono sub-lemma 1: the forward ofNat cast (name-independent, reused).
    register_checked_theorem_t(
        env,
        TRUSTIR_OFNAT_LE_OFNAT_OF_LE,
        crate::mirsem::ofnat_le_ofnat_of_le_type(),
        crate::mirsem::ofnat_le_ofnat_of_le_proof(),
    )?;
    // toNatMono sub-lemma 2: the converse cast (references sub-lemma 1 by name).
    register_checked_theorem_t(
        env,
        TRUSTIR_LE_OF_OFNAT_LE_OFNAT,
        crate::mirsem::le_of_ofnat_le_ofnat_type(),
        le_of_ofnat_le_ofnat_proof_named(TRUSTIR_OFNAT_LE_OFNAT_OF_LE),
    )?;
    // toNatMono sub-lemma 3: negSucc refutation (name-independent, reused).
    register_checked_theorem_t(
        env,
        TRUSTIR_NEGSUCC_NOT_NONNEG,
        crate::mirsem::negsucc_not_nonneg_type(),
        crate::mirsem::negsucc_not_nonneg_proof(),
    )?;
    // toNatMono itself (references sub-lemmas 2, 1, 3 by name).
    register_checked_theorem_t(
        env,
        TRUSTIR_TONAT_MONO,
        crate::mirsem::to_nat_mono_type(),
        to_nat_mono_proof_named(
            TRUSTIR_LE_OF_OFNAT_LE_OFNAT,
            TRUSTIR_OFNAT_LE_OFNAT_OF_LE,
            TRUSTIR_NEGSUCC_NOT_NONNEG,
        ),
    )?;
    // The stride decrease lemma (references loopRankDecrease + toNatMono by name).
    register_checked_theorem_t(
        env,
        TRUSTIR_STRIDE_RANK_DECREASE,
        crate::mirsem::stride_rank_decrease_type(),
        stride_rank_decrease_proof_named(TRUSTIR_LOOP_RANK_DECREASE, TRUSTIR_TONAT_MONO),
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The termination env — EXTENDS `trustir_anchor::trustir_env()` (never touches an
// existing registration) with natLeTrans + the rank-lemma suite + both layers' stacks.
// ---------------------------------------------------------------------------

/// Register the ENTIRE trust-ir termination theory into `env` (idempotent). Every
/// registration is kernel-checked and audited for an EMPTY axiom residue (fail-closed).
fn register_trustir_termination(env: &mut Environment) -> Result<(), String> {
    register_nat_le_trans_t(env)?;
    register_rank_lemma_suite_t(env)?;
    register_layer_termination_t(env, &BASE_LAYER)?;
    register_layer_termination_t(env, &SELECT_LAYER)?;
    Ok(())
}

/// Build the env the per-function total-correctness instances live in:
/// `trustir_anchor::trustir_env()` (the whole trust-ir denotation + partial-correctness
/// meta-theory, zero MirSem constants) EXTENDED with this module's termination theory.
pub fn trustir_termination_env() -> Result<Environment, String> {
    let mut env = crate::trustir_anchor::trustir_env()?;
    register_trustir_termination(&mut env)?;
    Ok(env)
}

// ---------------------------------------------------------------------------
// Per-function RANKING SYNTHESIS + concrete decrease proofs — port of
// `mirsem::synthesize_counter_ranking` and its per-class ranking/decrease builders,
// dispatched on the trust-ir `IrLoopInvariant` class.
// ---------------------------------------------------------------------------

/// The counter ranking `R := λ (e : Env). Int.toNat (Int.sub (e n_idx) (e i_idx))` —
/// the counter's distance to the bound (`toNat(n − i)`). Port of
/// `mirsem::counter_loop_ranking` (also the stride ranking — the measure is the distance
/// to the bound regardless of stride; `toNat` floors an overshoot to 0).
fn counter_ranking_t(i_idx: u64, n_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `λ (e : Env)`: e = bvar(0).
    let e_at = |idx: u64| Expr::app(Expr::bvar(0), Expr::nat_lit(idx));
    let sub = Expr::apps(cst("Int.sub"), [e_at(n_idx), e_at(i_idx)]);
    Expr::lam(bd(), env_ty(), Expr::app(cst("Int.toNat"), sub))
}

/// The `≤`-guarded counter ranking `R := λ e. Int.toNat (Int.sub ((e bound_idx)+1)
/// (e i_idx))` — the distance to `n+1` (the `while i ≤ n { i := i+1 }` loop runs until
/// `i = n+1`). Port of `mirsem::counter_loop_succ_ranking`.
fn counter_succ_ranking_t(i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_at = |idx: u64| Expr::app(Expr::bvar(0), Expr::nat_lit(idx));
    let b1 = Expr::apps(cst("Int.add"), [e_at(bound_idx), int_one()]);
    let sub = Expr::apps(cst("Int.sub"), [b1, e_at(i_idx)]);
    Expr::lam(bd(), env_ty(), Expr::app(cst("Int.toNat"), sub))
}

/// The countdown ranking `R := λ e. Int.toNat (e i_idx)` — `i` itself (it decreases to 0).
/// Port of `mirsem::countdown_loop_ranking`.
fn countdown_ranking_t(i_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_i = Expr::app(Expr::bvar(0), Expr::nat_lit(i_idx));
    Expr::lam(bd(), env_ty(), Expr::app(cst("Int.toNat"), e_i))
}

/// The CONCRETE decrease PROOF for the counter ranking over an `i := i+1` body under the
/// `Lt` guard: `λ (e)(hg). loopRankDecrease (e i) (e n) <hlt extracted from the guard>`.
/// The result type `Nat.lt (toNat(n-(i+1))) (toNat(n-i))` is def-eq to
/// `Nat.lt (R (<exec> e body)) (R e)` exactly when the body's net effect at `i_idx` is
/// `i+1` and `n_idx` is untouched — the KERNEL verifies that reduction (fail-closed for
/// any other body). Port of `mirsem::counter_loop_decrease_proof` (`cond_expr` is the
/// loop's CLOSED guard value).
fn counter_decrease_proof_t(cond_expr: &Expr, i_idx: u64, n_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ (e : Env) λ (hg : evalCond e cond = true)`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx));
    let e_n = Expr::app(Expr::bvar(1), Expr::nat_lit(n_idx));
    // p := Int.lt (e i)(e n) ; inst := Int.decLt (e i)(e n) — the guard `evalCond e (i<n)`
    // is def-eq `decide p inst`, so `of_decide_eq_true p inst hg : p`.
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i.clone(), e_n.clone()]);
    let hlt = Expr::apps(crate::trustir_anchor::of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]);
    let body = Expr::apps(cst(TRUSTIR_LOOP_RANK_DECREASE), [e_i, e_n, hlt]);
    // guard hypothesis type `evalCond e cond = true` (under `λ e`): e=0.
    let guard_eq = eq_bool_true(eval_cond_app_t(Expr::bvar(0), cond_expr.clone()));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The decrease PROOF for the `≤`-guarded `+1` loop's ranking `R := toNat((n+1)-i)`:
/// extract `i ≤ n` from the `Le` guard, add 1 on both sides (`Int.add_le_add_right`) ⇒
/// `i < n+1`, close with `loopRankDecrease i (n+1)`. Port of
/// `mirsem::counter_loop_le_decrease_proof`.
fn counter_le_decrease_proof_t(cond_expr: &Expr, i_idx: u64, bound_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ e λ hg`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx));
    let e_n = Expr::app(Expr::bvar(1), Expr::nat_lit(bound_idx));
    let b1 = Expr::apps(cst("Int.add"), [e_n.clone(), int_one()]);
    // Extract `i ≤ n` from the Le guard, then add 1 on both sides ⇒ `i+1 ≤ n+1` ≡ `i < n+1`.
    let p = Expr::apps(cst("Int.le"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLe"), [e_i.clone(), e_n.clone()]);
    let hg = Expr::apps(crate::trustir_anchor::of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // i ≤ n
    let hlt = add_le_add_right(e_i.clone(), e_n, hg, int_one()); // i+1 ≤ n+1 ≡ i < n+1
    let body = Expr::apps(cst(TRUSTIR_LOOP_RANK_DECREASE), [e_i, b1, hlt]);
    let guard_eq = eq_bool_true(eval_cond_app_t(Expr::bvar(0), cond_expr.clone()));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The decrease PROOF for the countdown ranking `R := toNat(i)`:
/// `λ (e)(hg). countdownRankDecrease (e i) <hlt: 0 < i>` — the `Gt` guard's evalCond is
/// the SWAPPED `decide (Int.lt 0 (e i))`. Port of `mirsem::countdown_loop_decrease_proof`.
fn countdown_decrease_proof_t(cond_expr: &Expr, i_idx: u64) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ e λ hg`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx));
    let zero = int_lit(0);
    let p = Expr::apps(cst("Int.lt"), [zero.clone(), e_i.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [zero, e_i.clone()]);
    let hlt = Expr::apps(crate::trustir_anchor::of_decide_eq_true_term(), [p, inst, Expr::bvar(0)]); // 0 < i
    let body = Expr::apps(cst(TRUSTIR_COUNTDOWN_RANK_DECREASE), [e_i, hlt]);
    let guard_eq = eq_bool_true(eval_cond_app_t(Expr::bvar(0), cond_expr.clone()));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// The decrease PROOF for the STRIDE loop `while i < n { i := i + k }` (`k ≥ 1`):
/// `λ (e)(hg). strideRankDecrease (e i) (e n) (int_lit k) <hlt: i<n> <hk: 1≤k>`, where
/// `hk` is the CLOSED decidable literal fact (`decide` on `1 ≤ k` reduces to `true`, so
/// `Eq.refl Bool.true` retypes). Port of `mirsem::stride_loop_decrease_proof`.
fn stride_decrease_proof_t(cond_expr: &Expr, i_idx: u64, n_idx: u64, k: i128) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ (e : Env) λ (hg : evalCond e cond = true)`: hg=0, e=1.
    let e_i = Expr::app(Expr::bvar(1), Expr::nat_lit(i_idx));
    let e_n = Expr::app(Expr::bvar(1), Expr::nat_lit(n_idx));
    let k_lit = int_lit(k); // Int.ofNat k (k ≥ 1)
    // hlt : Int.lt (e i)(e n) — extracted from the `Lt` guard.
    let p_lt = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst_lt = Expr::apps(cst("Int.decLt"), [e_i.clone(), e_n.clone()]);
    let hlt =
        Expr::apps(crate::trustir_anchor::of_decide_eq_true_term(), [p_lt, inst_lt, Expr::bvar(0)]);
    // hk : Int.le 1 k — a CLOSED decidable literal fact.
    let p_le = int_le(int_one(), k_lit.clone());
    let inst_le = Expr::apps(cst("Int.decLe"), [int_one(), k_lit.clone()]);
    let refl_true = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), cst("Bool.true")],
    );
    let hk =
        Expr::apps(crate::trustir_anchor::of_decide_eq_true_term(), [p_le, inst_le, refl_true]);
    let body = Expr::apps(cst(TRUSTIR_STRIDE_RANK_DECREASE), [e_i, e_n, k_lit, hlt, hk]);
    let guard_eq = eq_bool_true(eval_cond_app_t(Expr::bvar(0), cond_expr.clone()));
    Expr::lam(bd(), env_ty(), Expr::lam(bd(), guard_eq, body))
}

/// If `cond` is the `Lt (Var i) (Var n)` guard, return `(i, n)` (fail-closed `None`
/// otherwise) — the guard-based `(counter, bound)` recovery
/// `mirsem::recognize_counter_loop` performs on the guard leaf.
fn lt_guard_vars(cond: &IrCond) -> Option<(u64, u64)> {
    if cond.op != TrustIrCmpOp::Lt {
        return None;
    }
    let IrOperand::Var(i) = cond.a else { return None };
    let IrOperand::Var(n) = cond.b else { return None };
    if i == n {
        return None;
    }
    Some((i, n))
}

/// SYNTHESIZE the well-founded ranking for the trust-ir loop `lp` — the termination
/// measure is INFERRED from the certified invariant CLASS + the guard structure, exactly
/// mirroring `mirsem::synthesize_counter_ranking`'s shape-aware dispatch; the kernel then
/// VERIFIES the decrease (synthesis PROPOSES, the kernel VERIFIES). Returns
/// `(ranking, decrease_proof)`, or `None` for any class/guard the heuristic does not
/// recognize (fail-closed: no ranking proposed ⇒ no termination claimed).
fn synthesize_ir_counter_ranking(lp: &IrLoop) -> Option<(Expr, Expr)> {
    let cond_expr = lp.cond_expr();
    match &lp.inv {
        // COUNTER upper bound `i ≤ n` (also the CounterInRange→upper projection): the
        // `Lt`-guard `+1` loop. The invariant's indices must agree with the guard's.
        IrLoopInvariant::CounterLeBound { i_idx, bound_idx } => {
            let (gi, gn) = lt_guard_vars(&lp.cond)?;
            if gi != *i_idx || gn != *bound_idx {
                return None;
            }
            let ranking = counter_ranking_t(gi, gn);
            let decrease = counter_decrease_proof_t(&cond_expr, gi, gn);
            Some((ranking, decrease))
        }
        // COUNTER lower bound `c ≤ i` (the CounterInRange→lower projection, `count_up`):
        // termination is via the SAME `Lt` guard; the bound index is recovered from it.
        IrLoopInvariant::CounterGeConst { i_idx, .. } => {
            let (gi, gn) = lt_guard_vars(&lp.cond)?;
            if gi != *i_idx {
                return None;
            }
            let ranking = counter_ranking_t(gi, gn);
            let decrease = counter_decrease_proof_t(&cond_expr, gi, gn);
            Some((ranking, decrease))
        }
        // COUNTDOWN `while i > 0 { i := i-1 }`: ranking toNat(i).
        IrLoopInvariant::CountdownGeConst { i_idx, .. } => {
            if lp.cond.op != TrustIrCmpOp::Gt
                || lp.cond.a != IrOperand::Var(*i_idx)
                || lp.cond.b != IrOperand::Const(0)
            {
                return None;
            }
            let ranking = countdown_ranking_t(*i_idx);
            let decrease = countdown_decrease_proof_t(&cond_expr, *i_idx);
            Some((ranking, decrease))
        }
        // STRIDE `while i < n { i := i+k }` (k ≥ 1): ranking toNat(n − i), decrease via
        // `strideRankDecrease`. A non-positive `k` proposes NO ranking (fail-closed).
        IrLoopInvariant::StrideGeConst { i_idx, k, .. } => {
            let (gi, gn) = lt_guard_vars(&lp.cond)?;
            if gi != *i_idx || *k < 1 {
                return None;
            }
            let ranking = counter_ranking_t(gi, gn);
            let decrease = stride_decrease_proof_t(&cond_expr, gi, gn, *k);
            Some((ranking, decrease))
        }
        // ACCUMULATOR lower bound `c ≤ s`: the invariant is about `s`, TERMINATION is via
        // the GUARD counter (recovered from the `Lt` guard, exactly as MirSem takes the
        // accumulator class's `(i_idx, n_idx)`); the other body statements leave the
        // counter untouched so the counter decrease retypes through the multi-stmt exec.
        IrLoopInvariant::AccumGeConst { .. } => {
            let (gi, gn) = lt_guard_vars(&lp.cond)?;
            let ranking = counter_ranking_t(gi, gn);
            let decrease = counter_decrease_proof_t(&cond_expr, gi, gn);
            Some((ranking, decrease))
        }
        // RELATIONAL accumulator(s) `(s == i) ∧ i ≤ n` / `(⋀ₖ aₖ == i) ∧ i ≤ n`: the
        // ranking measures only the counter `i` (the invariant's pinned indices).
        IrLoopInvariant::AccumEqCounter { i_idx, n_idx, .. }
        | IrLoopInvariant::AccumEqCounterSet { i_idx, n_idx, .. } => {
            let ranking = counter_ranking_t(*i_idx, *n_idx);
            let decrease = counter_decrease_proof_t(&cond_expr, *i_idx, *n_idx);
            Some((ranking, decrease))
        }
        // `≤`-GUARDED conjoined range `c ≤ i ∧ i ≤ n+1` (`count_le`): ranking
        // toNat((n+1) − i), decrease from the `Le` guard.
        IrLoopInvariant::CounterInRangeSucc { i_idx, bound_idx, .. } => {
            if lp.cond.op != TrustIrCmpOp::Le
                || lp.cond.a != IrOperand::Var(*i_idx)
                || lp.cond.b != IrOperand::Var(*bound_idx)
            {
                return None;
            }
            let ranking = counter_succ_ranking_t(*i_idx, *bound_idx);
            let decrease = counter_le_decrease_proof_t(&cond_expr, *i_idx, *bound_idx);
            Some((ranking, decrease))
        }
    }
}

// ---------------------------------------------------------------------------
// The per-function `loopTotalCorrect[S]` INSTANCE: conclusion type, proof, check.
// ---------------------------------------------------------------------------

/// The per-function TOTAL-CORRECTNESS CONCLUSION TYPE — the layer's `loopTotalCorrect`
/// SPECIALIZED at the concrete `(I, R, cond, body)` after feeding `pres`/`decrease`:
/// `∀ (e : Env), I e → And (I (<exec_loop> e cond body (R e)))
///                          (evalCond (<exec_loop> e cond body (R e)) cond = false)`.
/// Port of `mirsem::loop_total_instance_conclusion_type` (layer-parametric).
fn total_instance_conclusion_type_t(
    layer: &LoopLayer,
    i_expr: &Expr,
    cond_expr: &Expr,
    body_expr: &Expr,
    ranking: &Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // ∀ (e:Env), I e → And A B   (A,B at fuel `R e`).
    //   under `∀ e`: e=0. `I e`: I lifted +1.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    //   under `∀ e` + `I e →`: e=1.
    let r_e = Expr::app(ranking.clone().lift(2), Expr::bvar(1)); // R e
    let looped = exec_loop_app_t(
        layer,
        Expr::bvar(1),
        cond_expr.clone().lift(2),
        body_expr.clone().lift(2),
        r_e,
    );
    let a = Expr::app(i_expr.clone().lift(2), looped.clone());
    let b = eq_bool_false(eval_cond_app_t(looped, cond_expr.clone().lift(2)));
    let and_ab = Expr::apps(cst("And"), [a, b]);
    let after_hi = Expr::pi(bd(), i_e, and_ab);
    Expr::pi(bd(), env_ty(), after_hi)
}

/// The per-function TOTAL-CORRECTNESS PROOF — the layer's general `loopTotalCorrect`
/// theorem APPLIED at the concrete `(I, R, cond, body, pres, decrease)`. Type-checking
/// this application at the conclusion type IS the per-function corollary. Port of
/// `mirsem::loop_total_instance_proof`.
fn total_instance_proof_t(
    layer: &LoopLayer,
    i_expr: Expr,
    ranking: Expr,
    cond_expr: Expr,
    body_expr: Expr,
    pres: Expr,
    decrease: Expr,
) -> Expr {
    Expr::apps(
        cst(layer.loop_total_correct),
        [i_expr, ranking, cond_expr, body_expr, pres, decrease],
    )
}

/// Shared kernel gate: `check_type` the instance proof at the conclusion, register under
/// `decl_name`, and audit the residue. Fail-closed at every step; `ProvenModulo3` IFF the
/// registered decl's axiom residue is EMPTY.
fn check_total_instance_decl(decl_name: &str, concl_ty: Expr, proof: Expr) -> RefinementVerdict {
    let mut env = match trustir_termination_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("{decl_name} check_type: {e:?}"));
        }
    }
    let name = Name::from_string(decl_name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add {decl_name}: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(format!("{decl_name} decl not found")),
    }
}

/// Kernel-check the per-function BASE-layer total-correctness instance for `lp` with the
/// PROVIDED `ranking`/`decrease` (the fail-closed hook the wrong-ranking probe uses; the
/// production entry [`check_loop_total_correct_instance`] SYNTHESIZES both).
fn check_loop_total_correct_instance_inner(
    lp: &IrLoop,
    ranking: &Expr,
    decrease: &Expr,
) -> RefinementVerdict {
    let i_expr = lp.invariant_expr(None);
    let cond_expr = lp.cond_expr();
    let body_expr = lp.body_expr();
    // The SAME preservation proof the PRIMARY (partial-correctness) witness certifies.
    let pres = crate::trustir_anchor::loop_instance_preservation_proof_ir(lp);
    let concl_ty =
        total_instance_conclusion_type_t(&BASE_LAYER, &i_expr, &cond_expr, &body_expr, ranking);
    let proof = total_instance_proof_t(
        &BASE_LAYER,
        i_expr,
        ranking.clone(),
        cond_expr,
        body_expr,
        pres,
        decrease.clone(),
    );
    check_total_instance_decl(
        "Trust.TrustIr.Refinement.loop_total_correct_instance",
        concl_ty,
        proof,
    )
}

/// Kernel-check (modulo 3) the per-function TOTAL-CORRECTNESS instance for the trust-ir
/// loop `lp`: the ranking is SYNTHESIZED from the certified invariant class
/// ([`synthesize_ir_counter_ranking`] — counter `toNat(n−i)`, countdown `toNat(i)`,
/// `≤`-guarded `toNat((n+1)−i)`, stride via `strideRankDecrease`), the decrease proof is
/// CONCRETE and kernel-verified, and the composed `Trust.TrustIr.loopTotalCorrect` is
/// applied at the loop's `(I, R, cond, body, pres, decrease)`. The proved theorem is
///
///   `∀ (e : Env), I e → And (I (execLoop e cond body (R e)))
///                            (evalCond (execLoop e cond body (R e)) cond = false)`
///
/// — TOTAL correctness on the TRUST-IR denotation: the invariant holds AT the halting
/// state AND the loop HALTS within `R e` guarded steps. This is the trust-ir RELOCATION
/// of `mirsem::check_loop_total_correct_instance` (the §6 via-trustir gate's Lane-T
/// termination clause). FAIL-CLOSED: an unrecognized invariant class / guard shape
/// proposes no ranking (KernelRejected, never a guess); a WRONG ranking's decrease does
/// not retype (KernelRejected); a non-empty axiom residue is never `ProvenModulo3`.
#[must_use]
pub fn check_loop_total_correct_instance(lp: &IrLoop) -> RefinementVerdict {
    let Some((ranking, decrease)) = synthesize_ir_counter_ranking(lp) else {
        return RefinementVerdict::KernelRejected(
            "trust-ir ranking synthesis did not recognize the loop class/guard shape".to_string(),
        );
    };
    check_loop_total_correct_instance_inner(lp, &ranking, &decrease)
}

/// Kernel-check (modulo 3) the per-function TOTAL-CORRECTNESS instance for the trust-ir
/// CONDITIONAL-UPDATE loop `lp` on the SELECT layer (`execLoopS`): ranking
/// `R := toNat(n − i)` with `(i, n)` from the `Lt` guard (`i` must be the certified
/// counter `lp.i_idx`); the `Sel` statement leaves `i`/`n` untouched, so the SAME
/// `loopRankDecrease` decrease retypes through `execS` — mirroring how MirSem's
/// `loop_total_correct_witness` handles `max_scan` (the `CondUpdateGeConst` arm of
/// `synthesize_counter_ranking`). Applied via `Trust.TrustIr.loopTotalCorrectS` with the
/// SAME `cond_update_preservation_proof_ir` the PRIMARY witness certifies. The proved
/// theorem is
///
///   `∀ (e : Env), I e → And (I (execLoopS e cond body (R e)))
///                            (evalCond (execLoopS e cond body (R e)) cond = false)`.
///
/// This instance ELIMINATES the in-path MirSem termination residue from
/// `prove::cond_update_fully_faithful_via_trustir` clause (e). FAIL-CLOSED: a non-`Lt`
/// guard / mismatched counter declines before the kernel; a body whose net effect at the
/// counter is not `+1` (or which writes the bound) makes the decrease ill-typed ⇒
/// KernelRejected.
#[must_use]
pub fn check_cond_update_total_correct_instance(lp: &IrCondUpdateLoop) -> RefinementVerdict {
    let Some((gi, gn)) = lt_guard_vars(&lp.cond) else {
        return RefinementVerdict::KernelRejected(
            "cond-update termination requires the `Lt (Var i) (Var n)` guard".to_string(),
        );
    };
    if gi != lp.i_idx {
        return RefinementVerdict::KernelRejected(
            "cond-update termination: the guard counter is not the certified counter".to_string(),
        );
    }
    if gn == lp.m_idx {
        return RefinementVerdict::KernelRejected(
            "cond-update termination: the guard bound is the conditionally-updated \
             accumulator (not a stable bound)"
                .to_string(),
        );
    }
    let ranking = counter_ranking_t(gi, gn);
    let cond_expr = lp.cond_expr();
    let decrease = counter_decrease_proof_t(&cond_expr, gi, gn);
    let i_expr = lp.invariant_expr(None);
    let body_expr = lp.body_expr();
    // The SAME preservation proof the PRIMARY (partial-correctness) witness certifies.
    let pres = crate::trustir_anchor::cond_update_preservation_proof_ir(lp);
    let concl_ty =
        total_instance_conclusion_type_t(&SELECT_LAYER, &i_expr, &cond_expr, &body_expr, &ranking);
    let proof = total_instance_proof_t(
        &SELECT_LAYER,
        i_expr,
        ranking,
        cond_expr,
        body_expr,
        pres,
        decrease,
    );
    check_total_instance_decl(
        "Trust.TrustIr.Refinement.cond_update_total_correct_instance",
        concl_ty,
        proof,
    )
}

// ---------------------------------------------------------------------------
// Tests — house style (see trustir_anchor's trustir_loop_postcondition_* tests):
// positive instances per loop class, NEGATIVE fail-closed controls, and the
// general-theorem axiom-closure registration probe.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trustir_anchor::{IrRvalue, IrSStmt, IrStmt, TrustIrBinOp};

    /// The canonical `count_to` counter loop `while i < n { i := i+1 }` over env indices
    /// `i = 3`, `n = 1`, carrying the guard-aware upper bound `i ≤ n` — the SAME shape as
    /// `trustir_anchor::example_count_to_loop`.
    fn count_to_loop() -> IrLoop {
        IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
            }],
            inv: IrLoopInvariant::CounterLeBound { i_idx: 3, bound_idx: 1 },
        }
    }

    /// The canonical `countdown` loop `while i > 0 { i := i-1 }` over `i = 3` with the
    /// inductive lower bound `0 ≤ i`.
    fn countdown_loop() -> IrLoop {
        IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(3), b: IrOperand::Const(0) },
            body: vec![IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Sub, IrOperand::Var(3), IrOperand::Const(1)),
            }],
            inv: IrLoopInvariant::CountdownGeConst { i_idx: 3, c: 0 },
        }
    }

    /// The STRIDE loop `while i < n { i := i+k }` over `i = 3`, `n = 1` with `c ≤ i`.
    fn stride_loop(k: i128) -> IrLoop {
        IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(k)),
            }],
            inv: IrLoopInvariant::StrideGeConst { i_idx: 3, c: 0, k },
        }
    }

    /// The relational accumulator loop `while i < n { s := s+1; i := i+1 }` over
    /// `s = 4`, `i = 3`, `n = 1`.
    fn accum_loop(inv: IrLoopInvariant) -> IrLoop {
        IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![
                IrStmt {
                    idx: 4,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(4),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(3),
                        IrOperand::Const(1),
                    ),
                },
            ],
            inv,
        }
    }

    /// The `≤`-guarded `count_le` loop `while i ≤ n { i := i+1 }` over `i = 3`, `n = 1`
    /// with the conjoined range `0 ≤ i ∧ i ≤ n+1`.
    fn count_le_loop() -> IrLoop {
        IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Le, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![IrStmt {
                idx: 3,
                rvalue: IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
            }],
            inv: IrLoopInvariant::CounterInRangeSucc { i_idx: 3, c: 0, bound_idx: 1 },
        }
    }

    /// The `three` general-relational-set loop `while i < n { a:=a+1; b:=b+1; i:=i+1 }`
    /// over `a = 4`, `b = 5`, `i = 3`, `n = 1`.
    fn three_loop() -> IrLoop {
        IrLoop {
            cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![
                IrStmt {
                    idx: 4,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(4),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 5,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(5),
                        IrOperand::Const(1),
                    ),
                },
                IrStmt {
                    idx: 3,
                    rvalue: IrRvalue::Bin(
                        TrustIrBinOp::Add,
                        IrOperand::Var(3),
                        IrOperand::Const(1),
                    ),
                },
            ],
            inv: IrLoopInvariant::AccumEqCounterSet { accum_idxs: vec![4, 5], i_idx: 3, n_idx: 1 },
        }
    }

    /// The canonical `max_scan` cond-update loop `while i < n { m := if i>m {i} else {m};
    /// i := i+1 }` over `i = 3`, `m = 4`, `n = 1` — the SAME shape as
    /// `trustir_anchor::example_max_scan_loop(3, 4, 1)`.
    fn max_scan_loop() -> IrCondUpdateLoop {
        IrCondUpdateLoop {
            cond: IrCond { op: TrustIrCmpOp::Lt, a: IrOperand::Var(3), b: IrOperand::Var(1) },
            body: vec![
                IrSStmt::Sel(
                    4,
                    IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(3), b: IrOperand::Var(4) },
                    IrOperand::Var(3),
                    IrOperand::Var(4),
                ),
                IrSStmt::Assign(
                    3,
                    IrRvalue::Bin(TrustIrBinOp::Add, IrOperand::Var(3), IrOperand::Const(1)),
                ),
            ],
            m_idx: 4,
            c: 0,
            i_idx: 3,
        }
    }

    /// REGISTRATION probe: the ENTIRE ported termination theory — both layers' general
    /// theorems (`guardFalseStable[S]`/`boundedHalt[S]`/`loopRankTerminates[S]`/
    /// `loopTotalCorrect[S]`), `natLeTrans`, and the full rank-lemma suite — registers
    /// with an axiom closure ⊆ the 3 foundational axioms (EMPTY residue per decl; the
    /// residue audit runs inside every registration, so a 4th axiom anywhere fails env
    /// construction). Also asserts the trust-ir env's zero-MirSem separation holds: no
    /// registered termination decl name mentions `MirSem`.
    #[test]
    fn trustir_termination_general_theorems_modulo3() {
        let env = trustir_termination_env().expect("termination theory must register modulo 3");
        for n in [
            TRUSTIR_NAT_LE_TRANS,
            TRUSTIR_LOOP_RANK_DECREASE,
            TRUSTIR_COUNTDOWN_RANK_DECREASE,
            TRUSTIR_OFNAT_LE_OFNAT_OF_LE,
            TRUSTIR_LE_OF_OFNAT_LE_OFNAT,
            TRUSTIR_NEGSUCC_NOT_NONNEG,
            TRUSTIR_TONAT_MONO,
            TRUSTIR_STRIDE_RANK_DECREASE,
            TRUSTIR_GUARD_FALSE_STABLE,
            TRUSTIR_BOUNDED_HALT,
            TRUSTIR_LOOP_RANK_TERMINATES,
            TRUSTIR_LOOP_TOTAL_CORRECT,
            TRUSTIR_GUARD_FALSE_STABLE_S,
            TRUSTIR_BOUNDED_HALT_S,
            TRUSTIR_LOOP_RANK_TERMINATES_S,
            TRUSTIR_LOOP_TOTAL_CORRECT_S,
        ] {
            assert!(!n.contains("MirSem"), "zero-MirSem separation violated by {n}");
            let residue = env
                .axiom_deps(&Name::from_string(n))
                .unwrap_or_else(|| panic!("decl not found: {n}"));
            assert!(
                residue.is_empty(),
                "{n} must rest on ⊆ the 3 foundational axioms; residue: {residue:?}",
            );
        }
    }

    /// POSITIVE (counter, the `count_to` shape): the synthesized ranking `toNat(n − i)`
    /// closes the trust-ir total-correctness instance modulo 3.
    #[test]
    fn trustir_loop_total_correct_counter_modulo3() {
        assert_eq!(
            check_loop_total_correct_instance(&count_to_loop()),
            RefinementVerdict::ProvenModulo3,
            "counter loop total-correctness instance did not prove modulo 3",
        );
    }

    /// POSITIVE (countdown): ranking `toNat(i)` via `countdownRankDecrease`.
    #[test]
    fn trustir_loop_total_correct_countdown_modulo3() {
        assert_eq!(
            check_loop_total_correct_instance(&countdown_loop()),
            RefinementVerdict::ProvenModulo3,
            "countdown loop total-correctness instance did not prove modulo 3",
        );
    }

    /// POSITIVE (stride k = 2): ranking `toNat(n − i)` via `strideRankDecrease`
    /// (`toNatMono`-based).
    #[test]
    fn trustir_loop_total_correct_stride2_modulo3() {
        assert_eq!(
            check_loop_total_correct_instance(&stride_loop(2)),
            RefinementVerdict::ProvenModulo3,
            "stride(k=2) loop total-correctness instance did not prove modulo 3",
        );
    }

    /// POSITIVE (accumulator, BOTH classes): the lower-bound `AccumGeConst` (counter
    /// recovered from the guard) and the relational `AccumEqCounter` (counter pinned by
    /// the invariant) — the counter decrease retypes through the 2-statement body.
    #[test]
    fn trustir_loop_total_correct_accum_modulo3() {
        assert_eq!(
            check_loop_total_correct_instance(&accum_loop(IrLoopInvariant::AccumGeConst {
                s_idx: 4,
                c: 0,
            })),
            RefinementVerdict::ProvenModulo3,
            "accumulator (lower-bound) total-correctness instance did not prove modulo 3",
        );
        assert_eq!(
            check_loop_total_correct_instance(&accum_loop(IrLoopInvariant::AccumEqCounter {
                s_idx: 4,
                i_idx: 3,
                n_idx: 1,
            })),
            RefinementVerdict::ProvenModulo3,
            "relational accumulator total-correctness instance did not prove modulo 3",
        );
    }

    /// POSITIVE (`≤`-guarded `count_le`): ranking `toNat((n+1) − i)` from the `Le` guard.
    #[test]
    fn trustir_loop_total_correct_count_le_modulo3() {
        assert_eq!(
            check_loop_total_correct_instance(&count_le_loop()),
            RefinementVerdict::ProvenModulo3,
            "`≤`-guarded loop total-correctness instance did not prove modulo 3",
        );
    }

    /// POSITIVE (general relational set, the `three` shape): the counter decrease
    /// retypes through the 3-statement body.
    #[test]
    fn trustir_loop_total_correct_accum_set_modulo3() {
        assert_eq!(
            check_loop_total_correct_instance(&three_loop()),
            RefinementVerdict::ProvenModulo3,
            "general relational set total-correctness instance did not prove modulo 3",
        );
    }

    /// POSITIVE (S-layer, the `max_scan` shape): `loopTotalCorrectS` over `execLoopS`
    /// with ranking `toNat(n − i)` — the `Sel` statement leaves the counter/bound
    /// untouched so the counter decrease retypes through `execS`. This is the instance
    /// that ELIMINATES the in-path MirSem termination residue from
    /// `prove::cond_update_fully_faithful_via_trustir`.
    #[test]
    fn trustir_cond_update_total_correct_max_scan_modulo3() {
        assert_eq!(
            check_cond_update_total_correct_instance(&max_scan_loop()),
            RefinementVerdict::ProvenModulo3,
            "max_scan (S-layer) total-correctness instance did not prove modulo 3",
        );
    }

    /// NEGATIVE (WRONG ranking): claim the NON-decreasing measure `toNat(i − n)` for the
    /// increment loop (it is 0 while i < n and does NOT strictly drop). The conclusion is
    /// built AT the wrong ranking; the honest decrease proof (for `toNat(n − i)`) does
    /// not retype against it ⇒ the kernel MUST reject. Proves the instance is GENUINE
    /// (the ranking is verified, not trusted).
    #[test]
    fn trustir_loop_total_correct_wrong_ranking_fails_closed() {
        let lp = count_to_loop();
        let Some((_honest_ranking, honest_decrease)) = synthesize_ir_counter_ranking(&lp) else {
            panic!("the count_to shape must synthesize a ranking");
        };
        // The WRONG ranking: toNat((e i) − (e n)) — indices swapped ⇒ non-decreasing.
        let wrong_ranking = counter_ranking_t(1, 3);
        assert!(
            matches!(
                check_loop_total_correct_instance_inner(&lp, &wrong_ranking, &honest_decrease),
                RefinementVerdict::KernelRejected(_)
            ),
            "a non-decreasing ranking MUST be kernel-rejected",
        );
    }

    /// NEGATIVE (stride k < 1): a zero/negative stride never proposes a ranking — the
    /// loop `while i < n { i := i+0 }` does NOT terminate, and the synthesis declines
    /// fail-closed (KernelRejected, never a guess).
    #[test]
    fn trustir_loop_total_correct_stride_lt_one_declines() {
        for k in [0, -1] {
            assert!(
                matches!(
                    check_loop_total_correct_instance(&stride_loop(k)),
                    RefinementVerdict::KernelRejected(_)
                ),
                "stride k={k} MUST decline fail-closed",
            );
        }
    }

    /// NEGATIVE (guard/class mismatch): a counter class whose invariant indices do not
    /// match the guard proposes no ranking (the `Lt` guard names `(3, 1)`, the claimed
    /// counter is 2) — declines BEFORE the kernel, fail-closed.
    #[test]
    fn trustir_loop_total_correct_guard_mismatch_declines() {
        let lp = IrLoop {
            inv: IrLoopInvariant::CounterLeBound { i_idx: 2, bound_idx: 1 },
            ..count_to_loop()
        };
        assert!(
            matches!(check_loop_total_correct_instance(&lp), RefinementVerdict::KernelRejected(_)),
            "a guard/invariant index mismatch MUST decline fail-closed",
        );
    }

    /// NEGATIVE (S-layer guard mismatch): a cond-update loop whose guard counter is not
    /// the certified counter declines fail-closed.
    #[test]
    fn trustir_cond_update_total_correct_guard_mismatch_declines() {
        let lp = IrCondUpdateLoop { i_idx: 5, ..max_scan_loop() };
        assert!(
            matches!(
                check_cond_update_total_correct_instance(&lp),
                RefinementVerdict::KernelRejected(_)
            ),
            "a cond-update guard/counter mismatch MUST decline fail-closed",
        );
    }
}
