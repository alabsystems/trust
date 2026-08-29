// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **R2 WF EQUATION PROBES — the probes-first battery for WELL-FOUNDED
//! recursion, measured BEFORE any R2 emitter arm or gate exists.**
//!
//! R1 (`r1_equation_probes.rs`) settled structural recursion: the §6e
//! IMPLEMENTATION AMENDMENT's abstract-ih judgment, in three components
//! (per-minor-premise defeq s3, recursive-argument identity s4, kernel-sourced
//! completeness s5), landed as `gate::check_faithful_equations`. R2 is the
//! seam that gate explicitly refuses: a `WellFounded.fix`-headed side A.
//! `recursion_boundary_probes.rs` r4 pinned that such a def is KERNEL-HOLDABLE
//! and that a closed application reduces; `gate.rs`'s
//! `NotStructuralRecursor` refusal names "kernel-checked equation lemmas" as
//! R2's prerequisite. **This file measures whether that prerequisite is real.
//! It is not.**
//!
//! # WHAT THIS FILE IS EVIDENCE ABOUT — read this before citing a row
//!
//! **Every side A here is a RAW KERNEL TERM this file assembles by hand. That
//! makes each row a true statement about what the KERNEL accepts, and none of
//! them a statement about what the ELABORATOR emits.** The two are different
//! questions and this lane learned the difference expensively.
//!
//! Measured 2026-08-22 and written up in
//! `docs/audits/2026-08-22-r2-wf-call-lane-unreachable.md`: `recognise_wf_nat_rec`
//! was built against the spellings in w1 below, and w1's `countdownSum` mirror
//! is hand-built. The real elaborator produces a DIFFERENT tree at three sites
//! — a surface `LT.lt`/`instLTNat` guard, an `instDecidableNatLt` instance, and
//! a surface `HSub.hSub`/`instHSubNat` predecessor — so the recognizer read
//! NOTHING a user could write, and the lane's own driver fixture
//! (`tests/ui/trust/clean_origin_wf_rec.rs`) failed to compile with `E0425`
//! while this file was entirely green. It was green about the kernel, which is
//! what it measures.
//!
//! **`tests/r2_session_probes.rs` is the file that measures the elaborator.**
//! Its side A comes from `CleanIslandSession::check_all`, the pipeline
//! `clean_origin_mir` actually drives. Add an elaborator claim there; add a
//! kernel claim here. Nothing below is weakened or deleted — w1's spine
//! spelling, w2's equation boundary, w6's F-layer defeq and w7's decrease
//! finding are all still exactly what they say they are, and w6/w7 in
//! particular are the reason the F-layer gate needs no equation route at all.
//!
//! One consequence worth stating: w1 pins the ETA-EXPANDED six-argument spine.
//! Measured in `r2_session_probes`, every source-elaborated body is ETA-
//! CONTRACTED (no outer lambda, five arguments), so the expanded arm of both
//! the recognizer and the gate is reachable only from a hand-built term — i.e.
//! from this file. It is kept, because it costs nothing and eta is definitional
//! here, but it is not the arm the compiler runs.
//!
//! # AMENDMENT 2026-08-25 — w10's soundness pin rested on a claim the kernel
//! # cannot support, and has been replaced by two that it decides
//!
//! `probe_w10_the_elaborators_functional_is_the_same_function` used to pin the
//! wrong-else control with **the SUCC equation**:
//!
//! ```text
//! .expect_err("SOUNDNESS PIN: the wrong-else sibling must REFUSE the same equation")
//! ```
//!
//! **That pin asserts a refusal the kernel has no grounds to produce, and it is
//! red at the current clean HEAD.** `f (succ k) = succ k + f k` is STRUCTURALLY
//! INSENSITIVE to the else arm: `0 < succ k` is DECIDABLY TRUE, so the `dite`
//! takes the then-branch on both sides of the equation and the else value never
//! appears in either term. Re-measured at the kernel before this edit, at open
//! `k` (the table is the measurement, not a recollection of one):
//!
//! | claim | correct sibling | wrong-else sibling | discriminates? |
//! |---|---|---|---|
//! | succ equation `f (succ k) = succ k + f k` | ADMIT | **ADMIT** | **NO** |
//! | succ equation, else value 7 instead of 1 | — | **ADMIT** | **NO** |
//! | **zero equation `f 0 = 0`** | ADMIT | **REFUSED** (`TypeMismatch`) | **YES** |
//! | **closed values `f 0/1/3/5`** | `0/1/6/15` | `1/2/7/16` | **YES** |
//! | F-layer defeq vs the delta-spelled `F` | ADMIT | **REFUSED** | **YES** |
//! | `plan_clean_origin_body` shape | same as delta | **DIFFERENT** | **YES** |
//!
//! So the red is the honest reading, and any green there would have been the
//! accident. The pin is replaced by the ZERO equation AND the closed-value rows
//! — the two claims whose statement actually REACHES the else arm — and the
//! succ equation is kept as an ADMIT on the real spelling, now asserted in BOTH
//! directions as a MEASURED NON-DISCRIMINATOR rather than deleted, so the
//! negative result is on the record where the next reader will look for it.
//!
//! **Nothing was weakened: the wrong-else sibling is still REFUSED by four
//! layers** — the F-layer defeq and the planner shape comparison (both already
//! in the probe, both still passing, and both untouched by this amendment), the
//! zero equation, and every closed-value row. The generalisable rule, since
//! this is a soundness-pin failure mode and not a typo: **a control mutation is
//! only pinned by a claim whose statement REACHES the mutated branch.** w2 puts
//! the same succ equation to `cds` vs `cds_mut` and it IS a discriminator there
//! — because that mutation lives in the THEN arm. Pick the equation by which
//! arm the mutation is in, and if no equation reaches it, pin it with a closed
//! value or at the F layer.
//!
//! # THE HEADLINE (2026-08-21, this file's assertions ARE the record)
//!
//! **The per-constructor user equations of a single-parameter WF def ARE
//! `rfl`-definitional at an OPEN argument in this kernel — the expectation
//! going in ("fix is stuck on `Acc.rec` at an open argument") is wrong — but
//! the fully-open `.eq_def` unfolding equation is NOT, and the boundary
//! between them is measured exactly.**
//!
//! The mechanism (w3), in two layers:
//!
//! 1. **Layer one always fires.** Clean's `Nat.accNatLt` is a
//!    `Declaration::Theorem` whose VALUE is `Acc.intro`-headed; `whnf`
//!    delta-unfolds it even at a completely open argument, so `Acc.rec`
//!    iota-fires and `WellFounded.fix` peels one layer at ANY argument.
//!    Measured directly: `whnf (cds <open n>)` reaches `Decidable.rec`
//!    (stuck only on `Nat.decLt 0 n`), and the same `.eq_def` equation with a
//!    NON-RECURSIVE `F` closes by rfl at a fully open `n`.
//! 2. **Layer two needs a constructor-headed argument.** The witness layer one
//!    threads into the recursive occurrence is `Nat.lt_wfLBound n y p`, whose
//!    own proof recurses on the BOUND `n`: at `n := succ k` it reduces to
//!    `Acc.intro` (so the recursion keeps unfolding and the per-constructor
//!    equation is rfl); at a fully open `n` it sticks at `Nat.rec`. A
//!    user-level equation spells the recursive occurrence with the CANONICAL
//!    witness `Nat.accNatLt y`, and re-canonicalizing is exactly what is not
//!    definitional — the one missing proposition, stated in full in w4.
//!
//! **None of this blocks R2**, because the gate w5–w7 derives never states an
//! equation: it compares the functional `F`, where no accessibility witness
//! appears at all.
//!
//! # The measured table
//!
//! | # | question | verdict |
//! |---|---|---|
//! | w0 | WF machinery in `with_prelude` | `Acc`/`Acc.intro`/`Acc.rec`/`WellFounded`/`WellFounded.intro`/`fixF`/`fix`/`Nat.lt_wf`/`Nat.accNatLt`/`Nat.lt_wfLBound`/`dite`/`Nat.decLt`/`Nat.sub_lt`/`Nat.le.refl` PRESENT; **`WellFounded.fixFEq`, `Acc.inv`, `WellFounded.recursion`, `WellFoundedRelation`, `SizeOf`, `invImage`, `measure`, `Nat.lt_wfRel`, `Nat.strongRecOnLt` ABSENT** — every one of them exists as SOURCE in clean-kernel but under `#[cfg(test)]` (`env/wf_recursion_support/{mod,fix_support}.rs`, `env/nat_strong_rec_lt.rs`), so it is compiled out of the production prelude this crate links |
//! | w1 | a single-parameter WF def admits, raw-kernel mirror of the island's `countdownSum` lowering | ADMIT — spine spelling pinned: `@WellFounded.fix.{1,1}` with SIX explicit args in the order `[α=Nat, C=fun _ => Nat, r=Nat.lt, hwf, F, x=bvar 0]`, `F = fun (x : Nat) (rec : (y : Nat) → Nat.lt y x → Nat) => …`; all three witness spellings (`Nat.lt_wf`, inline `WellFounded.intro Nat Nat.lt Nat.accNatLt`, a REDUCIBLE-`Definition` twin) and the eta-expanded relation admit and are mutually defeq |
//! | w2 | **THE CENTRAL QUESTION** — user equations at an OPEN argument | **per-constructor `∀ k, cds (succ k) = succ k + cds k`: ADMIT by bare `Eq.refl`.** Fully-open `.eq_def` (`∀ n, cds n = dite (0 < n) (fun h => n + cds (n-1)) (fun _ => 0)`): **REFUSED** — and the isolating control (same shape, non-recursive `F`) ADMITS, so the refusal is about the recursive occurrence's witness, not about `fix` being stuck. Mutations (wrong value, flipped addends, non-decreasing RHS) REFUSE |
//! | w2 | closed instances | `cds 0/1/3/5 ≡ 0/1/6/15`, both numeral lanes; mutations refuse |
//! | w3 | the mechanism | `whnf(Nat.accNatLt <open>)` = `Acc.intro`-headed (layer 1); `whnf(Nat.lt_wfLBound (succ k) k _)` = `Acc.intro` but `whnf(Nat.lt_wfLBound <open> y p)` = `Nat.rec` STUCK (layer 2's boundary); proof irrelevance identifies distinct proofs of one Prop, and NOT across props or recursion points |
//! | w4 | which unfolding lemma is missing, exactly | `fixFEq` form A (witness spelled as the reduction produces it): **rfl ADMIT**. Form B (canonical witness `Nat.accNatLt y`): **REFUSED**. The gap is exactly one proposition — `fixF F x a = fixF F x b` for `a b : Acc r x` — and `Acc.inv`/`fixFEq` would then need lifting out of `#[cfg(test)]`. **R2's gate needs neither** |
//! | w5 | is side A's `F` extractable by a spine parse? | YES — a 40-line parse; refuses a `Nat.rec`-headed body, a wrong level list, a wrong arity |
//! | w6 | F-layer defeq | correct independently-built F ADMITS; the defeq-equal `Nat.pred x` spelling of the MIR-faithful `Nat.sub x 1` ADMITS; wrong-VALUE F (extra `succ`, swapped addends, wrong else-branch) REFUSES — and F-agreement implies whole-body agreement by congruence (measured both directions) |
//! | w7 | **THE DECREASE QUESTION** | the F TYPE forces it: `rec : (y : Nat) → Nat.lt y x → C y`, so a non-decreasing self-call is REFUSED BY TYPE-CHECKING (`TypeMismatch`), not by any gate component. The escape is an AXIOM: with `axiom bogus : ∀ x, Nat.lt (succ x) x` in scope the diverging F kernel-checks. And defeq at the F layer refuses a well-typed, genuinely-decreasing but DIFFERENT argument (`x-2` vs `x-1`) |
//! | w8 | today's gate on a WF side A | `check_faithful_equations` → `NotStructuralRecursor` naming `WellFounded.fix` + "equation lemmas" (the latter is now MEASURED-WRONG as a prerequisite; the note must be re-worded when R2 lands). `check_faithful` — the WHOLE-TERM lane — ADMITS a WF side A today, with a wrong-F sibling refused: the whole-term gate is not WF-blind, it is only missing a side-B producer for the fix term |
//! | w10 | **the spelling this file was WRONG about** — every helper above builds side A from `Nat.lt` / `Nat.decLt` / `Nat.sub`, and the elaborator mints NONE of those | the TYPECLASS spellings (`@LT.lt.{0} Nat instLTNat 0 x`, `instDecidableNatLt 0 x`, `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat x (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))`) are δι-EQUAL to the delta-unfolded ones at an OPEN argument, the whole typeclass-spelled `countdownSum` is F-layer defeq to this file's `cds` and computes the same closed values — and a FOREIGN `LT` / `HSub` instance is NOT defeq, so the identification is a δ-step and not a collapse. w10b puts the same question to the REAL island elaborator |
//!
//! # WHAT THIS MEANS FOR R2's GATE (stated as a delta from R1's three components)
//!
//! R1's judgment = (1) per-minor-premise defeq with the recursive result held
//! abstract + (2) the recursive-argument identity + (3) equation-set
//! completeness read from the kernel's inductive declaration.
//!
//! For a `WellFounded.fix` side A, measured:
//!
//! * **(1) survives, and simplifies to ONE comparison.** There are no minor
//!   premises; there is one functional `F`, and its recursive slot `rec` is
//!   ALREADY an abstract binder of side A's own term — the abstract-ih
//!   discipline is structural here rather than imposed. Component 1 becomes
//!   "kernel defeq of side B's `F` against side A's `F`" (w6).
//! * **(2) DISSOLVES into typing.** R1 needed a separate argument-identity
//!   check because `Nat.rec`'s minor premise supplies `ih : Res` with the
//!   recursive ARGUMENT erased — nothing in the minor's type records which
//!   argument the emission recursed on, so the off-by-one was invisible to
//!   the case-value comparison (s2/s4). In a WF spine the argument is not
//!   erased: `rec y p : C y` mentions `y`, and `p : Nat.lt y x` mentions it
//!   again. Two consequences, both measured: a wrong argument is caught by
//!   DEFEQ (w6/w7 d3, even against a decreasing alternative), and a
//!   NON-DECREASING argument is caught by TYPE-CHECKING (w7 d1) — the
//!   divergence catch is the kernel's typing rule, not a gate component.
//!   **The replacement obligation is not "check the argument decreases" but
//!   "side B's `F` must KERNEL-CHECK at side A's `F` TYPE, and the proof
//!   terms occupying its `Nat.lt y x` slots must have an audited-empty axiom
//!   closure"** — because an axiom is the only way a non-decreasing call
//!   type-checks (w7 d4). The axiom-closure machinery for that already
//!   exists on the mint lane (`mint.rs`, `AxiomClosure::is_audited_empty`);
//!   what is new is that it must cover side B's proof slots, not only side A.
//! * **(3) DISSOLVES.** Completeness was "one reflected case per kernel minor
//!   premise". A WF lowering has no case family: `F` is a total function of
//!   `x`, and its internal case split lives INSIDE the term the defeq
//!   comparison already covers (w6's else-branch mutation is refused with no
//!   completeness check anywhere). Nothing is read from `get_inductive` /
//!   `get_recursor` on this lane.
//! * **NEW, and R2-specific: the witness is not side B's problem.** The three
//!   accessibility-witness spellings are mutually defeq (w1) and the F-layer
//!   factorization never touches the witness. A whole-term R2 gate would
//!   force side B to MINT an accessibility proof from MIR — which MIR does
//!   not contain. The F-layer gate does not, which is why R2's gate should be
//!   `parse the fix spine, compare F`, not `compare the whole term`.
//!
//! So R2's gate is a THREE-part check that is not R1's three parts:
//! **(a) side A's spine parses as `@WellFounded.fix.{1,1} α C r hwf F x` with
//! `x` the parameter (w5); (b) side B's `F` kernel-checks AT SIDE A's `F`
//! TYPE with an audited-empty axiom closure (w7); (c) kernel defeq of the two
//! `F`s (w6).** Equation lemmas appear nowhere — and that is the point: w2
//! measures that the equation route has a real boundary (the fully-open
//! `.eq_def` form is not definitional) and w4 states the exact proposition
//! that route would cost, while the F-layer route crosses no such boundary
//! because no accessibility witness ever enters the comparison.
//!
//! # HONESTY RULES (identical to `r1_equation_probes.rs`)
//!
//! * A probe that REFUSES asserts the refusal. A probe that ADMITS asserts
//!   admission. No probe passes vacuously; every ADMIT is paired with a
//!   refused mutation at the same layer.
//! * The kernel terms are RAW-KERNEL MIRRORS of the island elaborator's
//!   measured output (`recursion_boundary_probes.rs`, the `countdownSum` row:
//!   `@WellFounded.fix.{1,1} Nat (fun _ => Nat) (fun a b => Nat.lt a b)
//!   (WellFounded.intro … Acc.rec … Nat.accNatLt …) (fun x rec => dite …)`),
//!   built by hand because trust-clean-origin does not (and must not) depend
//!   on the elaborator. Deviations from the island's exact spelling are
//!   MEASURED to be defeq-immaterial in w1, not assumed.
//! * **An equation that cites the defined CONSTANT is a side-A fact, never a
//!   gate.** R1's s2 measured the constant-citing spelling admitting a
//!   diverging body; that lesson carries over unchanged, which is why w2's
//!   equations are recorded as *properties of side A* and R2's gate (w5–w7)
//!   never states one.
//! * Side B's producers and the kernel are FROZEN against this lane: if a
//!   verdict here is not the one an R2 design wants, the fix is kernel/prelude
//!   work or a different gate — never an edit to this fixture's assertions.

use clean_kernel::{
    BinderInfo, ConstantKind, Declaration, Environment, Expr, ExprKind, Level, Name, TypeChecker,
};
use trust_clean_origin::gate::{
    GateRefusal, ReflectedCase, ReflectedStructuralRec, check_faithful, check_faithful_equations,
};
use trust_clean_origin::plan_clean_origin_body;

// ───────────────────────── helpers (R1's conventions) ─────────────────────────

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// Succ-tree numeral `Nat.succ^k Nat.zero`.
fn nat_num(k: u64) -> Expr {
    let mut e = cnst("Nat.zero");
    for _ in 0..k {
        e = Expr::app(cnst("Nat.succ"), e);
    }
    e
}

fn succ(x: Expr) -> Expr {
    Expr::app(cnst("Nat.succ"), x)
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.add"), [a, b])
}

/// `Nat.sub a b` — the DELTA-UNFOLDED subtraction, hand-built.
///
/// **This is not what the elaborator mints for the surface `n - 1`.** It mints
/// `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat a b` ([`hsub_tc`]), and the two
/// are one denotation only because `instHSubNat`'s value IS `Nat.sub` — a fact
/// this file did not measure until w10, and whose absence let the R2 recognizer
/// refuse the exact text its own diagnostic advertised. Every helper in this
/// section is a hand-built spelling; w10/w10b are where that is checked against
/// reality rather than assumed.
fn sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.sub"), [a, b])
}

/// `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat a b` — the TYPECLASS spelling of
/// [`sub`], and the one a surface `n - 1` actually elaborates to.
fn hsub_tc(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("HSub.hSub"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        [nat(), nat(), nat(), cnst("instHSubNat"), a, b],
    )
}

/// `@OfNat.ofNat.{0} Nat <k> (instOfNatNat <k>)` — the surface numeral, as
/// distinct from [`nat_num`]'s succ tower and from a bare `Nat` literal.
fn surface_num(k: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [nat(), Expr::nat_lit(k), Expr::app(cnst("instOfNatNat"), Expr::nat_lit(k))],
    )
}

/// `Nat.lt a b` — the DELTA-UNFOLDED order, hand-built. See [`sub`]: the
/// elaborator mints [`lt_tc`] for a surface `a < b`.
fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.lt"), [a, b])
}

/// `@LT.lt.{0} <alpha> <instance> a b` — the TYPECLASS order, with the type
/// argument and the instance left OPEN so w10 can put a foreign instance and a
/// non-`Nat` carrier to the kernel as controls.
fn lt_tc_with(alpha: Expr, instance: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [alpha, instance, a, b],
    )
}

/// `@LT.lt.{0} Nat instLTNat a b` — the prelude spelling of [`lt_tc_with`].
fn lt_tc(a: Expr, b: Expr) -> Expr {
    lt_tc_with(nat(), cnst("instLTNat"), a, b)
}

fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![lvl1()]), [nat(), lhs, rhs])
}

fn refl_nat(x: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]), [nat(), x])
}

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    try_define(env, name, type_, value)
        .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e}"));
}

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

fn try_theorem(env: &mut Environment, name: &str, prop: Expr, proof: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: prop,
        value: proof,
    })
    .map_err(|e| format!("{e:?}"))
}

fn has(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

// ─────────────────── the WF spine, exactly as the island builds it ───────────

/// `(y : Nat) → Nat.lt y X → Nat` — `F`'s recursive slot. `x_under_y` is X as
/// seen from UNDER the `y` binder (already shifted by one).
fn rec_ty(x_under_y: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), Expr::arrow(nat_lt(Expr::bvar(0), x_under_y), nat()))
}

/// `fun (n : Nat) => @WellFounded.fix.{1,1} Nat (fun _ => Nat) r hwf F n` —
/// the raw-kernel mirror of the WF lowering (`recursion_boundary_probes.rs`,
/// the `countdownSum` row; binder order per
/// `clean-kernel/src/env/algebra_advanced/well_founded.rs`: `{α} {C} {r} hwf
/// F x`).
fn wf_body_with(rel: Expr, hwf: Expr, f: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("WellFounded.fix"), vec![lvl1(), lvl1()]),
            [nat(), Expr::lam(BinderInfo::Default, nat(), nat()), rel, hwf, f, Expr::bvar(0)],
        ),
    )
}

fn wf_body(f: Expr) -> Expr {
    wf_body_with(cnst("Nat.lt"), cnst("Nat.lt_wf"), f)
}

/// `@Nat.le.refl 1 : Nat.le 1 1 ≡ Nat.lt 0 1` — the `0 < 1` side condition
/// `Nat.sub_lt` needs. (`Nat.le.refl`'s `{n}` is implicit at the surface; in
/// raw kernel terms it is an ordinary argument.)
fn one_pos() -> Expr {
    Expr::app(cnst("Nat.le.refl"), nat_num(1))
}

/// `Nat.le.step (Nat.le.refl 1) : Nat.le 1 2 ≡ Nat.lt 0 2`.
fn two_pos() -> Expr {
    Expr::apps(cnst("Nat.le.step"), [nat_num(1), nat_num(1), one_pos()])
}

/// `F` for `countdownSum` — the ISLAND's shape, in raw kernel terms:
///
/// ```text
/// fun (x : Nat) (rec : (y : Nat) → Nat.lt y x → Nat) =>
///   @dite.{1} Nat (Nat.lt 0 x) (Nat.decLt 0 x)
///     (fun (h : Nat.lt 0 x) => Nat.add x (rec ARG PRF))
///     (fun (_ : Not (Nat.lt 0 x)) => ELSE)
/// ```
///
/// `then_call` is built in the scope `[x, rec, h]` (so `x = bvar 2`,
/// `rec = bvar 1`, `h = bvar 0`); `else_value` in `[x, rec, _]`.
fn cds_f(then_call: Expr, else_value: Expr) -> Expr {
    let c_at = |x: Expr| nat_lt(cnst("Nat.zero"), x);
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
                    c_at(Expr::bvar(1)),
                    Expr::apps(cnst("Nat.decLt"), [cnst("Nat.zero"), Expr::bvar(1)]),
                    Expr::lam(BinderInfo::Default, c_at(Expr::bvar(1)), then_call),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::app(cnst("Not"), c_at(Expr::bvar(1))),
                        else_value,
                    ),
                ],
            ),
        ),
    )
}

/// The correct then-branch: `Nat.add x (rec (Nat.sub x 1) (Nat.sub_lt x 1 h 0<1))`,
/// in the scope `[x, rec, h]`.
fn cds_then_correct() -> Expr {
    let x = || Expr::bvar(2);
    let rec = || Expr::bvar(1);
    let h = || Expr::bvar(0);
    add(
        x(),
        Expr::apps(
            rec(),
            [
                sub(x(), nat_num(1)),
                Expr::apps(cnst("Nat.sub_lt"), [x(), nat_num(1), h(), one_pos()]),
            ],
        ),
    )
}

/// The canonical side A: `countdownSum n = if 0 < n then n + countdownSum (n-1) else 0`.
fn install_cds(env: &mut Environment, name: &str) {
    define(
        env,
        name,
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(cds_then_correct(), cnst("Nat.zero"))),
    );
}

// ─────────────────── the F-layer spine parse (probe w5's subject) ────────────

/// The six components of a `WellFounded.fix` side A.
#[derive(Debug)]
struct FixSpine {
    alpha: Expr,
    motive: Expr,
    rel: Expr,
    hwf: Expr,
    f: Expr,
}

/// R2's candidate side-A parse: peel one lambda over `Nat`, uncurry, require
/// `@WellFounded.fix.{1,1}` with six arguments whose major premise is the
/// parameter. Deliberately written HERE and not in `gate.rs`: this file
/// measures whether such a parse is possible before any gate is designed.
fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    e
}

fn parse_wf_fix_spine(body: &Expr) -> Result<FixSpine, String> {
    let strip = strip_mdata;
    let cursor = strip(body);
    let ExprKind::Lam(_, param_ty, inner) = cursor.kind() else {
        return Err("not a one-parameter lambda".to_owned());
    };
    if !matches!(strip(param_ty).kind(), ExprKind::Const(n, l) if *n == Name::from_string("Nat") && l.is_empty())
    {
        return Err("a lambda over a non-Nat parameter".to_owned());
    }
    let mut head = strip(inner);
    let mut args: Vec<&Expr> = Vec::new();
    while let ExprKind::App(function, argument) = head.kind() {
        args.push(strip(argument));
        head = strip(function);
    }
    args.reverse();
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return Err("a non-constant application head".to_owned());
    };
    if *head_name != Name::from_string("WellFounded.fix") {
        return Err(format!("an application headed by `{head_name}`"));
    }
    if head_levels.as_slice() != [lvl1(), lvl1()] {
        return Err(format!("`WellFounded.fix` at unexpected levels {head_levels:?}"));
    }
    if args.len() != 6 {
        return Err(format!("a fix spine with {} argument(s) where 6 were required", args.len()));
    }
    if !matches!(args[5].kind(), &ExprKind::BVar(0)) {
        return Err("a fix whose major premise is not the parameter".to_owned());
    }
    Ok(FixSpine {
        alpha: args[0].clone(),
        motive: args[1].clone(),
        rel: args[2].clone(),
        hwf: args[3].clone(),
        f: args[4].clone(),
    })
}

// ═══════════════ (w0) what the production prelude actually holds ═══════════════

/// The R2 analogue of `recursion_boundary_probes` r2, extended to the
/// UNFOLDING machinery. The load-bearing half is the ABSENCES: every absent
/// name below EXISTS as source in clean-kernel and is compiled out —
/// `Acc.inv` / `WellFounded.fixFEq` / `WellFounded.recursion` /
/// `WellFoundedRelation` / `SizeOf` / `invImage` / `measure` / `Nat.lt_wfRel`
/// live under `#[cfg(test)]` in
/// `clean-kernel/src/env/wf_recursion_support/{mod,fix_support}.rs`
/// (`init_wf_recursion_support` is itself `#[cfg(test)]`, so nothing in
/// `with_prelude` can call it), and `Nat.strongRecOnLt` likewise in
/// `env/nat_strong_rec_lt.rs`. A crate that LINKS clean-kernel — this one,
/// and the compiler — therefore sees none of them.
///
/// If any ABSENT row flips, someone lifted a `#[cfg(test)]`: re-measure w4
/// before assuming the R2 story changed, because w2/w3 say R2 does not need
/// these declarations at all.
#[test]
fn probe_w0_wf_prelude_inventory() {
    let env = Environment::with_prelude();

    // PRESENT — the substrate a WF lowering rides.
    for name in [
        "Nat.rec",
        "Acc",
        "Acc.intro",
        "Acc.rec",
        "WellFounded",
        "WellFounded.intro",
        "WellFounded.fix",
        "WellFounded.fixF",
        "Nat.lt_wf",
        "Nat.accNatLt",
        "Nat.lt_wfLBound",
        "Nat.lt",
        "Nat.le",
        "Nat.le.refl",
        "Nat.le.step",
        "Nat.lt_succ_self",
        "Nat.sub_lt",
        "Nat.pred_le",
        "Nat.succ_le_succ",
        "Nat.sub",
        "Nat.pred",
        "Nat.zero_le",
        "dite",
        "ite",
        "Not",
        "Decidable",
        "Decidable.casesOn",
        "Nat.decLt",
        "Nat.decLe",
        "Nat.ble",
        "Nat.beq",
        "Nat.eq_of_beq_eq_true",
    ] {
        assert!(has(&env, name), "with_prelude must carry `{name}`");
    }

    // ABSENT — the unfolding/measure machinery. Source exists; `#[cfg(test)]`.
    for name in [
        "Acc.inv",
        "WellFounded.fixFEq",
        "WellFounded.recursion",
        "WellFoundedRelation",
        "WellFoundedRelation.rel",
        "SizeOf",
        "sizeOf",
        "invImage",
        "measure",
        "Nat.lt_wfRel",
        "Nat.strongRecOnLt",
    ] {
        assert!(
            !has(&env, name),
            "measured 2026-08-21: `{name}` is NOT in the production prelude (it is \
             `#[cfg(test)]` source in clean-kernel). It has appeared — re-measure w4"
        );
    }

    // The `down`-shaped island refusal's missing bridge, named precisely: the
    // Bool-test spelling (`if n == 0 …`) yields `Not (Nat.beq n 0 = true)` in
    // the else branch, and turning THAT into `Nat.lt 0 n` needs a positivity
    // bridge the prelude does not carry (`Nat.pos_of_ne_zero` /
    // `Nat.ne_of_beq_eq_false`). This is the kernel-side counterpart of the
    // island's measured `down` rejection ("no decreasing proof was found …
    // tried: hypothesis lookup, Nat.sub_lt, omega, simp_arith"): the
    // DECIDABLE-hypothesis spelling (`if h : 0 < n`) hands the cascade
    // `Nat.sub_lt` directly, which is why `countdownSum` admits and `down`
    // does not.
    // RE-MEASURED 2026-08-22, honouring this probe's own instruction ("if it
    // lands, re-measure whether the island's `down` rejection still holds").
    // `Nat.pos_of_ne_zero` LANDED — proved by `Nat.rec`, axiom closure EMPTY,
    // on the gcd-bool-spelling lane — so the kernel half of this row flips.
    //
    // The lane's measurement corrected this comment's own diagnosis TWICE, and
    // both corrections are kept because they are the useful part:
    //   * `Nat.ne_of_beq_eq_false` was never the bridge. `n == 0` inside an
    //     `if` elaborates to `@BEq.beq Nat (instBEqOfDecidableEq …) n 0`, which
    //     never mentions `Nat.beq`; the kernel REJECTS
    //     `(n == 0) = Nat.beq n 0` as a type mismatch. A `Nat.beq`-shaped
    //     bridge would have matched nothing. It remains absent, correctly.
    //   * A bridge theorem ALONE could never have sufficed: a non-dependent
    //     `ite` binds no hypothesis, so nothing existed for a bridge to
    //     consume. The load-bearing piece is an `ite`->`dite` normalization
    //     (Lean's own WF.Ite step), whose faithfulness is DEFINITIONAL and is
    //     asserted sibling-side by an `rfl` fixture.
    assert!(
        has(&env, "Nat.pos_of_ne_zero"),
        "re-measured 2026-08-22: the positivity bridge LANDED (axiom-free, \
         proved by Nat.rec) — the kernel half of the `down` gap is closed"
    );
    assert!(
        !has(&env, "Nat.ne_of_beq_eq_false"),
        "measured 2026-08-22: still absent, and correctly so — it is not the \
         bridge this spelling needs (the elaboration yields BEq.beq, not Nat.beq)"
    );
    // THE ISLAND-SIDE CLAIM IS NOW MEASURED, AND THE REJECTION IS GONE.
    // This note used to say the island verdict "needs a rebuilt trustc" and
    // instructed the next stage2 build to re-measure. That was wrong about the
    // instrument, which is the part worth keeping: an island verdict needs
    // `trust_certify::clean_island::CleanIslandSession`, a library this crate
    // already carries as a dev-dependency, NOT the stage2 binary — so the
    // measurement was available the whole time and the standing instruction
    // pointed at a build nobody needed to run.
    //
    // Re-measured 2026-08-22 through that session, from this tree
    // (`r2_session_probes::probe_p5_down_elaborates_but_refuses_at_the_call_lane`):
    // **with `termination_by n` present, the Bool-tested `down` island
    // ELABORATES AND KERNEL-CHECKS.** The rejection recorded above ("no
    // decreasing proof was found … tried: hypothesis lookup, Nat.sub_lt, omega,
    // simp_arith") no longer reproduces; `Nat.pos_of_ne_zero` landing is what
    // closed it, exactly as the paragraph above predicted.
    //
    // The CALL side is a SEPARATE question, and p5 answers it: `down` refuses,
    // at the guard. Its guard is
    // `Eq Bool (BEq.beq Nat (instBEqOfDecidableEq Nat instDecidableEqNat) n 0) Bool.true`
    // under `instDecidableEqBool` — a different PROPOSITION rather than a
    // different spelling of `0 < n` — and its branch POLARITY is inverted (the
    // `then` arm is the zero case). Admitting it is its own landing, with its
    // own producer arm and its own mutation controls.

    // The two declarations w3's mechanism turns on, by KIND.
    let acc = env.get_const(&Name::from_string("Nat.accNatLt")).expect("Nat.accNatLt");
    assert_eq!(
        acc.kind,
        ConstantKind::Theorem,
        "MEASURED: `Nat.accNatLt` is a THEOREM (proof-carrying), not a Definition — \
         and w3 measures that whnf unfolds it anyway"
    );
    assert!(acc.value.is_some(), "and it carries its proof term");
    let wf = env.get_const(&Name::from_string("Nat.lt_wf")).expect("Nat.lt_wf");
    assert_eq!(wf.kind, ConstantKind::Definition, "MEASURED: `Nat.lt_wf` is a Definition");

    eprintln!(
        "PROBE-ROW | w0 WF prelude inventory      | PRESENT: Acc/Acc.rec/WellFounded.fix/fixF/\
         Nat.lt_wf/Nat.accNatLt/dite/Nat.decLt/Nat.sub_lt | ABSENT: fixFEq, Acc.inv, \
         WellFounded.recursion, WellFoundedRelation, SizeOf, invImage, measure, \
         Nat.lt_wfRel, Nat.strongRecOnLt (all `#[cfg(test)]` source)"
    );
}

// ═══════ (w1) the WF def admits; the elaborated spelling is PINNED ═══════

/// The raw-kernel mirror of the island's `countdownSum` lowering ADMITS, and
/// this probe pins the spelling the R2 gate will have to parse:
///
/// * head `WellFounded.fix` at level params `[1, 1]`;
/// * SIX explicit arguments, in the order `α`, `C`, `r`, `hwf`, `F`, `x` —
///   `{α} {C} {r}` implicit at the surface are ordinary leading arguments in
///   raw kernel terms (`well_founded.rs`'s `fix_type` binder order);
/// * `x` is the definition's own parameter (`bvar 0`);
/// * `F : (x : Nat) → ((y : Nat) → Nat.lt y x → Nat) → Nat` — **the recursive
///   slot is a FUNCTION OVER `r`-PREDECESSORS CARRYING THE PROOF**, which is
///   the fact w7 turns on.
///
/// The island writes the relation eta-expanded (`fun a b => Nat.lt a b`) and
/// the witness inline (`WellFounded.intro … Acc.rec … Nat.accNatLt …`) rather
/// than as the constants used here. Both deviations are MEASURED
/// defeq-immaterial: all three witness spellings admit, compute the same
/// closed values, and are mutually defeq — including a REDUCIBLE-`Definition`
/// twin of the `Theorem` `Nat.accNatLt`, which is the control that w3's
/// mechanism does not secretly depend on the Theorem/Definition distinction.
#[test]
fn probe_w1_wf_def_admits_and_spine_spelling_pinned() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");

    // (a) the island's inline witness spelling.
    let intro_witness = Expr::apps(
        Expr::const_(Name::from_string("WellFounded.intro"), vec![lvl1()]),
        [nat(), cnst("Nat.lt"), cnst("Nat.accNatLt")],
    );
    define(
        &mut env,
        "cds_intro",
        Expr::arrow(nat(), nat()),
        wf_body_with(
            cnst("Nat.lt"),
            intro_witness.clone(),
            cds_f(cds_then_correct(), cnst("Nat.zero")),
        ),
    );

    // (b) the eta-expanded relation spelling the island emits.
    let eta_rel = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), nat_lt(Expr::bvar(1), Expr::bvar(0))),
    );
    define(
        &mut env,
        "cds_eta",
        Expr::arrow(nat(), nat()),
        wf_body_with(eta_rel, cnst("Nat.lt_wf"), cds_f(cds_then_correct(), cnst("Nat.zero"))),
    );

    // (c) a REDUCIBLE Definition twin of the accessibility witness —
    //     `fun n => Acc.intro n (fun m h => Nat.lt_wfLBound n m h)`, which is
    //     verbatim `Nat.accNatLt`'s proof term, registered as a Definition.
    let acc_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Acc"), vec![lvl1()]),
            [nat(), cnst("Nat.lt"), Expr::bvar(0)],
        ),
    );
    let acc_val = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Acc.intro"), vec![lvl1()]),
            [
                nat(),
                cnst("Nat.lt"),
                Expr::bvar(0),
                Expr::lam(
                    BinderInfo::Default,
                    nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_lt(Expr::bvar(0), Expr::bvar(1)),
                        Expr::apps(
                            cnst("Nat.lt_wfLBound"),
                            [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
                        ),
                    ),
                ),
            ],
        ),
    );
    define(&mut env, "accDef", acc_ty, acc_val);
    let def_witness = Expr::apps(
        Expr::const_(Name::from_string("WellFounded.intro"), vec![lvl1()]),
        [nat(), cnst("Nat.lt"), cnst("accDef")],
    );
    define(
        &mut env,
        "cds_red",
        Expr::arrow(nat(), nat()),
        wf_body_with(cnst("Nat.lt"), def_witness, cds_f(cds_then_correct(), cnst("Nat.zero"))),
    );

    // CONTROL sibling, defined up front: a def with a DIFFERENT F, so the
    // "spelling is immaterial" measurements below are not a collapse.
    define(
        &mut env,
        "cds_wrongF",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(add(succ(Expr::bvar(2)), Expr::bvar(2)), cnst("Nat.zero"))),
    );

    // THE SPELLING PIN — the spine parse succeeds and names each position.
    let body = env
        .get_const(&Name::from_string("cds"))
        .and_then(|c| c.value.clone())
        .expect("side A's body is readable from the kernel env");
    let spine = parse_wf_fix_spine(&body).expect("MEASURED: the WF side A parses as a fix spine");
    let tc = TypeChecker::new(&env);
    assert!(tc.is_def_eq(&spine.alpha, &nat()), "arg 0 is α = Nat");
    assert!(
        tc.is_def_eq(&spine.motive, &Expr::lam(BinderInfo::Default, nat(), nat())),
        "arg 1 is C = fun _ => Nat"
    );
    assert!(tc.is_def_eq(&spine.rel, &cnst("Nat.lt")), "arg 2 is r = Nat.lt");
    assert!(tc.is_def_eq(&spine.hwf, &cnst("Nat.lt_wf")), "arg 3 is hwf");
    // arg 4 is F, and its TYPE is the fact w7 rests on.
    let f_ty = tc.infer_type(&spine.f).expect("F's type is inferable");
    let expected_f_ty =
        Expr::pi(BinderInfo::Default, nat(), Expr::arrow(rec_ty(Expr::bvar(1)), nat()));
    // `Expr::arrow` and the pi above differ only in binder naming; compare by defeq.
    assert!(
        tc.is_def_eq(&f_ty, &expected_f_ty),
        "MEASURED: F : (x : Nat) → ((y : Nat) → Nat.lt y x → Nat) → Nat — the \
         recursive slot is a function over r-predecessors CARRYING THE PROOF. \
         got: {f_ty:?}"
    );

    // The three witness spellings are mutually defeq, and the eta-expanded
    // relation is too — so neither is load-bearing for a defeq gate.
    assert!(
        tc.is_def_eq(&cnst("Nat.lt_wf"), &intro_witness),
        "MEASURED: `Nat.lt_wf ≡ WellFounded.intro Nat Nat.lt Nat.accNatLt` — the \
         island's inline witness and the constant are the same term to the kernel"
    );
    for name in ["cds_intro", "cds_eta", "cds_red"] {
        assert!(
            tc.is_def_eq(&Expr::app(cnst("cds"), nat_num(3)), &Expr::app(cnst(name), nat_num(3))),
            "MEASURED: `{name} 3 ≡ cds 3` — the spelling deviation is immaterial"
        );
    }
    // CONTROL: the immateriality is not a collapse — a different F is a
    // different function.
    assert!(
        !tc.is_def_eq(
            &Expr::app(cnst("cds"), nat_num(3)),
            &Expr::app(cnst("cds_wrongF"), nat_num(3))
        ),
        "CONTROL: a def with a different F does NOT identify with cds"
    );

    // The parse REFUSES what it must.
    let structural = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
            [
                Expr::lam(BinderInfo::Default, nat(), nat()),
                cnst("Nat.zero"),
                Expr::lam(
                    BinderInfo::Default,
                    nat(),
                    Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
                ),
                Expr::bvar(0),
            ],
        ),
    );
    let err =
        parse_wf_fix_spine(&structural).expect_err("R1's structural shape is not a fix spine");
    assert!(err.contains("Nat.rec"), "the refusal must name the head it found, got: {err}");
    let err2 = parse_wf_fix_spine(&cnst("Nat.zero")).expect_err("a constant is not a fix spine");
    assert!(err2.contains("lambda"), "got: {err2}");
    eprintln!(
        "PROBE-ROW | w1 WF spine spelling         | @WellFounded.fix.{{1,1}} [α, C, r, hwf, F, \
         x=bvar 0] | F : (x)→((y)→Nat.lt y x→Nat)→Nat | witness spellings (const / inline \
         intro / reducible-Definition twin) mutually defeq | eta-expanded r immaterial | \
         parse refuses Nat.rec-headed and non-lambda"
    );
}

// ═══ (w2) THE CENTRAL QUESTION: the user equations at an OPEN argument ═══

/// **Expected NO; MEASURED YES.** Both user-level defining-equation forms of
/// the WF `countdownSum` close by a bare `Eq.refl` against the real kernel, at
/// an OPEN argument:
///
/// * the PER-CONSTRUCTOR form `∀ k, cds (succ k) = succ k + cds k` — the
///   shape R1's e1 measured for structural defs;
/// * the UNCONDITIONAL `.eq_def` form
///   `∀ n, cds n = dite (0 < n) (fun h => n + cds (n-1)) (fun _ => 0)` — the
///   shape a `termination_by` def actually has, with the recursion unfolded
///   exactly one layer and NO case analysis on `n` at all.
///
/// The second is the stronger measurement: it says the fix unfolds one step
/// at a COMPLETELY open argument, which is precisely what "stuck on `Acc.rec`"
/// would forbid. w3 measures why.
///
/// **These are side-A facts, NOT a gate.** Both statements cite the defined
/// constant on the right, and R1's s2 measured that the constant-citing
/// spelling admits a diverging body. They are recorded because they decide
/// whether R2 needs equation machinery (it does not), not because a gate may
/// be built out of them.
#[test]
fn probe_w2_user_equations_at_an_open_argument() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    // Mutation sibling: the then-branch adds `succ x` instead of `x`.
    define(
        &mut env,
        "cds_mut",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
            add(
                succ(Expr::bvar(2)),
                Expr::apps(
                    Expr::bvar(1),
                    [
                        sub(Expr::bvar(2), nat_num(1)),
                        Expr::apps(
                            cnst("Nat.sub_lt"),
                            [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                        ),
                    ],
                ),
            ),
            cnst("Nat.zero"),
        )),
    );

    // — the closed base equation —
    try_theorem(
        &mut env,
        "cds.eq_zero",
        eq_nat(Expr::app(cnst("cds"), nat_num(0)), nat_num(0)),
        refl_nat(nat_num(0)),
    )
    .expect("MEASURED: `cds 0 = 0` kernel-checks with a bare Eq.refl");

    // — THE PER-CONSTRUCTOR EQUATION AT OPEN k —
    let succ_eq = |f: &str| {
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(
                Expr::app(cnst(f), succ(Expr::bvar(0))),
                add(succ(Expr::bvar(0)), Expr::app(cnst(f), Expr::bvar(0))),
            ),
        )
    };
    let succ_rfl = |f: &str| {
        Expr::lam(BinderInfo::Default, nat(), refl_nat(Expr::app(cnst(f), succ(Expr::bvar(0)))))
    };
    try_theorem(&mut env, "cds.eq_succ", succ_eq("cds"), succ_rfl("cds")).expect(
        "THE HEADLINE MEASUREMENT: the WF def's succ equation is rfl-DEFINITIONAL \
         at an OPEN k. The expectation was REFUSAL (fix stuck on Acc.rec at an \
         open argument). If this ever refuses, w3's mechanism has changed and \
         R2's gate design must be re-derived from a fresh measurement",
    );

    // — THE UNCONDITIONAL `.eq_def` FORM AT FULLY OPEN n —
    // `∀ n, cds n = @dite Nat (0 < n) (Nat.decLt 0 n)
    //                 (fun h => Nat.add n (cds (Nat.sub n 1))) (fun _ => 0)`
    let eq_def_rhs = |f: &str| {
        let c = nat_lt(cnst("Nat.zero"), Expr::bvar(0));
        Expr::apps(
            Expr::const_(Name::from_string("dite"), vec![lvl1()]),
            [
                nat(),
                c.clone(),
                Expr::apps(cnst("Nat.decLt"), [cnst("Nat.zero"), Expr::bvar(0)]),
                Expr::lam(
                    BinderInfo::Default,
                    c.clone(),
                    add(Expr::bvar(1), Expr::app(cnst(f), sub(Expr::bvar(1), nat_num(1)))),
                ),
                Expr::lam(BinderInfo::Default, Expr::app(cnst("Not"), c), cnst("Nat.zero")),
            ],
        )
    };
    let eq_def_prop = |f: &str| {
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(Expr::app(cnst(f), Expr::bvar(0)), eq_def_rhs(f)),
        )
    };
    let err_def = try_theorem(
        &mut env,
        "cds.eq_def",
        eq_def_prop("cds"),
        Expr::lam(BinderInfo::Default, nat(), refl_nat(Expr::app(cnst("cds"), Expr::bvar(0)))),
    )
    .expect_err(
        "THE MEASURED BOUNDARY: the `.eq_def` form at a COMPLETELY open `n` is NOT \
         rfl — even though the fix DOES unfold there (w3 pins `whnf (cds <open \
         n>)` reaching `Decidable.rec`, and the non-recursive-F control admits \
         this very equation shape). What sticks is the RECURSIVE OCCURRENCE's \
         accessibility witness: the equation's right-hand side spells it \
         canonically as `Nat.accNatLt (n-1)` while the unfolding produces \
         `Nat.lt_wfLBound n (n-1) _`, and the two are interconvertible only when \
         the BOUND is constructor-headed (w3). w4 states the exact lemma. \
         If this ever ADMITS, the kernel gained `Acc`-proof convertibility: \
         re-measure w4 and simplify R2's work-list",
    );
    assert!(
        err_def.contains("TypeMismatch"),
        "the refusal must be the defeq TypeMismatch, got: {err_def}"
    );
    eprintln!("REFUSAL-DATA | w2 `.eq_def` at fully open n | TypeMismatch (kernel defeq)");

    // THE ISOLATING CONTROL: the same equation shape with a NON-RECURSIVE `F`
    // (its `rec` slot unused) ADMITS at a fully open `n`. So the fix's own
    // one-layer unfolding IS definitional at an open argument — the refusal
    // above is about the recursive occurrence's WITNESS, nothing else.
    define(
        &mut env,
        "gnr",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(Expr::bvar(2), cnst("Nat.zero"))),
    );
    let c = nat_lt(cnst("Nat.zero"), Expr::bvar(0));
    let gnr_rhs = Expr::apps(
        Expr::const_(Name::from_string("dite"), vec![lvl1()]),
        [
            nat(),
            c.clone(),
            Expr::apps(cnst("Nat.decLt"), [cnst("Nat.zero"), Expr::bvar(0)]),
            Expr::lam(BinderInfo::Default, c.clone(), Expr::bvar(1)),
            Expr::lam(BinderInfo::Default, Expr::app(cnst("Not"), c), cnst("Nat.zero")),
        ],
    );
    try_theorem(
        &mut env,
        "gnr.eq_def",
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(Expr::app(cnst("gnr"), Expr::bvar(0)), gnr_rhs),
        ),
        Expr::lam(BinderInfo::Default, nat(), refl_nat(Expr::app(cnst("gnr"), Expr::bvar(0)))),
    )
    .expect(
        "THE ISOLATING CONTROL: with a non-recursive F, the `.eq_def` unfolding \
         equation IS rfl at a fully open `n` — one `WellFounded.fix` layer peels \
         definitionally at an open argument. This is what makes the refusal above \
         a statement about the recursive occurrence's accessibility witness \
         rather than about `fix` being stuck",
    );

    // — MUTATION CONTROLS, so neither ADMIT above is vacuous —
    let err = try_theorem(&mut env, "cds_mut.eq_succ", succ_eq("cds_mut"), succ_rfl("cds_mut"))
        .expect_err(
            "SOUNDNESS PIN: the wrong-VALUE sibling must be REFUSED on the same \
             equation — otherwise the open-equation lane is a rubber stamp",
        );
    assert!(err.contains("TypeMismatch"), "the refusal must be the defeq TypeMismatch, got: {err}");
    eprintln!("REFUSAL-DATA | w2 wrong-value sibling | TypeMismatch at cds_mut.eq_succ");

    // Flipped addends — R1's e4 control, restated on the WF lane.
    let flipped = Expr::pi(
        BinderInfo::Default,
        nat(),
        eq_nat(
            Expr::app(cnst("cds"), succ(Expr::bvar(0))),
            add(Expr::app(cnst("cds"), Expr::bvar(0)), succ(Expr::bvar(0))),
        ),
    );
    let err2 = try_theorem(&mut env, "cds.eq_succ_flipped", flipped, succ_rfl("cds"))
        .expect_err("CONTROL: the flipped addend order must REFUSE — defeq is not arithmetic");
    assert!(err2.contains("TypeMismatch"), "got: {err2}");

    // A DIFFERENT-ARGUMENT equation must refuse too (`cds (succ k) = succ k + cds (succ k)`).
    let self_arg = Expr::pi(
        BinderInfo::Default,
        nat(),
        eq_nat(
            Expr::app(cnst("cds"), succ(Expr::bvar(0))),
            add(succ(Expr::bvar(0)), Expr::app(cnst("cds"), succ(Expr::bvar(0)))),
        ),
    );
    try_theorem(&mut env, "cds.eq_succ_selfarg", self_arg, succ_rfl("cds"))
        .expect_err("CONTROL: a non-decreasing right-hand side must refuse");

    eprintln!(
        "PROBE-ROW | w2 OPEN user equations       | per-constructor succ equation (OPEN k): \
         rfl ADMIT | `.eq_def` (FULLY open n): REFUSED — the recursive occurrence's witness \
         | same shape with a NON-RECURSIVE F (fully open n): ADMIT | wrong-value / \
         flipped-addend / non-decreasing-RHS: REFUSED"
    );
}

// ═══════ (w3) WHY nothing is stuck — the mechanism, measured ═══════

/// Three measurements that together explain w2, and that any R2 design must
/// keep true:
///
/// 1. **`whnf (Nat.accNatLt <open>)` is `Acc.intro`-headed.** Clean's
///    `Nat.accNatLt` is a `Declaration::Theorem` whose VALUE is
///    `fun n => Acc.intro n (fun m h => Nat.lt_wfLBound n m h)` — a
///    constructor application. The kernel's whnf delta-unfolds it even at an
///    open argument, so `Acc.rec`'s major premise is constructor-headed and
///    iota fires. This is the whole reason a `WellFounded.fix` application
///    unfolds one layer at an open argument here. (Lean's `Nat.lt_wf` is not
///    of this shape, which is why the Lean intuition — "fix is stuck" — does
///    not transfer.)
/// 2. **Proof irrelevance absorbs the residual Acc mismatch.** After one
///    unfolding the recursive occurrence carries `Nat.lt_wfLBound n y p`
///    where the equation's right-hand side carries `Nat.accNatLt y`. Both
///    inhabit `Acc Nat.lt y`, a Prop, and the kernel identifies them.
/// 3. **The identification is TYPE-directed, not blanket.** Proofs of
///    DIFFERENT propositions are not identified, and `fixF` applications at
///    DIFFERENT points are not identified — so (2) does not make the lane
///    vacuous.
#[test]
fn probe_w3_the_mechanism_accnatlt_unfolds_and_proofs_are_irrelevant() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    // The second witness spelling, defined up front so the type-checker borrow
    // below spans no mutation of the environment.
    let intro_witness = Expr::apps(
        Expr::const_(Name::from_string("WellFounded.intro"), vec![lvl1()]),
        [nat(), cnst("Nat.lt"), cnst("Nat.accNatLt")],
    );
    define(
        &mut env,
        "cds_w2",
        Expr::arrow(nat(), nat()),
        wf_body_with(cnst("Nat.lt"), intro_witness, cds_f(cds_then_correct(), cnst("Nat.zero"))),
    );
    let tc = TypeChecker::new(&env);

    // (1) the accessibility witness whnfs to a constructor at an OPEN point.
    let reduced = tc.whnf(&Expr::app(cnst("Nat.accNatLt"), Expr::bvar(0)));
    let mut head = &reduced;
    while let ExprKind::App(function, _) = head.kind() {
        head = function;
    }
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Acc.intro")),
        "MEASURED, THE MECHANISM: `whnf (Nat.accNatLt <open>)` is `Acc.intro`-headed \
         — delta fires through a Theorem whose value is a constructor application, \
         so `Acc.rec` iota-reduces at an OPEN argument and `WellFounded.fix` \
         unfolds. If this ever sticks, w2 flips and R2 needs `fixFEq` after all. \
         got head: {head:?}"
    );

    // (1b) THE DEPTH BOUNDARY. The SECOND unfolding layer needs the
    // accessibility witness the FIRST one produced — `Nat.lt_wfLBound n y p`,
    // whose own proof recurses on the BOUND `n`. Measured: constructor-headed
    // bound reduces to `Acc.intro`; fully open bound sticks at `Nat.rec`.
    // This is the whole difference between w2's admitting per-constructor
    // equation and its refusing `.eq_def` equation.
    let head_of = |e: &Expr| {
        let reduced = tc.whnf(e);
        let mut cursor = &reduced;
        while let ExprKind::App(function, _) = cursor.kind() {
            cursor = function;
        }
        match cursor.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        }
    };
    assert_eq!(
        head_of(&Expr::apps(
            cnst("Nat.lt_wfLBound"),
            [
                succ(Expr::bvar(0)),
                Expr::bvar(0),
                Expr::app(cnst("Nat.le.refl"), succ(Expr::bvar(0)))
            ],
        )),
        "Acc.intro",
        "MEASURED: at a CONSTRUCTOR-HEADED bound, the threaded accessibility \
         witness reduces to `Acc.intro` — so the recursion unfolds to any depth \
         and the per-constructor equation is rfl (w2)"
    );
    assert_eq!(
        head_of(&Expr::apps(
            cnst("Nat.lt_wfLBound"),
            [Expr::bvar(1), Expr::bvar(0), Expr::bvar(2)]
        )),
        "Nat.rec",
        "MEASURED, THE DEPTH BOUNDARY: at a FULLY OPEN bound the threaded witness \
         sticks at `Nat.rec` — the second unfolding layer does not fire, which is \
         exactly why w2's `.eq_def` equation refuses while its per-constructor \
         equation admits"
    );

    // (2) proof irrelevance: two DIFFERENT proofs of the same Prop.
    // `Nat.lt_succ_self k` (a constant application) vs `@Nat.le.refl (succ k)`
    // (a constructor application) — both prove `Nat.lt k (succ k)`.
    let p1 = Expr::app(cnst("Nat.lt_succ_self"), Expr::bvar(0));
    let p2 = Expr::app(cnst("Nat.le.refl"), succ(Expr::bvar(0)));
    assert!(
        tc.is_def_eq(&p1, &p2),
        "MEASURED: two different proofs of `Nat.lt k (succ k)` are definitionally \
         equal — proof irrelevance. This is what absorbs the Acc-witness mismatch \
         between the unfolded fix and the equation's right-hand side"
    );
    // (3a) …but proofs of DIFFERENT props are not identified.
    let p3 = Expr::app(cnst("Nat.le.refl"), succ(succ(Expr::bvar(0))));
    assert!(
        !tc.is_def_eq(&p2, &p3),
        "CONTROL: proof irrelevance is TYPE-directed — `Nat.le (succ k) (succ k)` \
         and `Nat.le (succ (succ k)) (succ (succ k))` are different propositions \
         and their proofs are not identified"
    );

    // (3b) `fixF` at different points is not identified. Build the two
    // applications through the defined constant's own body: `cds k` vs
    // `cds (succ k)` at an open k.
    let cds_at = |x: Expr| Expr::app(cnst("cds"), x);
    assert!(
        !tc.is_def_eq(&cds_at(Expr::bvar(0)), &cds_at(succ(Expr::bvar(0)))),
        "CONTROL: the fix at DIFFERENT points is not identified — proof \
         irrelevance absorbs the witness, never the recursion point"
    );
    // …while the same point under two different witness spellings IS.
    assert!(
        tc.is_def_eq(&cds_at(Expr::bvar(0)), &Expr::app(cnst("cds_w2"), Expr::bvar(0))),
        "MEASURED: the same recursion point under two witness spellings IS \
         identified, at an OPEN argument"
    );
    eprintln!(
        "PROBE-ROW | w3 mechanism                 | whnf(Nat.accNatLt open) = Acc.intro-headed \
         (layer 1 fires at any argument) | whnf(lt_wfLBound (succ k) ..) = Acc.intro but \
         whnf(lt_wfLBound <open> ..) = Nat.rec STUCK (layer 2 needs a constructor-headed \
         bound) | proof irrelevance identifies distinct proofs of one Prop, NOT across \
         props, NOT across recursion points | same point + different witness: identified"
    );
}

// ═══════ (w4) THE SIBLING WORK-LIST: which unfolding lemma is missing,
//         stated exactly, and which one this kernel already proves by rfl ═══════

/// R2's sibling work-list, made precise enough to implement from. Two forms of
/// the `fixF` unfolding equation are put to the kernel, differing ONLY in how
/// the recursive occurrence's accessibility witness is spelled:
///
/// * **form A — the UNFOLDING-NATIVE witness.**
///   ```text
///   ∀ (n : Nat),
///     @WellFounded.fixF Nat Nat.lt (fun _ => Nat) F n (Nat.accNatLt n)
///   = F n (fun (y : Nat) (p : Nat.lt y n) =>
///            @WellFounded.fixF Nat Nat.lt (fun _ => Nat) F y
///              (Nat.lt_wfLBound n y p))
///   ```
///   This is `WellFounded.fixFEq` at R2's instantiation, with the ABSENT
///   `Acc.inv acx p` replaced by the concrete witness the reduction actually
///   produces. **MEASURED: rfl.** So the `fixFEq` half of the sibling
///   work-list is empty — the statement is definitional here.
///
/// * **form B — the CANONICAL witness.** Same statement with the recursive
///   occurrence's witness re-canonicalized to `Nat.accNatLt y`, which is what
///   the DEFINED CONSTANT `cds y` elaborates to and therefore what any
///   user-level equation says. **MEASURED: REFUSED.**
///
/// The gap between A and B is exactly one proposition, and it is the lemma a
/// sibling would have to provide **if R2 ever went the equation route**:
///
/// ```text
/// theorem WellFounded.fixF_acc_irrel :
///   ∀ {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
///     (F : (x : α) → ((y : α) → r y x → C y) → C x)
///     (x : α) (a b : Acc r x),
///     @WellFounded.fixF α r C F x a = @WellFounded.fixF α r C F x b
/// ```
///
/// — `fixF` does not depend on WHICH accessibility proof it is given. (Lean
/// derives its `WellFounded.fix_eq` from exactly this, via `Acc`
/// subsingleton-ness; kernel proof irrelevance does not supply it, because the
/// proofs sit in `Acc.rec`'s major-premise position where the kernel is
/// reducing, not comparing — the "`fixFEq`/Acc-proof mismatch lesson" that
/// `clean-kernel/src/env/algebra_nat_bitwise_def.rs` records in its own
/// module docs.) With it, `Acc.inv` and `WellFounded.fixFEq` — both already
/// written, both `#[cfg(test)]`, both documented axiom-free — would need
/// lifting into `with_prelude` too; that part is a REGISTRATION, not a proof.
///
/// **R2 does not need any of it**, because w5–w7's gate never states an
/// equation. This probe exists so that the option is costed, not so that it
/// is taken.
#[test]
fn probe_w4_the_missing_unfolding_lemma_stated_exactly() {
    let mut env = Environment::with_prelude();
    assert!(
        !has(&env, "WellFounded.fixFEq") && !has(&env, "Acc.inv"),
        "w0's absences are the premise of this probe"
    );
    install_cds(&mut env, "cds");
    let f = cds_f(cds_then_correct(), cnst("Nat.zero"));

    // `@WellFounded.fixF.{1,1} Nat Nat.lt (fun _ => Nat) F x acc`
    // (binder order per `well_founded.rs`: {α} {r} {C} F x a).
    let fix_f = |x: Expr, acc: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("WellFounded.fixF"), vec![lvl1(), lvl1()]),
            [
                nat(),
                cnst("Nat.lt"),
                Expr::lam(BinderInfo::Default, nat(), nat()),
                f.clone(),
                x,
                acc,
            ],
        )
    };
    let lhs = fix_f(Expr::bvar(0), Expr::app(cnst("Nat.accNatLt"), Expr::bvar(0)));

    // form A — the witness the unfolding itself produces.
    // scope inside the rec argument: [n, y, p] => n = bvar 2, y = bvar 1, p = bvar 0
    let rec_native = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat_lt(Expr::bvar(0), Expr::bvar(1)),
            fix_f(
                Expr::bvar(1),
                Expr::apps(cnst("Nat.lt_wfLBound"), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]),
            ),
        ),
    );
    try_theorem(
        &mut env,
        "fixFEq_form_a_unfolding_native",
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(lhs.clone(), Expr::apps(f.clone(), [Expr::bvar(0), rec_native])),
        ),
        Expr::lam(BinderInfo::Default, nat(), refl_nat(lhs.clone())),
    )
    .expect(
        "MEASURED: `WellFounded.fixFEq` at R2's instantiation, with the recursive \
         occurrence's witness spelled as the reduction produces it, closes by \
         bare rfl — the fixFEq half of the work-list is EMPTY",
    );

    // form B — the canonical witness (what any user-level equation says).
    let rec_canonical = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat_lt(Expr::bvar(0), Expr::bvar(1)),
            fix_f(Expr::bvar(1), Expr::app(cnst("Nat.accNatLt"), Expr::bvar(1))),
        ),
    );
    let err = try_theorem(
        &mut env,
        "fixFEq_form_b_canonical_witness",
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(lhs.clone(), Expr::apps(f, [Expr::bvar(0), rec_canonical])),
        ),
        Expr::lam(BinderInfo::Default, nat(), refl_nat(lhs)),
    )
    .expect_err(
        "THE WORK-LIST ITEM: re-canonicalizing the recursive occurrence's \
         accessibility witness is NOT definitional. The missing proposition is \
         `fixF F x a = fixF F x b` for any two `a b : Acc r x` — see this \
         probe's doc comment for the exact statement. If this ever ADMITS, the \
         kernel gained Acc-proof convertibility and w2's `.eq_def` refusal \
         should flip too: re-measure both together",
    );
    assert!(err.contains("TypeMismatch"), "the refusal must be the defeq TypeMismatch, got: {err}");
    eprintln!("REFUSAL-DATA | w4 form B canonical witness | TypeMismatch (kernel defeq)");
    eprintln!(
        "PROBE-ROW | w4 missing unfolding lemma   | WellFounded.fixFEq + Acc.inv ABSENT \
         (`#[cfg(test)]` source, axiom-free proofs documented) | form A (unfolding-native \
         witness): rfl ADMIT | form B (canonical witness): REFUSED -> the ONLY missing \
         proposition is `fixF F x a = fixF F x b` for `a b : Acc r x` | R2's gate needs \
         NEITHER"
    );
}

// ═══════ (w5/w6) THE F-LAYER — §6e's abstract-ih analogue for WF ═══════

/// The F-layer is where R2's gate lives, and this probe measures all three
/// halves of that claim:
///
/// * **(a) extractability** — side A's `F` is recoverable by the w5 spine
///   parse (already exercised in w1); here it is compared, not just found.
/// * **(b) a correct hand-built F ADMITS** — built independently below rather
///   than by reusing this file's helper, so the check is a defeq question
///   about two constructions. The recursive slot needs no "held abstract"
///   discipline: `rec` is a BINDER of side A's own term, so the defined
///   constant cannot appear (R1's s2 vacuity is impossible here by
///   construction, exactly as in s3 — but structurally rather than by a
///   reflection convention).
/// * **(b′) a defeq-equal SPELLING admits** — `Nat.pred x` for the
///   MIR-faithful `Nat.sub x 1`, the WF analogue of R1's s6.
/// * **(c) wrong-VALUE F's REFUSE** — three of them: a wrong addend, a
///   swapped addend order, and a wrong ELSE branch (the analogue of a dropped
///   case, which needs no completeness component because the case split is
///   inside the term being compared).
/// * **congruence, both directions** — F-agreement implies whole-body
///   agreement, and F-disagreement propagates to the whole body. This is what
///   makes an F-layer gate SOUND with respect to the whole-term question
///   while never requiring side B to mint an accessibility witness.
#[test]
fn probe_w5_w6_f_layer_defeq_admits_correct_refuses_wrong_value() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    let body = env
        .get_const(&Name::from_string("cds"))
        .and_then(|c| c.value.clone())
        .expect("side A body");
    let f_a = parse_wf_fix_spine(&body).expect("side A parses").f;

    // (b) side B's F, built independently, term by term.
    let f_b = {
        let cond = nat_lt(cnst("Nat.zero"), Expr::bvar(1));
        let then_branch = Expr::lam(
            BinderInfo::Default,
            nat_lt(cnst("Nat.zero"), Expr::bvar(1)),
            Expr::apps(
                cnst("Nat.add"),
                [
                    Expr::bvar(2),
                    Expr::apps(
                        Expr::bvar(1),
                        [
                            Expr::apps(cnst("Nat.sub"), [Expr::bvar(2), nat_num(1)]),
                            Expr::apps(
                                cnst("Nat.sub_lt"),
                                [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                            ),
                        ],
                    ),
                ],
            ),
        );
        let else_branch =
            Expr::lam(BinderInfo::Default, Expr::app(cnst("Not"), cond.clone()), cnst("Nat.zero"));
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
                        cond,
                        Expr::apps(cnst("Nat.decLt"), [cnst("Nat.zero"), Expr::bvar(1)]),
                        then_branch,
                        else_branch,
                    ],
                ),
            ),
        )
    };

    // (b′) the defeq-equal `Nat.pred` spelling of the MIR-faithful `Nat.sub x 1`.
    // The SAME proof term type-checks in the slot, because `Nat.sub x 1 ≡ Nat.pred x`.
    let f_pred = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [
                    Expr::app(cnst("Nat.pred"), Expr::bvar(2)),
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    );
    define(&mut env, "cds_pred", Expr::arrow(nat(), nat()), wf_body(f_pred.clone()));

    // (c) wrong-VALUE F's — each kernel-checks (so the refusal is a genuine
    // DEFEQ verdict, not a typing accident) and each is refused.
    let wrong_addend = cds_f(
        add(
            succ(Expr::bvar(2)),
            Expr::apps(
                Expr::bvar(1),
                [
                    sub(Expr::bvar(2), nat_num(1)),
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    );
    let swapped = cds_f(
        add(
            Expr::apps(
                Expr::bvar(1),
                [
                    sub(Expr::bvar(2), nat_num(1)),
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                    ),
                ],
            ),
            Expr::bvar(2),
        ),
        cnst("Nat.zero"),
    );
    let wrong_else = cds_f(cds_then_correct(), nat_num(1));
    let mutations = [
        ("wrong-addend", wrong_addend),
        ("swapped-addends", swapped),
        ("wrong-else-branch", wrong_else),
    ];
    for (name, f_wrong) in &mutations {
        define(
            &mut env,
            &format!("cds_{}", name.replace('-', "_")),
            Expr::arrow(nat(), nat()),
            wf_body(f_wrong.clone()),
        );
    }

    // ONE type-checker borrow, after every definition this probe needs.
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&f_b, &f_a),
        "MEASURED (component 1 of the R2 gate): an independently-built correct F \
         is kernel-defeq to side A's F, with the recursive slot an ABSTRACT \
         BINDER on both sides — no defined constant anywhere, so the s2 vacuity \
         cannot recur"
    );
    assert!(
        tc.is_def_eq(&f_pred, &f_a),
        "MEASURED (the WF analogue of s6): the `Nat.pred x` spelling of the \
         recursive argument identifies with the MIR-faithful `Nat.sub x 1` — the \
         F comparison accepts defeq-equal spellings, it is not a syntax match"
    );
    for (name, f_wrong) in &mutations {
        assert!(
            tc.is_def_eq(
                &tc.infer_type(f_wrong).expect("it kernel-checks"),
                &tc.infer_type(&f_a).expect("F_A type")
            ),
            "the mutation must have side A's F TYPE — otherwise the refusal below \
             would be a typing accident, not a defeq verdict ({name})"
        );
        assert!(
            !tc.is_def_eq(f_wrong, &f_a),
            "SOUNDNESS PIN: the `{name}` F must be REFUSED at the F layer. The \
             wrong-else-branch case is the one that shows R1's COMPLETENESS \
             component is unnecessary here: the case split lives inside the term \
             the comparison already covers"
        );
        // …and the disagreement propagates to the whole body (congruence, the
        // direction that makes an F-layer gate sound).
        assert!(
            !tc.is_def_eq(&wf_body(f_wrong.clone()), &body),
            "and the whole bodies disagree too ({name})"
        );
    }

    // congruence, the admitting direction: F-agreement ⟹ body agreement.
    assert!(
        tc.is_def_eq(&wf_body(f_b), &body),
        "MEASURED: F-agreement implies whole-body agreement — the F-layer check \
         is SOUND with respect to the whole-term question, and it never asks \
         side B for an accessibility witness"
    );
    eprintln!(
        "PROBE-ROW | w5/w6 F layer                | independent correct F: defeq ADMIT | \
         `Nat.pred` spelling: ADMIT | wrong addend / swapped addends / wrong else-branch: \
         REFUSED (all three type-check first) | congruence measured both directions"
    );
}

// ═══════ (w7) THE DECREASE QUESTION ═══════

/// **Does the F-layer comparison alone inherit side A's termination evidence,
/// or does R2 need R1's separate recursive-argument check?** Four
/// measurements, and the answer is: the F's TYPE pins it, so no separate
/// decrease component is needed — but a NEW component is, and it is not about
/// arguments at all.
///
/// * **(d1) TYPE-FORCING.** `rec : (y : Nat) → Nat.lt y x → C y`. An F that
///   recurses at `Nat.succ x` — the diverging off-by-one whose R1 analogue
///   passed the constant-citing spelling (s2) — cannot be given the available
///   proof: `Nat.sub_lt x 1 h 0<1 : Nat.lt (x-1) x` does not prove
///   `Nat.lt (succ x) x`, and the kernel REFUSES the definition. The
///   divergence catch is the TYPING RULE.
/// * **(d2) the proof slot is IRRELEVANT.** Two F's differing only in which
///   proof fills the `Nat.lt y x` slot are defeq. This is what lets side B
///   BORROW side A's proof term at each call site without co-authoring the
///   checked content: the proof is not what the comparison decides, the
///   ARGUMENT is.
/// * **(d3) defeq is ARGUMENT-sensitive even among decreasing alternatives.**
///   An F recursing at `x - 2` (well-typed, genuinely decreasing, terminating)
///   is REFUSED against side A's `x - 1`. Typing cannot see this; defeq can.
/// * **(d4) THE ESCAPE, and the new obligation.** With
///   `axiom bogus : (x : Nat) → Nat.lt (Nat.succ x) x` in scope, the
///   diverging F kernel-checks and the diverging def ADMITS. So the guarantee
///   d1 provides is exactly as strong as the axiom closure of the proof terms
///   in side B's F. **R2's gate must audit that closure** — the machinery
///   exists (`mint.rs` / `AxiomClosure::is_audited_empty`), but it currently
///   covers side A's declaration, not side B's proof slots.
///   (No closed application of the diverging def is evaluated here: it would
///   not terminate. Its ADMISSION is the measurement.)
#[test]
fn probe_w7_the_decrease_question() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    let body = env
        .get_const(&Name::from_string("cds"))
        .and_then(|c| c.value.clone())
        .expect("side A body");
    let f_a = parse_wf_fix_spine(&body).expect("side A parses").f;

    // (d1) the non-decreasing self-call cannot be typed.
    let f_diverging = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [
                    succ(Expr::bvar(2)), // THE OFF-BY-ONE: recurse at x + 1
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    );
    let err = try_define(
        &mut env,
        "cds_diverging",
        Expr::arrow(nat(), nat()),
        wf_body(f_diverging.clone()),
    )
    .expect_err(
        "THE DECREASE ANSWER: an F that recurses on a NON-DECREASING argument is \
         refused by the KERNEL'S TYPING RULE — `rec`'s second argument must prove \
         `Nat.lt y x`, and no proof of `Nat.lt (succ x) x` exists. R1 needed a \
         separate recursive-argument identity (s4) because `Nat.rec`'s `ih` \
         ERASES the argument; a WF spine does not",
    );
    assert!(
        err.contains("TypeMismatch") || err.contains("TypeCheckFailed"),
        "the refusal must be the typing verdict at the proof slot, got: {err}"
    );
    eprintln!("REFUSAL-DATA | w7 d1 non-decreasing | typing refusal at the `Nat.lt y x` slot");

    // (d2) the proof slot is irrelevant: swap in a different proof of the
    // same proposition (`Nat.lt (x-1) x`) via the `Nat.pred` spelling of the
    // subtrahend — a DIFFERENT term of a DEFEQ type.
    let f_other_proof = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [
                    sub(Expr::bvar(2), nat_num(1)),
                    // `Nat.sub_lt x 1 h (Nat.lt_succ_self 0)` — `Nat.lt_succ_self 0`
                    // and `Nat.le.refl 1` are different terms of `Nat.lt 0 1`.
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [
                            Expr::bvar(2),
                            nat_num(1),
                            Expr::bvar(0),
                            Expr::app(cnst("Nat.lt_succ_self"), cnst("Nat.zero")),
                        ],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    );
    define(&mut env, "cds_other_proof", Expr::arrow(nat(), nat()), wf_body(f_other_proof.clone()));

    // (d3) a well-typed, genuinely decreasing, but DIFFERENT argument refuses.
    let f_two_back = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [
                    sub(Expr::bvar(2), nat_num(2)),
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(2), Expr::bvar(0), two_pos()],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    );
    define(&mut env, "cds_two_back", Expr::arrow(nat(), nat()), wf_body(f_two_back.clone()));

    // (d4) THE ESCAPE: an axiom makes the diverging F type-check.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("r2_probe_bogus_lt"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat(), nat_lt(succ(Expr::bvar(0)), Expr::bvar(0))),
    })
    .expect("an axiom may be declared");
    let f_axiom_diverging = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [succ(Expr::bvar(2)), Expr::app(cnst("r2_probe_bogus_lt"), Expr::bvar(2))],
            ),
        ),
        cnst("Nat.zero"),
    );
    try_define(
        &mut env,
        "cds_axiom_diverging",
        Expr::arrow(nat(), nat()),
        wf_body(f_axiom_diverging),
    )
    .expect(
        "THE ADVERSE PIN (d4): with a bogus decrease AXIOM in scope, the DIVERGING \
         F kernel-checks and the definition ADMITS. The termination guarantee d1 \
         provides is exactly as strong as the AXIOM CLOSURE of the proof terms in \
         side B's F — so R2's gate must audit that closure. This ADMIT is the \
         adverse finding, not good news (same polarity inversion as R1's s2). \
         NOTE: no closed application of this def is evaluated — it would not \
         terminate; its admission is the whole measurement",
    );

    // ONE type-checker borrow, after every definition this probe needs.
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&f_other_proof, &f_a),
        "MEASURED (d2): F's differing ONLY in the proof filling the decrease slot \
         are defeq — so side B may borrow side A's proof terms without \
         co-authoring what the gate decides"
    );
    assert!(
        tc.is_def_eq(
            &tc.infer_type(&f_two_back).expect("it types"),
            &tc.infer_type(&f_a).expect("F_A types")
        ),
        "the `x - 2` F has side A's F type — it is a legal, terminating recursion"
    );
    assert!(
        !tc.is_def_eq(&f_two_back, &f_a),
        "SOUNDNESS PIN (d3): a DIFFERENT decreasing argument is refused by defeq. \
         Typing cannot see this — both are terminating — so the F comparison is \
         doing real work beyond termination"
    );
    eprintln!(
        "PROBE-ROW | w7 THE DECREASE QUESTION     | d1 non-decreasing arg: REFUSED BY TYPING \
         (not by a gate component) | d2 proof slot: irrelevant (borrowable) | d3 different \
         decreasing arg: REFUSED by defeq | d4 with a bogus AXIOM the diverging F \
         type-checks and ADMITS -> the new obligation is an AXIOM-CLOSURE audit of side B's \
         proof slots"
    );
}

// ═══════ (w8) what today's landed gate does with a WF side A ═══════

/// Two pins on `gate.rs` as it stands, both of which R2 will move:
///
/// * `check_faithful_equations` — R1's per-equation lane — refuses with
///   `NotStructuralRecursor`, and its note names `WellFounded.fix` and
///   "equation lemmas". **The second half of that note is now
///   measured-wrong** (w2/w4): equation lemmas are not R2's prerequisite.
///   The assertion below pins the CURRENT text as data; when R2 lands, the
///   note must be re-worded and this assertion updated in the same change —
///   that is the no-silent-ratchet rule, not a test to relax.
/// * `check_faithful` — the WHOLE-TERM lane — **ADMITS** a WF side A when
///   handed the body itself, and refuses a wrong-F sibling. So the whole-term
///   gate is not WF-blind; what is missing is a side-B producer, and w1/w6
///   are why R2 should factor through `F` rather than mint an accessibility
///   witness from MIR.
#[test]
fn probe_w8_todays_gate_on_a_wellfounded_side_a() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    // A structural def, purely to obtain a plannable carrier for `Nat -> Nat`.
    define(
        &mut env,
        "tozero",
        Expr::arrow(nat(), nat()),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::apps(
                Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
                [
                    Expr::lam(BinderInfo::Default, nat(), nat()),
                    cnst("Nat.zero"),
                    Expr::lam(
                        BinderInfo::Default,
                        nat(),
                        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
                    ),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let plan = plan_clean_origin_body(&env, "tozero").expect("R1 plans the structural def");
    let carrier = plan.result_carrier();

    // (1) the per-equation lane refuses a WF side A before looking at side B.
    let dummy = ReflectedStructuralRec {
        cases: vec![
            ReflectedCase { constructor: "Nat.zero".to_owned(), value: cnst("Nat.zero") },
            ReflectedCase {
                constructor: "Nat.succ".to_owned(),
                value: Expr::lam(
                    BinderInfo::Default,
                    nat(),
                    Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
                ),
            },
        ],
        rec_arg: Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
    };
    let refusal = check_faithful_equations(&env, "cds", &dummy, carrier)
        .expect_err("R1's per-equation gate must refuse a WellFounded.fix side A");
    assert!(matches!(refusal, GateRefusal::NotStructuralRecursor { .. }), "got {refusal:?}");
    assert!(
        refusal.note().contains("WellFounded.fix"),
        "the refusal must name the head it found; got: {}",
        refusal.note()
    );
    assert!(
        refusal.note().contains("equation lemmas"),
        "PINNED AS DATA, AND MEASURED-WRONG: today's note names kernel-checked \
         equation lemmas as R2's prerequisite. w2/w4 measure that the equations \
         are already definitional and that the one candidate lemma is rfl at \
         R2's instantiation. When R2 lands, re-word the note and update THIS \
         assertion in the same change. got: {}",
        refusal.note()
    );

    // (2) the whole-term lane ADMITS a WF side A — it is only missing side B.
    let body = env
        .get_const(&Name::from_string("cds"))
        .and_then(|c| c.value.clone())
        .expect("side A body");
    let admitted = check_faithful(&env, "cds", &body, carrier)
        .expect("MEASURED: the WHOLE-TERM gate admits a WellFounded.fix side A");
    assert_eq!(admitted.name(), "cds");
    // …and refuses a wrong-F side B, so the admission is a decision.
    let wrong_body = wf_body(cds_f(add(succ(Expr::bvar(2)), Expr::bvar(2)), cnst("Nat.zero")));
    let refused = check_faithful(&env, "cds", &wrong_body, carrier)
        .expect_err("a wrong-F side B must be refused by the whole-term gate");
    assert!(matches!(refused, GateRefusal::Disagreement { .. }), "got {refused:?}");
    eprintln!(
        "PROBE-ROW | w8 today's gate vs WF side A | check_faithful_equations: \
         NotStructuralRecursor (note names WellFounded.fix + `equation lemmas` — the latter \
         MEASURED-WRONG, re-word when R2 lands) | check_faithful (whole-term): ADMITS, \
         wrong-F REFUSED"
    );
}

// ═══════ (w9) closed-value pins for the future R2 fixture ═══════

/// The values an R2 run-pass fixture will assert, pinned here first, in BOTH
/// numeral lanes, each with a refusing mutation — R1's e5 discipline on the WF
/// lane. `cds n = n + (n-1) + … + 1` (triangular numbers), so `cds 5 ≡ 15`.
///
/// These also pin something the structural lane never tested: that the
/// `Acc.rec` tower actually GRINDS on a closed argument through a genuinely
/// recursive `F` (r4's `wfz` ignored its `rec` slot entirely, so it measured
/// one unfolding, not a recursion).
#[test]
fn probe_w9_closed_value_pins() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    define(
        &mut env,
        "cds_mut",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
            add(
                succ(Expr::bvar(2)),
                Expr::apps(
                    Expr::bvar(1),
                    [
                        sub(Expr::bvar(2), nat_num(1)),
                        Expr::apps(
                            cnst("Nat.sub_lt"),
                            [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                        ),
                    ],
                ),
            ),
            cnst("Nat.zero"),
        )),
    );
    let tc = TypeChecker::new(&env);

    for (n, expected) in [(0u64, 0u64), (1, 1), (3, 6), (5, 15)] {
        assert!(
            tc.is_def_eq(&Expr::app(cnst("cds"), nat_num(n)), &nat_num(expected)),
            "MEASURED: `cds {n} ≡ {expected}` (succ-tree lane) — the Acc.rec tower \
             grinds through a genuinely recursive F on a closed argument"
        );
        assert!(
            tc.is_def_eq(&Expr::app(cnst("cds"), Expr::nat_lit(n)), &Expr::nat_lit(expected)),
            "MEASURED: `cds {n} ≡ {expected}` (literal lane)"
        );
    }
    assert!(
        !tc.is_def_eq(&Expr::app(cnst("cds"), nat_num(5)), &nat_num(14)),
        "`cds 5 ≡ 14` must refuse — the computation pin is a decision"
    );
    // The mutation sibling computes to ITS value (`cds_mut n = (n+1) + …`),
    // and not to side A's.
    assert!(
        tc.is_def_eq(&Expr::app(cnst("cds_mut"), nat_num(3)), &nat_num(9)),
        "the mutation sibling must compute to ITS value: 4 + 3 + 2 = 9"
    );
    assert!(
        !tc.is_def_eq(&Expr::app(cnst("cds_mut"), nat_num(3)), &nat_num(6)),
        "…and must not compute to side A's"
    );
    eprintln!(
        "PROBE-ROW | w9 closed values             | cds 0/1/3/5 ≡ 0/1/6/15, BOTH numeral \
         lanes | cds 5 ≢ 14 | mutation sibling: cds_mut 3 ≡ 9, ≢ 6"
    );
}

// ═══ (w10) THE SPELLING THIS FILE WAS WRONG ABOUT — typeclass vs delta ═══
//
// w1–w9 all build side A out of `Nat.lt`, `Nat.decLt` and `Nat.sub`, and this
// file's own HONESTY RULES call those "RAW-KERNEL MIRRORS of the island
// elaborator's measured output". The mirror was measured at the SPINE and
// never inside the `dite`: the elaborator mints the TYPECLASS spellings
// (`@LT.lt.{0} Nat instLTNat 0 x`, `instDecidableNatLt 0 x`,
// `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat n 1`), so a recognizer written
// against these helpers refused the exact surface text its own diagnostic
// advertised. That divergence has now produced this class of defect twice
// (C9's select-literal decidability tree; this one), which is why the rows
// below exist and why w10b puts the same question to the REAL elaborator
// rather than to another hand-built term.

/// `cds_f` with the guard's TWO components left open, so one probe can vary the
/// spelling without varying anything else.
///
/// `cond` and `dec` are built in the scope `[x = bvar 1, rec = bvar 0]` — the
/// same depth as the `dite` arguments and as both branch binders' TYPES;
/// `then_call` in `[x = bvar 2, rec = bvar 1, h = bvar 0]`, `else_value` in
/// `[x, rec, _]`. Identical to [`cds_f`] when handed
/// `nat_lt(Nat.zero, bvar 1)` and `Nat.decLt Nat.zero (bvar 1)`.
fn cds_f_spelled(cond: Expr, dec: Expr, then_call: Expr, else_value: Expr) -> Expr {
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

/// The `countdownSum` functional in the ELABORATOR's spelling: typeclass
/// guard, typeclass decidability instance, typeclass subtraction.
///
/// The guard's lower bound stays `Nat.zero` and the subtrahend stays the succ
/// tower DELIBERATELY: `Nat.sub_lt`'s premise is spelled
/// `Nat.le (Nat.succ Nat.zero) a` in the prelude
/// (`clean-kernel/src/env/nat_sub_order_remaining_proof.rs`), so keeping the
/// numerals in that spelling means every typing obligation here is exactly the
/// ONE δι step under measurement (the instance projection) and nothing else.
/// The surface numeral is measured separately below, and end-to-end in w10b.
fn cds_f_typeclass() -> Expr {
    cds_f_spelled(
        lt_tc(cnst("Nat.zero"), Expr::bvar(1)),
        Expr::apps(cnst("instDecidableNatLt"), [cnst("Nat.zero"), Expr::bvar(1)]),
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [
                    hsub_tc(Expr::bvar(2), nat_num(1)),
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    )
}

/// `LT.{0} Nat` — the type of an `LT Nat` instance.
fn lt_nat_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("LT"), vec![Level::zero()]), nat())
}

/// `@LT.mk.{0} Nat <rel>`.
fn lt_mk(rel: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]), [nat(), rel])
}

fn three_zero_levels() -> Vec<Level> {
    vec![Level::zero(), Level::zero(), Level::zero()]
}

/// `HSub.{0,0,0} Nat Nat Nat` — the type of a homogeneous `Nat` HSub instance.
fn hsub_nat_ty() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("HSub"), three_zero_levels()),
        [nat(), nat(), nat()],
    )
}

/// `@HSub.mk.{0,0,0} Nat Nat Nat <op>`.
fn hsub_mk(op: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("HSub.mk"), three_zero_levels()),
        [nat(), nat(), nat(), op],
    )
}

/// `fun (a b : Nat) => body`, with `a = bvar 1` and `b = bvar 0` inside.
fn nat_binop_lam(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat(), Expr::lam(BinderInfo::Default, nat(), body))
}

/// **The typeclass spellings are δι-ALIASES of the delta-unfolded ones — and
/// that is a measured kernel verdict, not a naming convention.**
///
/// Four ADMITs, each paired with a refusing control at the same layer per this
/// file's honesty rules:
///
/// * `@LT.lt.{0} Nat instLTNat 0 x ≡ Nat.lt 0 x` at an OPEN `x`, controlled by
///   a REVERSED `LT Nat` instance, which is a different relation and is NOT
///   identified. So the guard recognizer may read `instLTNat` by name and know
///   it has not admitted a second proposition — and may not read *any* `LT`
///   instance, because they do not all denote this order.
/// * `instDecidableNatLt ≡ Nat.decLt` — the wrapper's VALUE is the bare
///   constant. Controlled by `Nat.decLe`, a different decision procedure.
/// * `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat x 1 ≡ Nat.sub x 1` at an OPEN
///   `x`, controlled by an `HSub Nat Nat Nat` instance carrying `Nat.add`.
/// * `@OfNat.ofNat.{0} Nat k (instOfNatNat k)` is the same `Nat` as the succ
///   tower, controlled by an off-by-one.
///
/// If a control ever ADMITS, the by-name instance discipline in
/// `emit.rs`'s `is_zero_lt_param` / `read_wf_value` has stopped being
/// conservative and R2's fragment must be re-derived from a fresh measurement.
#[test]
fn probe_w10_typeclass_spellings_are_delta_aliases() {
    let mut env = Environment::with_prelude();

    // The PREMISE, asserted rather than assumed: every name the two typeclass
    // spellings are built from is in the PRODUCTION prelude this crate links
    // (the w0 discipline). If one is absent, nothing below means what it says.
    for name in [
        "LT", "LT.mk", "LT.lt", "instLTNat", "instDecidableNatLt", "Nat.decLt", "Nat.decLe",
        "HSub", "HSub.mk", "HSub.hSub", "instHSubNat", "OfNat.ofNat", "instOfNatNat",
    ] {
        assert!(
            has(&env, name),
            "the typeclass spelling of the emittable WF fragment rests on `{name}`, and \
             `with_prelude` does not carry it"
        );
    }

    // A REVERSED order: `fun a b => Nat.lt b a`. Well-typed as an `LT Nat`
    // instance and genuinely a different relation.
    let reversed = nat_binop_lam(nat_lt(Expr::bvar(0), Expr::bvar(1)));
    define(&mut env, "revLtNat", lt_nat_ty(), lt_mk(reversed));
    // An `HSub Nat Nat Nat` instance whose operation is ADDITION.
    define(&mut env, "addHSubNat", hsub_nat_ty(), hsub_mk(cnst("Nat.add")));

    let tc = TypeChecker::new(&env);
    let open = || Expr::bvar(0);

    assert!(
        tc.is_def_eq(&lt_tc(cnst("Nat.zero"), open()), &nat_lt(cnst("Nat.zero"), open())),
        "MEASURED: `@LT.lt.{{0}} Nat instLTNat 0 x ≡ Nat.lt 0 x` at an OPEN x — the \
         guard's two spellings are ONE proposition, by δι through `instLTNat`'s \
         projection, not by an identification the emitter asserts on its own authority"
    );
    assert!(
        !tc.is_def_eq(
            &lt_tc_with(nat(), cnst("revLtNat"), cnst("Nat.zero"), open()),
            &nat_lt(cnst("Nat.zero"), open())
        ),
        "CONTROL: a DIFFERENT `LT Nat` instance denotes a DIFFERENT relation and must \
         NOT be identified — this is why the guard reads the instance BY NAME and why \
         the δι-alias above is a δ-step rather than a collapse"
    );

    assert!(
        tc.is_def_eq(&cnst("instDecidableNatLt"), &cnst("Nat.decLt")),
        "MEASURED: `instDecidableNatLt`'s VALUE is the bare constant `Nat.decLt` — the \
         two names name ONE decision procedure, which is what lets the guard accept \
         both and no third"
    );
    assert!(
        !tc.is_def_eq(&cnst("instDecidableNatLt"), &cnst("Nat.decLe")),
        "CONTROL: a different decision procedure is not identified"
    );

    assert!(
        tc.is_def_eq(&hsub_tc(open(), nat_num(1)), &sub(open(), nat_num(1))),
        "MEASURED: `@HSub.hSub.{{0,0,0}} Nat Nat Nat instHSubNat x 1 ≡ Nat.sub x 1` at an \
         OPEN x — the third predecessor spelling is a δ-ALIAS of the second, not a \
         second operation"
    );
    assert!(
        !tc.is_def_eq(
            &Expr::apps(
                Expr::const_(Name::from_string("HSub.hSub"), three_zero_levels()),
                [nat(), nat(), nat(), cnst("addHSubNat"), open(), nat_num(1)],
            ),
            &sub(open(), nat_num(1))
        ),
        "CONTROL: an `HSub Nat Nat Nat` instance carrying `Nat.add` is NOT the \
         subtraction — this is why the predecessor arm reads `instHSubNat` by name \
         instead of accepting any HSub at Nat"
    );

    for k in [0u64, 1, 2] {
        assert!(
            tc.is_def_eq(&surface_num(k), &nat_num(k)),
            "MEASURED: the SURFACE numeral `@OfNat.ofNat.{{0}} Nat {k} (instOfNatNat {k})` \
             is the same `Nat` as the succ tower — the third numeral lane w9 never \
             measured, and the one the elaborator actually writes"
        );
    }
    assert!(
        !tc.is_def_eq(&surface_num(1), &nat_num(2)),
        "CONTROL: the numeral identification is value-sensitive"
    );

    eprintln!(
        "PROBE-ROW | w10 typeclass spellings      | LT.lt+instLTNat ≡ Nat.lt (reversed \
         instance: NOT) | instDecidableNatLt ≡ Nat.decLt (Nat.decLe: NOT) | \
         HSub.hSub+instHSubNat ≡ Nat.sub (Nat.add-carrying instance: NOT) | \
         OfNat.ofNat ≡ succ tower (off-by-one: NOT)"
    );
}

/// **The WHOLE `countdownSum` written the way the elaborator writes it is the
/// same function, at the F layer the R2 gate actually judges — and the R2
/// PLANNER reads it.**
///
/// The previous probe measured the pieces; this one measures that they compose,
/// which is the fact the gate rests on:
///
/// * the typeclass-spelled side A DEFINES (so every typing obligation the δι
///   steps carry is discharged by the real kernel, not asserted here);
/// * its `F` is kernel-defeq to `cds`'s `F` — the w6 judgment, and therefore
///   `check_faithful_wf_functional` admits the elaborator's spelling with NO
///   change to the gate;
/// * the per-constructor equations are still rfl and the closed values still
///   compute, so the identification is not confined to open terms;
/// * `plan_clean_origin_body` — the RECOGNIZER, the component that was
///   measured wrong — reads both spellings to the SAME shape;
/// * every one of those is paired with a wrong-F control at its own layer.
///
/// **What REFUSES the wrong-else sibling, named explicitly because one claimed
/// refuser was not real** (the header's 2026-08-25 amendment): the F-layer
/// defeq (`!is_def_eq(f_wrong, f_delta)`), the planner's shape comparison
/// (`plan_wrong.shape() != plan_delta.shape()`), the ZERO equation, and every
/// closed-value row. The SUCC equation is NOT one of them, and now says so in
/// an assertion instead of pretending otherwise.
#[test]
fn probe_w10_the_elaborators_functional_is_the_same_function() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");
    define(&mut env, "cdsTypeclass", Expr::arrow(nat(), nat()), wf_body(cds_f_typeclass()));
    // CONTROL siblings, in the SAME typeclass spelling with a wrong else-branch,
    // so neither the defeq nor the plan comparison below can be a collapse.
    // Parameterised by the else VALUE because the succ-equation row below has to
    // show its insensitivity is to the ARM, not a coincidence at the constant 1.
    let wrong_else_f = |else_value: Expr| {
        cds_f_spelled(
            lt_tc(cnst("Nat.zero"), Expr::bvar(1)),
            Expr::apps(cnst("instDecidableNatLt"), [cnst("Nat.zero"), Expr::bvar(1)]),
            add(
                Expr::bvar(2),
                Expr::apps(
                    Expr::bvar(1),
                    [
                        hsub_tc(Expr::bvar(2), nat_num(1)),
                        Expr::apps(
                            cnst("Nat.sub_lt"),
                            [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                        ),
                    ],
                ),
            ),
            else_value,
        )
    };
    define(
        &mut env,
        "cdsTypeclassWrongElse",
        Expr::arrow(nat(), nat()),
        wf_body(wrong_else_f(nat_num(1))),
    );

    // — THE RECOGNIZER: both spellings plan, to the SAME shape —
    let plan_delta = plan_clean_origin_body(&env, "cds").unwrap_or_else(|refusal| {
        panic!("the delta-unfolded side A must plan: {}", refusal.note())
    });
    let plan_tc = plan_clean_origin_body(&env, "cdsTypeclass").unwrap_or_else(|refusal| {
        panic!(
            "THE MEASURED DEFECT, IF THIS FIRES: the R2 recognizer refuses the spelling \
             the elaborator actually mints, which is the exact surface text its own \
             diagnostic advertises (`if h : 0 < n`, `n - 1`). Widen the recognizer, \
             never this probe. got: {}",
            refusal.note()
        )
    });
    assert_eq!(
        plan_tc.shape(),
        plan_delta.shape(),
        "both spellings of ONE function must read to ONE shape; a recognizer that reads \
         them differently has invented a distinction the kernel does not make"
    );
    assert_eq!(plan_tc.return_ty(), plan_delta.return_ty());
    // CONTROL: the shape comparison is a DECISION. A different else-branch, in
    // the same typeclass spelling, plans to a DIFFERENT shape.
    let plan_wrong = plan_clean_origin_body(&env, "cdsTypeclassWrongElse")
        .expect("the wrong-else sibling is still inside the fragment");
    assert_ne!(
        plan_wrong.shape(),
        plan_delta.shape(),
        "CONTROL: if a wrong else-branch plans to the same shape, the assertion above is \
         comparing nothing"
    );

    // — THE GATE'S OWN JUDGMENT: the two functionals are kernel-defeq —
    let body_delta = env
        .get_const(&Name::from_string("cds"))
        .and_then(|c| c.value.clone())
        .expect("side A body");
    let f_delta = parse_wf_fix_spine(&body_delta).expect("the delta side A parses").f;
    let f_typeclass = cds_f_typeclass();
    let f_wrong = parse_wf_fix_spine(
        &env.get_const(&Name::from_string("cdsTypeclassWrongElse"))
            .and_then(|c| c.value.clone())
            .expect("the control's body"),
    )
    .expect("the control parses")
    .f;

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&f_typeclass, &f_delta),
        "MEASURED (w6's judgment on the REAL spelling): the elaborator's functional is \
         kernel-defeq to this file's hand-built one, so `check_faithful_wf_functional` \
         admits it with NO change to the gate — the widening was a RECOGNIZER question \
         only"
    );
    assert!(
        !tc.is_def_eq(&f_wrong, &f_delta),
        "CONTROL: a wrong-VALUE functional in the SAME typeclass spelling is REFUSED at \
         the F layer — the defeq above is a verdict, not a spelling-blind pass"
    );

    // — CLOSED VALUES, on the real spelling AND on the control: the
    //   identification is not confined to open terms, and — the half the
    //   superseded pin was missing — a closed argument DOES reach the else arm,
    //   so this row separates the two siblings. Every `n` shifts by exactly the
    //   else value, because the else arm is evaluated exactly once, at the
    //   bottom of the recursion.
    for (n, correct, wrong) in [(0u64, 0u64, 1u64), (1, 1, 2), (3, 6, 7), (5, 15, 16)] {
        assert!(
            tc.is_def_eq(&Expr::app(cnst("cdsTypeclass"), nat_num(n)), &nat_num(correct)),
            "MEASURED: `cdsTypeclass {n} ≡ {correct}` — the typeclass spelling COMPUTES, \
             it is not merely convertible at open terms"
        );
        assert!(
            !tc.is_def_eq(&Expr::app(cnst("cdsTypeclassWrongElse"), nat_num(n)), &nat_num(correct)),
            "SOUNDNESS PIN (closed row): the wrong-else sibling must NOT compute \
             `cdsTypeclass`'s value at {n}. IF THIS FIRES, the else arm has stopped \
             being observable at a closed argument, and the F-layer defeq above is the \
             only thing left separating the two functions — re-derive both pins before \
             trusting either"
        );
        assert!(
            tc.is_def_eq(&Expr::app(cnst("cdsTypeclassWrongElse"), nat_num(n)), &nat_num(wrong)),
            "…and it computes {wrong} instead — recorded as a value, not merely as a \
             non-equality, so the control cannot drift into meaning something else"
        );
    }
    assert!(
        !tc.is_def_eq(&Expr::app(cnst("cdsTypeclass"), nat_num(5)), &nat_num(14)),
        "…and the computation pin is a decision"
    );
    drop(tc);

    // — THE ZERO EQUATION: the per-constructor row that DISCRIMINATES —
    //
    // `f 0 = 0` is the one equation whose statement forces the else arm, so it
    // is the one the two siblings must disagree on. Both directions asserted:
    // ADMIT for the elaborator's spelling, REFUSE for the wrong-else sibling.
    let zero_eq = |f: &str| eq_nat(Expr::app(cnst(f), nat_num(0)), nat_num(0));
    try_theorem(&mut env, "cdsTypeclass.eq_zero", zero_eq("cdsTypeclass"), refl_nat(nat_num(0)))
        .expect(
            "w2's `cds 0 = 0` restated on the REAL spelling: the base equation is still \
             rfl-definitional for the term the elaborator produces",
        );
    let err_zero = try_theorem(
        &mut env,
        "cdsTypeclassWrongElse.eq_zero",
        zero_eq("cdsTypeclassWrongElse"),
        refl_nat(nat_num(0)),
    )
    .expect_err(
        "SOUNDNESS PIN: the wrong-else sibling must REFUSE the ZERO equation. This is the \
         equation row whose statement REACHES the else arm, and therefore the only \
         per-constructor equation that can tell the two siblings apart — see the \
         2026-08-25 amendment in this file's header for the succ-equation pin it replaced",
    );
    assert!(
        err_zero.contains("TypeMismatch"),
        "the refusal must be the defeq TypeMismatch: {err_zero}"
    );
    eprintln!(
        "REFUSAL-DATA | w10 wrong-else sibling | TypeMismatch at cdsTypeclassWrongElse.eq_zero"
    );

    // — THE SUCC EQUATION: an ADMIT for the real spelling, and a MEASURED
    //   NON-DISCRIMINATOR, asserted in BOTH directions so the negative result
    //   is a recorded verdict rather than an omission.
    //
    // `f (succ k) = succ k + f k` is STRUCTURALLY INSENSITIVE to the else arm:
    // `0 < succ k` is decidably TRUE, the `dite` takes the then-branch on both
    // sides, and the else value never appears in either term. w2 states the
    // same equation about `cds` and its wrong-VALUE sibling `cds_mut`, where it
    // IS a discriminator — because that mutation is in the THEN arm, which this
    // equation does reach. Which arm a mutation lives in decides which equation
    // can see it; that is the distinction the superseded pin here did not make.
    let succ_eq = |f: &str| {
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(
                Expr::app(cnst(f), succ(Expr::bvar(0))),
                add(succ(Expr::bvar(0)), Expr::app(cnst(f), Expr::bvar(0))),
            ),
        )
    };
    let succ_rfl = |f: &str| {
        Expr::lam(BinderInfo::Default, nat(), refl_nat(Expr::app(cnst(f), succ(Expr::bvar(0)))))
    };
    try_theorem(
        &mut env,
        "cdsTypeclass.eq_succ",
        succ_eq("cdsTypeclass"),
        succ_rfl("cdsTypeclass"),
    )
    .expect(
        "w2's headline restated on the REAL spelling: the per-constructor equation is \
         still rfl-definitional at an OPEN k",
    );
    // A SECOND wrong-else sibling with a different constant, so the insensitivity
    // below is measured as a property of the ARM and not as a coincidence at 1.
    define(
        &mut env,
        "cdsTypeclassWrongElse7",
        Expr::arrow(nat(), nat()),
        wf_body(wrong_else_f(nat_num(7))),
    );
    for sibling in ["cdsTypeclassWrongElse", "cdsTypeclassWrongElse7"] {
        try_theorem(&mut env, &format!("{sibling}.eq_succ"), succ_eq(sibling), succ_rfl(sibling))
            .unwrap_or_else(|e| {
                panic!(
                    "MEASURED NON-DISCRIMINATOR (asserted, not assumed): `{sibling}` \
                     satisfies the SUCC equation too, for ANY else value, because the \
                     equation never reaches the else arm. If this ever REFUSES, the kernel \
                     has started distinguishing terms that agree on every reachable branch \
                     — re-derive this probe's pins and w2's before trusting either: {e}"
                )
            });
    }
    // …and the zero equation still separates the second sibling too, which is
    // what makes the pair above a statement about the ARM.
    try_theorem(
        &mut env,
        "cdsTypeclassWrongElse7.eq_zero",
        zero_eq("cdsTypeclassWrongElse7"),
        refl_nat(nat_num(0)),
    )
    .expect_err("the zero equation discriminates at BOTH wrong else values, not just at 1");

    eprintln!(
        "PROBE-ROW | w10 the elaborator's side A  | typeclass-spelled countdownSum: \
         DEFINES | F-layer defeq to the delta-spelled one: ADMIT (wrong-else sibling: \
         REFUSED) | plan_clean_origin_body: SAME shape (wrong-else: DIFFERENT shape) | \
         closed values 0/1/3/5 ≡ 0/1/6/15 (wrong-else: 1/2/7/16) | ZERO equation: rfl \
         ADMIT (wrong-else, both values: REFUSED) | SUCC equation: rfl ADMIT — and a \
         MEASURED NON-DISCRIMINATOR, the wrong-else siblings satisfy it too"
    );
}

/// **w10b — THE SAME QUESTION PUT TO THE REAL ISLAND ELABORATOR, because a
/// hand-built spelling is not evidence about what the elaborator produces.**
///
/// This is `fragment_widening_probes`' `probe_i3` discipline on the R2 lane:
/// side A comes from `CleanIslandSession::check_all` — the exact pipeline
/// `clean_origin_mir` drives — and the ONLY load-bearing assertion is that the
/// planner reads THAT tree. Nothing here pins a particular head name, so the
/// probe does not go red merely because the elaborator changed how it spells a
/// numeral; it goes red when the planner can no longer read what the
/// elaborator writes, which is the defect this row exists to catch. The heads
/// actually observed are printed as the recorded measurement.
///
/// If the island REJECTS the source, that is a finding about the elaborator's
/// WF phase-1 limits (`clean-elab/src/infer/wf_recursion/mod.rs`: one
/// parameter, `Nat` measure, cascade-dischargeable decrease), not about this
/// probe — record the rejection and re-derive, never soften the assertion.
#[test]
fn probe_w10b_the_real_island_elaboration_plans() {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[
        "def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0\n\
         termination_by n",
    ]);
    assert!(
        !batch.is_rejected(),
        "the island must kernel-check the measured-ADMITTED `countdownSum` \
         (`recursion_boundary_probes` module table, the countdownSum row). If it no \
         longer does, the elaborator's WF phase-1 limits moved and R2's fragment must \
         be re-derived: {batch:?}"
    );
    let env = session.environment().expect("an untainted session has an environment");

    // THE LOAD-BEARING ROW: the planner reads the REAL elaborated tree.
    let plan = plan_clean_origin_body(env, "countdownSum").unwrap_or_else(|refusal| {
        panic!(
            "THE C9 DEFECT, RESTATED ON R2: the planner refuses the tree the REAL \
             elaborator produces for the exact surface text the WF refusal advertises. \
             Every hand-built probe in this file can be green while this is red — that \
             is the whole reason this row exists. got: {}",
            refusal.note()
        )
    });

    // The shape is the one the emitter is built for, compared against a
    // hand-built side A rather than spelled out again here — so this row cannot
    // drift from w10's.
    let mut mirror = Environment::with_prelude();
    install_cds(&mut mirror, "cds");
    let mirrored = plan_clean_origin_body(&mirror, "cds").expect("the hand-built mirror plans");
    assert_eq!(
        plan.shape(),
        mirrored.shape(),
        "the REAL elaboration and this file's hand-built mirror must read to ONE shape; \
         if they do not, the mirror is the thing that is wrong"
    );
    assert_eq!(plan.return_ty(), mirrored.return_ty());

    // THE RECORDED MEASUREMENT: which spellings the elaborator actually used.
    //
    // Deliberately NOT an assertion. The load-bearing verdict is above; this is
    // the row that lets a reader see WHAT was read, and it must not be able to
    // fail the probe for a reason the probe is not about — the w5 parse below
    // accepts only the ETA-EXPANDED spine, and `recognise_wf_nat_rec` accepts
    // the contracted one too, so a contracted elaboration would panic here
    // while the thing under test had already passed.
    let head_name = |e: &Expr| {
        let mut cursor = strip_mdata(e);
        while let ExprKind::App(function, _) = cursor.kind() {
            cursor = strip_mdata(function);
        }
        match cursor.kind() {
            ExprKind::Const(n, levels) => format!("{n}.{levels:?}"),
            other => format!("{other:?}"),
        }
    };
    let observed = env
        .get_const(&Name::from_string("countdownSum"))
        .and_then(|c| c.value.clone())
        .and_then(|body| parse_wf_fix_spine(&body).ok())
        .and_then(|spine| {
            let ExprKind::Lam(_, _, after_x) = strip_mdata(&spine.f).kind() else {
                return None;
            };
            let ExprKind::Lam(_, _, functional_body) = strip_mdata(after_x).kind() else {
                return None;
            };
            let mut cursor = strip_mdata(functional_body);
            let mut args: Vec<Expr> = Vec::new();
            while let ExprKind::App(function, argument) = cursor.kind() {
                args.push(strip_mdata(argument).clone());
                cursor = strip_mdata(function);
            }
            args.reverse();
            Some((head_name(cursor), args))
        });
    let (case_head, guard_head, dec_head) = match observed {
        Some((head, args)) => (
            head,
            args.get(1).map_or_else(|| "<none>".to_owned(), head_name),
            args.get(2).map_or_else(|| "<none>".to_owned(), head_name),
        ),
        None => (
            "<not the eta-expanded spine the w5 parse reads>".to_owned(),
            "<unread>".to_owned(),
            "<unread>".to_owned(),
        ),
    };
    eprintln!(
        "PROBE-ROW | w10b REAL island elaboration | plan: ADMIT, shape identical to the \
         hand-built mirror | observed case-split head: {case_head} | observed guard: \
         {guard_head} | observed decidability instance: {dec_head}"
    );
}
