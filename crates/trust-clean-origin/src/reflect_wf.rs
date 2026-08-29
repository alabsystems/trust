// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Side B for WELL-FOUNDED-recursion emissions (R2)** — the reflection mint
//! that turns a recognized [`WfRecBody`] (read out of the EMITTED MIR by
//! `trust_types::admissible_body::recognize_wf_nat_rec`) into the
//! [`ReflectedWfFunctional`] that [`crate::gate::check_faithful_wf_functional`]
//! decides over.
//!
//! # FROZEN against the lane it feeds
//!
//! This module is a side-B producer, under the same standing prohibition as
//! `crates/trust-clean/src/reflect.rs`, [`crate::reflect_rec`] and
//! `recognize_structural_rec`: **if a Clean-origin body fails the gate, the fix
//! is NEVER an edit here.** Editing the reflection to make side B agree with
//! side A converts the gate into a round trip. Its output is a CLAIM — every
//! part of it is re-decided against the kernel by the gate, which is the only
//! place a [`crate::gate::Faithful`] can come from.
//!
//! # THE TWO PROHIBITIONS THIS MODULE IS SHAPED BY
//!
//! 1. **The defined constant is unnameable in a rendered term.** §6e's
//!    amendment turns on side B never citing it: probe s2 measured the
//!    constant-citing spelling VACUOUS as a gate (it admits a diverging
//!    off-by-one body), and the §6e MEASUREMENT NOTE records that a
//!    `SelfCall { arg }`-style reflection — one that spells the recursive
//!    occurrence as the constant applied to an argument — reopens exactly that
//!    class. Here the recursive occurrence is `rec <argument> <slot>`, where
//!    `rec` is the FUNCTIONAL'S OWN BINDER (`Expr::bvar(1)` at every rendering
//!    site). As in [`crate::reflect_rec`], the prohibition is enforced by a
//!    TYPE and not by a reading: every constant a rendering can name goes
//!    through [`cnst`], whose parameter is `&'static str`, while the
//!    declaration name arrives as an ordinary `&str`. There is no way to render
//!    it.
//! 2. **Side B may not author a decrease proof.** MIR contains no proof terms,
//!    so every `r y x` slot is written as the sentinel
//!    [`crate::gate::DECREASE_SLOT_SENTINEL`] and BORROWED from side A's own
//!    kernel-checked declaration by the gate. Probe c5 measures that even a
//!    *correct* emitter-authored proof is refused, because "correct" is exactly
//!    what the gate would otherwise take on trust — the term's axiom closure is
//!    the termination evidence (probe c1: one assumed decrease makes a
//!    diverging functional kernel-check and ADMIT).
//!
//! # The renderings, each with its measurement
//!
//! Every rendering site sits under the functional's `N + 1` binders plus the
//! `dite` branch's hypothesis binder, so ONE de Bruijn layout serves both
//! branches. **R3a (2026-08-26) made that layout a function of the ARITY `N`**
//! rather than three literals; it is computed in one place,
//! [`crate::reflect::RecCall`], and at `N = 1` every index below is the
//! constant R2 shipped:
//!
//! ```text
//! x = bvar (N+1)      rec = bvar N      branch hypothesis = bvar 0
//! the j-th THREADED parameter (source order) = bvar (N-1-j)
//! ```
//!
//! The reflection is a DUMB reading of the recognized dataflow, never
//! pre-simplified — the KERNEL does the reduction, and the reflector stays too
//! simple to smuggle in a semantic step.
//!
//! | node | rendering | measurement |
//! |---|---|---|
//! | `Decreasing` | `bvar (N+1)` — the functional's MEASURE parameter | w1 pins `F : (x : Nat) → ((y : Nat) → Nat.lt y x → Nat) → Nat` at `N = 1`; `r7` q1 reads `bvar 3` at `N = 2` |
//! | `Param(i)` | `bvar (N-1-j)` — a THREADED parameter, at the index its binder sits at | `r7` q1 (the layout) + q3 (the kernel DECIDES parameter order: `sel a b = b` admits, `sel a b = a` is refused) |
//! | `Pred` | `Nat.sub x 1` — what the MIR computes (`Nat::sub(&n, &from_u64(1))`), never pre-reduced to a binder | w6 (b′): the defeq-equal `Nat.pred x` spelling admits too, so the comparison is defeq and not syntax |
//! | `Rec` | `rec <decreasing> Trust.CleanOrigin.decreaseSlot <threaded…>` | w7/d2 (the slot is defeq-irrelevant, hence borrowable) + c5 (an authored slot is refused); `r7` q1 measures the 3-argument spine at `N = 2` |
//! | `NatConst(c)` | `c` (kernel literal) | e5 — literal↔constructor bridging (`nat_lit 0 ≡ Nat.zero`) |
//! | `Add` | `Nat.add _ _` | e4/e5; s8 bridges the surface `HAdd` spelling |
//! | `Mul` | `Nat.mul _ _` | `r6` q7 |
//!
//! # R3d (2026-08-27): the SECOND telescope, and the second borrow
//!
//! `first-party/clean` lowers a `termination_by` measure that names SEVERAL
//! parameters as a course-of-values recursion on the measure's VALUE (WF phase
//! 3). Its functional binds `n, rec, p⃗, hm` — `arity + 3` binders — where phase
//! 2 binds `x, rec, threaded…`, and its self-call is
//! `rec <measure> <hm> <p⃗> <proof>`. `reflect_wf_functional` renders both,
//! selected by its `lowering` parameter; the per-node vocabulary and the arm
//! polarity are shared and unchanged.
//!
//! **The rendering site indices at phase 3, measured on the elaborated `gcdB`
//! (`gcd_phase3_probes` p2), under a branch binder:**
//!
//! ```text
//! n = bvar (N+3)   rec = bvar (N+2)   hm = bvar 1   branch hypothesis = bvar 0
//! source parameter i = bvar (N+1-i)      -- the GUARDED one included
//! ```
//!
//! Note what is NOT there: phase 3 has no privileged measure binder, so
//! `Decreasing` (the guarded parameter) and `Param(i)` use ONE formula. That is
//! the whole index difference, and [`crate::reflect::RecCall`] computes it.
//!
//! **THE THIRD PROHIBITION, which phase 3 adds: side B may not author the
//! MEASURE.** It occupies the `rec` binder's type, the `hm` binder's type and
//! each self-call's major premise, and MIR contains no measure at all — the
//! emitted body computes a guard, two branch values and a self-call's arguments,
//! and nothing else. All three positions are rendered as
//! [`MEASURE_SLOT_SENTINEL`] and BORROWED by the gate from side A's own
//! functional at the same position. Same mechanism as the decrease slot, same
//! enforcement: the sentinel must not resolve, and a sentinel written anywhere
//! else — or a term written at a borrowed position, even the right one — is
//! refused (`control_18` (f), `gcd_phase3_probes` p4).
//!
//! and the scaffold the two arms hang on, which is the ZERO TEST the emitted
//! MIR performs, rendered as the decidable guard side A's WF lowering uses:
//!
//! ```text
//! fun (x : Nat) (rec : (y : Nat) → Nat.lt y x → Nat^(N-1) → Nat)
//!    (threaded : Nat)^(N-1) =>
//!   @dite.{1} Nat (Nat.lt Nat.zero x) (Nat.decLt Nat.zero x)
//!     (fun (h : Nat.lt Nat.zero x) => <nonzero_value>)
//!     (fun (_ : Not (Nat.lt Nat.zero x)) => <zero_value>)
//! ```
//!
//! **The threaded binders' ORDER is the contract.** They are bound in SOURCE
//! order, outermost first, so parameter `i` is at a different index depending on
//! where the measure sits — `r7` q1 measures both cases (`addAcc`, measure at
//! source 0; `addAcc2`, measure at source 1). `control_16` (f) is the mutation
//! row that requires a wrong index to be caught, structurally and at the kernel.
//!
//! **The arm swap is the contract, and it is the mutation control's subject.**
//! The MIR's `is_zero` TRUE arm is the `dite` ELSE branch and its FALSE arm is
//! the THEN branch; getting that inversion backwards is the one-construct
//! mistranslation this producer can make, and `control_8`'s swapped-cases row
//! requires it to be caught.
//!
//! # Why NOTHING here is kernel-checked, and where the check went instead
//!
//! [`crate::reflect_rec`] full-kernel-checks each minted term in a scratch
//! clone. This module deliberately cannot: the functional it renders carries
//! the decrease-slot sentinel, a constant that must NOT exist in the
//! environment (the gate refuses if it resolves). The check is not dropped —
//! it MOVES, and it moves to a strictly better place: the gate type-checks the
//! functional AFTER the borrow, at side A's own functional type
//! (`check_faithful_wf_functional` step 7), which is the term the kernel is
//! actually handed, and then audits its axiom closure (step 7b). A pre-borrow
//! check here would have to be run against a term the kernel never sees.
//!
//! What this module still owes, and does: the structural preconditions of the
//! fragment, restated fail-closed rather than inherited (the controls call this
//! function DIRECTLY, so on the fast lane the recognizer is not in front of
//! it), and a demand-driven environment preflight so a missing prelude constant
//! is named (v7/D3) instead of surfacing as an opaque kernel refusal about a
//! term nobody wrote.

//!
//! # SINCE §6f LANDING 1: the rendering is the SHARED descent
//!
//! The per-node `render` that used to live here is now
//! [`crate::reflect::render_rec_node`] — ONE recursive descent, driven by
//! [`crate::table`], serving R2's three sites and R1's three. Nothing about the
//! terms changed: the local `Site { Zero, Nonzero, RecArg }` became
//! `Site { WfZero, WfNonzero, WfRecArg }` with the same fixed de Bruijn layout
//! (`x = bvar 2`, `rec = bvar 1`), and the node vocabulary's kernel constants
//! moved from match arms into the rows that name them. This function keeps its
//! signature, its structural preconditions, its sentinel check and its
//! demand-driven preflight, and `docs/TCB.md` still names it as R2's side-B
//! producer.

use std::collections::BTreeSet;

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use trust_types::admissible_body::{RecBodyExpr, WfRecBody};

use crate::emit::WfLowering;
use crate::gate::{DECREASE_SLOT_SENTINEL, MEASURE_SLOT_SENTINEL, ReflectedWfFunctional};
use crate::reflect::{RecCall, RecFamily, Site, cnst, render_rec_node};

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// R2's half of the shared descent: render one recognized node at one of R2's
/// three sites. `rec_arg` IS read here — the functional puts the self-call
/// argument inline in its own `rec` slot, which is why R2 has no separate
/// argument site to compare and the gate decides the argument by TYPING
/// instead (probe w7/d1).
fn render(
    name: &str,
    node: &RecBodyExpr,
    site: Site,
    ctx: RecCall<'_>,
    named: &mut BTreeSet<&'static str>,
) -> Result<Expr, String> {
    render_rec_node(RecFamily::WellFounded, name, node, site, ctx, named)
}

/// Mint side B for a well-founded-recursion emission: the functional, with
/// every decrease slot left as [`DECREASE_SLOT_SENTINEL`].
///
/// `body` is `recognize_wf_nat_rec`'s reading of the EMITTED body — never the
/// plan's shape — for the module-doc reason: side B must be a reading of what
/// was emitted.
///
/// # Errors
///
/// A `String` detail, which `emit::admit_lowering` wraps in
/// [`crate::emit::EmitRefusal::ReflectionRejected`]:
///
/// * the recognized tree violates a structural precondition of the fragment
///   (re-stated here rather than inherited — this producer must be sound
///   alone, and the controls call it with the recognizer removed);
/// * a node has no reading at its site (the fail-closed vocabulary);
/// * the decrease-slot sentinel resolves to a real declaration, so a borrowed
///   slot could not be told apart from a term someone declared;
/// * a kernel constant the rendering names is absent from `env`.
///
/// All of them are producer-chain defects, not user-actionable refusals, and
/// there is no degraded rendering.
/// # R3d: the `lowering` parameter, and why it is NOT side A co-authoring
///
/// `lowering` says which TELESCOPE to render — phase 2's `x, rec, threaded…` or
/// phase 3's `n, rec, p⃗, hm`. It is a SHAPE, not a term: it carries no value,
/// no argument and no branch, and the gate re-derives it for itself from side
/// A's own spine (`parse_wf_fix_spine`) rather than being told. A wrong
/// `lowering` here produces a functional whose telescope disagrees with side
/// A's, which `peel_functional` refuses on the binder count — it cannot admit.
///
/// What side B genuinely cannot author at phase 3 is the MEASURE, and it is not
/// smuggled in through this parameter: every position the measure occupies —
/// the recursive slot's type, the hypothesis binder's type, and each self-call's
/// major premise — is written as [`MEASURE_SLOT_SENTINEL`] and BORROWED at the
/// gate, exactly as the decrease proof already was. See
/// [`crate::gate::check_faithful_wf_functional`]'s step 5.
pub fn reflect_wf_functional(
    env: &Environment,
    name: &str,
    body: &WfRecBody,
    lowering: WfLowering,
) -> Result<ReflectedWfFunctional, String> {
    // ── 1. Structural preconditions, restated fail-closed ──────────────────
    if body.zero_value.contains(&RecBodyExpr::Rec) || body.zero_value.contains(&RecBodyExpr::Pred) {
        return Err(format!(
            "cannot reflect the well-founded recursion emitted for `{name}`: its zero-arm \
             value contains the self-call result or the predecessor, neither of which has a \
             reading under a parameter the zero test reported ZERO. This is a \
             producer-chain defect; please report it."
        ));
    }
    if body.nonzero_value.count(&RecBodyExpr::Rec) != 1 {
        return Err(format!(
            "cannot reflect the well-founded recursion emitted for `{name}`: its nonzero-arm \
             value contains {} self-call result(s) where the single-call fragment admits \
             exactly one. A body with none is not a recursion (route it through the \
             non-recursive lane, `check_faithful`); a body with several is outside this \
             fragment — the gate's borrow pairs side B's call sites with side A's one at a \
             time and would refuse on the count, but a producer must not hand it a term it \
             knows is out of fragment. This is a producer-chain defect; please report it.",
            body.nonzero_value.count(&RecBodyExpr::Rec)
        ));
    }
    // ARITY, restated fail-closed. The layout below is a function of it, and
    // the controls call this producer with the recognizer removed, so it is
    // read from the recognized body and checked here rather than assumed.
    let arity = body.rec_args.len();
    if arity == 0 || body.measure_index >= arity {
        return Err(format!(
            "cannot reflect the well-founded recursion emitted for `{name}`: it carries {arity} \
             self-call argument(s) with its measure at parameter {}, which is not a parameter \
             layout — the functional binds one binder per parameter and the measure must be one \
             of them. This is a producer-chain defect; please report it.",
            body.measure_index
        ));
    }
    for (index, argument) in body.rec_args.iter().enumerate() {
        if argument.contains(&RecBodyExpr::Rec) {
            return Err(format!(
                "cannot reflect the well-founded recursion emitted for `{name}`: its self-call \
                 argument at source parameter {index} contains the self-call result. An argument \
                 computed from the call's own result is not a well-founded recursion, and side \
                 A's decrease proof could not be borrowed for it. This is a producer-chain \
                 defect; please report it."
            ));
        }
    }
    // NOTE what is deliberately NOT restated here: that the MEASURE argument is
    // the predecessor. That confinement belongs to the plan and the recognizer;
    // this producer must render whatever reading it is handed and let the GATE
    // decide it, because the gate's decision is the kernel's (probe c6 — a
    // non-decreasing argument cannot take side A's borrowed proof). Restating
    // it here would move a kernel question into a Rust `if`.

    // ── 2. The sentinel must not resolve ───────────────────────────────────
    //
    // The gate checks this too, and deliberately: this producer must be sound
    // alone. A sentinel that names a real declaration would let the kernel
    // type-check an UNBORROWED slot, which is the one thing the borrow exists
    // to prevent.
    for sentinel in [DECREASE_SLOT_SENTINEL, MEASURE_SLOT_SENTINEL] {
        if env.get_const(&Name::from_string(sentinel)).is_some() {
            return Err(format!(
                "cannot reflect the well-founded recursion emitted for `{name}`: the borrow \
                 sentinel `{sentinel}` resolves to a real declaration in this environment, so a \
                 slot side B left for the gate to borrow could not be told apart from a term \
                 someone declared. This is a producer-chain defect; please report it."
            ));
        }
    }

    // ── 3. Render, recording every constant the terms name ─────────────────
    //
    // `Nat` is seeded because the binder types below always name it.
    let ctx = RecCall {
        args: &body.rec_args,
        arity,
        measure_index: body.measure_index,
        lowering,
    };
    let mut named = BTreeSet::from(["Nat"]);
    let nonzero = render(name, &body.nonzero_value, Site::WfNonzero, ctx, &mut named)?;
    let zero = render(name, &body.zero_value, Site::WfZero, ctx, &mut named)?;

    // The guard, the decidability instance, and the two branch binder types.
    // `Nat.lt Nat.zero x` is the proposition the emitted `is_zero` test decides;
    // the MIR's TRUE arm is this `dite`'s ELSE branch, which is the whole
    // polarity contract (module docs).
    let guard = |named: &mut BTreeSet<&'static str>, x: Expr| {
        Expr::apps(cnst("Nat.lt", named), [cnst("Nat.zero", named), x])
    };
    // AT THE FUNCTIONAL BODY the GUARDED parameter is:
    //
    //   phase 2 — `bvar arity`, under `x`, `rec` and the (arity-1) threaded
    //     binders; under a branch binder one further out. At arity 1 that is
    //     `bvar 1` / `bvar 2`, the pair R2 shipped, and `r7` q1 measured the
    //     elaborator using `bvar 2` at arity 2.
    //   phase 3 — `bvar (arity - measure_index)`, under `n`, `rec`, ALL the
    //     parameters and `hm`. Measured on the elaborated `gcdB`: arity 2,
    //     guard on source 1, `bvar 1` (`gcd_phase3_probes` p2).
    let measure_at_body = match lowering {
        WfLowering::OnParameter => u32::try_from(arity).unwrap_or(u32::MAX),
        WfLowering::OnMeasureValue => {
            u32::try_from(arity.saturating_sub(body.measure_index)).unwrap_or(u32::MAX)
        }
    };
    let guard_at_body = guard(&mut named, Expr::bvar(measure_at_body));
    let decidable = Expr::apps(cnst("Nat.decLt", &mut named), [
        cnst("Nat.zero", &mut named),
        Expr::bvar(measure_at_body),
    ]);
    let not_guard = Expr::app(cnst("Not", &mut named), guard_at_body.clone());
    let dite = {
        named.insert("dite");
        Expr::const_(Name::from_string("dite"), vec![lvl1()])
    };

    // The `dite` sits under the WHOLE telescope, which is the ONE thing the
    // lowering changes about this producer.
    // Built directly rather than through `cnst`, whose `&'static str` parameter
    // is the mechanism that makes the DECLARATION's name unrenderable; the
    // sentinel is recorded in `named` explicitly at its one use site below.
    let measure_sentinel = || Expr::const_(Name::from_string(MEASURE_SLOT_SENTINEL), vec![]);
    let dite_app = Expr::apps(dite, [
        nat(),
        guard_at_body.clone(),
        decidable,
        Expr::lam(BinderInfo::Default, guard_at_body, nonzero),
        Expr::lam(BinderInfo::Default, not_guard, zero),
    ]);
    let functional = match lowering {
        // PHASE 2 — `fun (x : Nat) (rec : (y : Nat) → Nat.lt y x → Nat^(N-1) →
        // Nat) (threaded : Nat)^(N-1) => dite …`. The threaded binders are
        // wrapped around the `dite` from the inside out so their source order is
        // the order `RecCall::other_bvar` indexes them at. Rendered wholly from
        // side B's own reading; the gate re-clothes nothing and type-checks the
        // whole term at SIDE A's functional type, which is where a slot type
        // that disagreed with side A's motive is caught.
        WfLowering::OnParameter => {
            let rec_slot_ty = {
                let lt = Expr::apps(cnst("Nat.lt", &mut named), [Expr::bvar(0), Expr::bvar(1)]);
                let mut result = nat();
                for _ in 0..arity - 1 {
                    result = Expr::arrow(nat(), result);
                }
                Expr::pi(BinderInfo::Default, nat(), Expr::arrow(lt, result))
            };
            let mut functional = dite_app;
            for _ in 0..arity - 1 {
                functional = Expr::lam(BinderInfo::Default, nat(), functional);
            }
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, rec_slot_ty, functional),
            )
        }
        // PHASE 3 (R3d) — `fun (n : Nat) (rec : ⟨borrowed⟩) (p⃗ : Nat)
        // (hm : ⟨borrowed⟩) => dite …`.
        //
        // TWO binder TYPES are the measure's, and MIR contains no measure:
        //
        //   rec : (k : Nat) → Nat.lt k n → (Π p⃗, Nat.lt m[p⃗] k → Nat)
        //   hm  : Nat.lt m n
        //
        // Both mention `m`, the `termination_by` term, which the emitted body
        // holds no trace of. Side B writes the bare `MEASURE_SLOT_SENTINEL` in
        // each and the gate replaces it with side A's own type AT THAT SAME
        // BINDER POSITION — the decrease-proof borrow, applied to the two
        // remaining positions that are plumbing rather than program. Side B
        // still authors every binder it CAN: `n` and all `arity` parameters are
        // `Nat`, written here.
        //
        // A stray sentinel anywhere else is refused by the gate's rebuild, so
        // this is a fixed four-position borrow and not a licence.
        WfLowering::OnMeasureValue => {
            named.insert(MEASURE_SLOT_SENTINEL);
            let mut functional =
                Expr::lam(BinderInfo::Default, measure_sentinel(), dite_app);
            for _ in 0..arity {
                functional = Expr::lam(BinderInfo::Default, nat(), functional);
            }
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, measure_sentinel(), functional),
            )
        }
    };

    // ── 4. Environment preflight, DEMAND-DRIVEN ────────────────────────────
    //
    // The gate's type check would already refuse a term naming an absent
    // constant, but as an opaque failure about a term nobody wrote. This says
    // WHAT is missing (v7/D3), and only about constants step 3 actually named,
    // so it never refuses an environment that lacks something this body does
    // not use. The SENTINEL is excluded by construction: it is the one name
    // that must be absent.
    for &constant in &named {
        if constant == DECREASE_SLOT_SENTINEL || constant == MEASURE_SLOT_SENTINEL {
            continue;
        }
        if env.get_const(&Name::from_string(constant)).is_none() {
            return Err(format!(
                "cannot reflect the well-founded recursion emitted for `{name}`: the kernel \
                 environment has no `{constant}`, which the rendering names. This is a \
                 producer-chain defect, not a user error: side B is being minted against an \
                 environment that does not carry the `Nat` prelude the fragment is stated \
                 over. Please report it."
            ));
        }
    }

    Ok(ReflectedWfFunctional { functional })
}

#[cfg(test)]
mod tests {
    //! The producer's own coverage. `control_8` exercises it through the whole
    //! route; these pin the checks that route cannot reach — the structural
    //! preconditions of step 1, which exist precisely because the fast lane
    //! calls this function with the recognizer removed.

    use clean_kernel::{Declaration, Environment, Name};

    use super::{RecBodyExpr, WfLowering, WfRecBody, nat, reflect_wf_functional};

    fn cds_body() -> WfRecBody {
        WfRecBody {
            zero_value: RecBodyExpr::NatConst(0),
            nonzero_value: RecBodyExpr::Add(
                Box::new(RecBodyExpr::Decreasing),
                Box::new(RecBodyExpr::Rec),
            ),
            rec_args: vec![RecBodyExpr::Pred],
            measure_index: 0,
        }
    }

    #[test]
    fn the_countdown_sum_body_reflects() {
        let reflected =
            reflect_wf_functional(
                &Environment::with_prelude(),
                "countdownSum",
                &cds_body(),
                WfLowering::OnParameter,
            )
                .expect("the in-fragment body must reflect");
        // The rendered functional binds exactly two binders before the `dite`.
        assert!(matches!(reflected.functional.kind(), clean_kernel::ExprKind::Lam(..)));
    }

    #[test]
    fn a_nonzero_arm_without_exactly_one_recursive_result_is_refused() {
        let env = Environment::with_prelude();
        for nonzero in [
            RecBodyExpr::NatConst(1),
            RecBodyExpr::Add(Box::new(RecBodyExpr::Decreasing), Box::new(RecBodyExpr::NatConst(1))),
            RecBodyExpr::Add(Box::new(RecBodyExpr::Rec), Box::new(RecBodyExpr::Rec)),
        ] {
            let detail = reflect_wf_functional(
                &env,
                "f",
                &WfRecBody { nonzero_value: nonzero, ..cds_body() },
                WfLowering::OnParameter,
            )
            .expect_err("outside the single-call fragment");
            assert!(
                detail.contains("nonzero-arm value") && detail.contains("exactly one"),
                "the refusal must name the position and the contract: {detail}"
            );
        }
    }

    #[test]
    fn the_zero_arm_may_not_read_the_recursion_or_the_predecessor() {
        let env = Environment::with_prelude();
        for zero in [
            RecBodyExpr::Rec,
            RecBodyExpr::Pred,
            RecBodyExpr::Add(Box::new(RecBodyExpr::NatConst(1)), Box::new(RecBodyExpr::Pred)),
        ] {
            let detail =
                reflect_wf_functional(
                    &env,
                    "f",
                    &WfRecBody { zero_value: zero, ..cds_body() },
                    WfLowering::OnParameter,
                )
                    .expect_err("no zero-arm reading exists for either node");
            assert!(detail.contains("zero-arm value"), "must name the position: {detail}");
        }
    }

    #[test]
    fn the_self_call_argument_may_not_read_the_recursion() {
        let detail = reflect_wf_functional(
            &Environment::with_prelude(),
            "f",
            &WfRecBody { rec_args: vec![RecBodyExpr::Rec], ..cds_body() },
            WfLowering::OnParameter,
        )
        .expect_err("an argument computed from the call's own result is not well-founded");
        assert!(detail.contains("self-call argument"), "must name the position: {detail}");
    }

    /// A sentinel that RESOLVES would let the kernel type-check an unborrowed
    /// slot — the one thing the borrow exists to prevent. The producer refuses
    /// on its own, without the gate in front of it.
    #[test]
    fn a_resolvable_sentinel_is_refused_by_the_producer_alone() {
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(super::DECREASE_SLOT_SENTINEL),
            level_params: vec![],
            type_: nat(),
        })
        .expect("an axiom may be declared");
        let detail = reflect_wf_functional(&env, "f", &cds_body(), WfLowering::OnParameter)
            .expect_err("a resolvable sentinel must refuse");
        assert!(detail.contains("resolves to a real declaration"), "{detail}");
    }
}
