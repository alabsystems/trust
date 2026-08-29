// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Side B for structural-recursion emissions** — the reflection mint that
//! turns a recognized [`StructuralRecBody`] (read out of the EMITTED MIR by
//! `trust_types::admissible_body::recognize_structural_rec`) into the kernel
//! terms [`crate::gate::check_faithful_equations`] decides over.
//!
//! # RECONCILIATION NOTE (2026-08-22) — this file had TWO authors
//!
//! Two sessions wrote this module independently and neither saw the other:
//!
//! * **A** — commit `1a6e56493ea` ("RECURSION RUNS"), which added the file
//!   together with `tests/control_7_structural_rec_emitter_mutation.rs` and
//!   carries the measured end-to-end run (`tozero(3) == 0` computing through
//!   the kernel-gated emission).
//! * **B** — authored directly inside merge commit `167a7e2acf6`; *neither*
//!   parent of that merge contains the file, so it is a genuine second
//!   implementation rather than an edit of A. It shipped **without** a
//!   control: `control_7` is not on that lineage.
//!
//! A later merge kept A and dropped B outright. Merge order is not a design
//! decision, so this file is the deliberate reconciliation. What each
//! contributed, and how each disputed point was decided:
//!
//! | decision | A | B | taken | why |
//! |---|---|---|---|---|
//! | full kernel check of the minted terms | yes — `add_decl` of all three into a CLONE of `env` | none | **A** | `emit.rs`'s own step 3 (`admit_structural_rec_lowering`, landed in `a613e62eb0e`, an ancestor of *both*) already specifies "each term full-kernel-checked in a scratch clone". B does not meet the contract its caller documents, and the gate then runs `TypeChecker::is_def_eq` over terms nothing has typed. |
//! | prelude preflight with a shaped message | none (a missing constant surfaces as an opaque kernel refusal) | fixed list of four `get_const` probes | **B's idea, A's honesty** | v7/D3: a refusal must say what is wrong. B's fixed list over-rejects — it demands `Nat.add` of a body with no `Add` node. The reconciled preflight is demand-driven: it probes exactly the constants the rendering actually named, so it never refuses an environment the term does not need. |
//! | refusals name the declaration and the position | generic prose | `name` + position in every message | **B** | Same ruling. The wrapper (`EmitRefusal::ReflectionRejected`) already carries `name`, but the *position* is information only this module has. The position string is now derived from the [`Case`], so it cannot be mislabelled by a caller. |
//! | case/binder representation | closed `Case { Zero, SuccValue, SuccRecArg }`, de Bruijn indices fixed per variant | `CaseContext::Succ { k_index, ih_index }`, indices supplied by the caller | **A** | Identical output at all three sites, but the binder shape is soundness-relevant: `check_faithful_equations` compares these terms against side A's own minor premises and against `fun k => bvar 0`. A closed enum makes a wrong index unrepresentable; B's parameter has exactly three legal values and infinitely many illegal ones. |
//! | structural preconditions restated in side B | yes — no `Rec`/`Pred` in the base, exactly one `Rec` in the step, no `Rec` in the argument | none (relies on the render arms refusing) | **A** | The render arms alone catch `Rec`/`Pred` in the zero case and `Rec` in the argument, but **not** a step with zero or two `Rec` nodes: B renders both silently. The recognizer forbids them, and this producer must be sound alone. |
//! | "the defined constant's name is not a parameter" | claimed | not claimed | **B** — A's sentence was FALSE | `name` is a parameter of both. The checkable statement is the one below: no *rendered term* can name it, and that is now enforced by a type rather than by a reading. |
//! | standing side-B FREEZE notice | absent | present | **B** | It is the rule that stops this file being edited into a round trip, and it matches the identical prohibition on `trust-clean/src/reflect.rs` and `recognize_structural_rec`. |
//! | §6f pedigree / per-node measurement table | present | prose per node | **A**, with B's prose folded in | |
//!
//! **The two takes did not disagree on anything soundness-relevant in the
//! rendering itself.** Node for node, case for case, A and B render the same
//! terms — including the §6e question: *neither* cites the defined constant
//! anywhere in a rendered term, both put the self-call's result at the
//! recursor's own `ih` binder, and both render the predecessor as the
//! MIR-faithful `Nat.sub (Nat.succ k) 1` rather than pre-reducing it to `k`.
//! The soundness-shaped gap is A's kernel check, which B lacks entirely, plus
//! A's arity guard on the step; both are producer-alone weaknesses in B rather
//! than live false-verifies, because the recognizer's own belt stands in front
//! of them on the compiler path — but the controls call this function
//! *directly*, so on the fast lane there is nothing in front of it at all.
//!
//! # FROZEN against the lane it feeds
//!
//! This module is a side-B producer, under the same standing prohibition as
//! `crates/trust-clean/src/reflect.rs` and `recognize_structural_rec`: **if a
//! Clean-origin body fails the gate, the fix is NEVER an edit here.** Editing
//! the reflection to make side B agree with side A converts the gate into a
//! round trip. Its output is a CLAIM — every part is re-decided against the
//! kernel by [`crate::gate::check_faithful_equations`], which is the only
//! place a [`crate::gate::Faithful`] can come from.
//!
//! # Why this producer lives here, and what that costs
//!
//! The non-recursive shapes reflect through `trust_spec_elab`'s `admit_*`
//! family — producers written years earlier for the OPPOSITE direction, which
//! is the frozen-R independence argument. No such pre-existing producer can
//! exist for the abstract-ih form: it was derived adversarially in the §6e
//! IMPLEMENTATION AMENDMENT (2026-08-21). This module is therefore a NEW
//! side-B producer, and per §6f's discipline it gets its own `docs/TCB.md`
//! row instead of borrowing frozen-R's pedigree. The ratified substitute for
//! that pedigree is FAST-LANE-FIRST: every rendering below is committed to a
//! kernel measurement that landed BEFORE this module
//! (`tests/r1_equation_probes.rs` — the s-series, s6/s7/s8 included), and the
//! mutation controls (`tests/control_7_structural_rec_emitter_mutation.rs`)
//! demand refusals at both the structural and the kernel layer.
//!
//! # The renderings, each with its measurement
//!
//! The reflection is a DUMB reading of the recognized dataflow — deliberately
//! never pre-simplified, so the KERNEL does the reduction and the reflector
//! stays too simple to smuggle a semantic step. Every node spells what the
//! MACHINE computes, not what side A wrote; every identification between the
//! two spellings is the kernel's decision and never this module's:
//!
//! | node | zero case (`n := 0`) | succ case (`n := succ k`, under `k`,`ih`) | measurement |
//! |---|---|---|---|
//! | `Rec` | refused | `ih` (the bound variable) | s3 — the abstract-ih minors |
//! | `Pred` | refused | `Nat.sub (Nat.succ k) 1` — what the MIR computes (`Nat::sub(&n, &1)`), under the case substitution | s6 — `≡ k` by kernel computation; the off-by-one `succ k ≢ k` is s4 |
//! | `Decreasing` | `0` (literal) | `Nat.succ k` | s4 (the refusing direction), e5 (literal lane) |
//! | `NatConst(c)` | `c` (literal) | `c` (literal) | e5 — literal↔constructor bridging; s7 — `0 ≡ Nat.zero ≡ OfNat.ofNat …` |
//! | `Add` | `Nat.add _ _` | `Nat.add _ _` | e4/e5 — `Nat.add` reduces closed and stays structure-sensitive open; s8 — the surface `HAdd` spelling identifies with it |
//!
//! The `Pred` row is the one worth restating: reflecting it as the case binder
//! `k` directly would decide the recursive-argument identity *here* instead of
//! at the kernel, which is exactly the authority this module must not have.
//!
//! # The defined constant is unnameable in a rendered term
//!
//! §6e's amendment turns on side B never citing the defined constant: probe s2
//! measures that the constant-citing spelling is VACUOUS as a gate — it admits
//! a diverging off-by-one body. Here that is enforced by a **type**, not by a
//! reading: every constant a rendering can name goes through [`cnst`], whose
//! parameter is `&'static str`, and the declaration name arrives as an ordinary
//! `&str`. There is no way to render it. `name` reaches only the scratch
//! declaration prefix (a fresh name, never a reference) and the refusal text.
//! Circularity (probe r1's boundary) and the s2 vacuity are therefore both
//! unconstructible rather than merely absent.
//!
//! Every minted term is FULL-KERNEL-CHECKED: the three definitions
//! (`{p}_eq_zero : Nat`, `{p}_eq_succ : Nat → Nat → Nat`,
//! `{p}_rec_arg : Nat → Nat`) go through `Environment::add_decl` in a CLONE
//! of the caller's environment — the same scratch-clone discipline as
//! `emit::admit_lowering`'s reflection step, so checking a body can never
//! mutate the environment it is checked against.

//!
//! # SINCE §6f LANDING 1: the rendering is the SHARED descent
//!
//! The per-node `render` that used to live here is now
//! [`crate::reflect::render_rec_node`] — ONE recursive descent, driven by
//! [`crate::table`], serving R1's three sites and R2's three. Nothing about the
//! terms changed: `Case { Zero, SuccValue, SuccRecArg }` became
//! `Site { RecZero, RecSuccValue, RecSuccArg }` with the same fixed de Bruijn
//! indices, and the node vocabulary's kernel constants (`Nat.sub`, `Nat.add`)
//! moved from match arms into the rows that name them. This function keeps its
//! signature, its structural preconditions, its demand-driven preflight and its
//! full kernel check, and `docs/TCB.md` still names it as R1's side-B producer.

use std::collections::BTreeSet;

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_types::admissible_body::{RecBodyExpr, StructuralRecBody};

use crate::gate::{ReflectedCase, ReflectedStructuralRec};
use crate::reflect::{RecCall, RecFamily, Site, render_rec_node};

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// R1's half of the shared descent: render one recognized node at one of R1's
/// three sites. The self-call CONTEXT is unread on this lane — R1 renders the
/// self-call argument at its OWN site, which is what lets the gate compare it
/// against `fun k => bvar 0` (probe s4) — so it is passed as the unary context
/// R1's single-parameter contract fixes: arity 1, measure 0, one argument.
/// `RecCall::unary` is the only shape R1 can construct, which is what keeps
/// R3a's arity widening off this lane by construction rather than by review.
fn render(
    name: &str,
    node: &RecBodyExpr,
    case: Site,
    named: &mut BTreeSet<&'static str>,
) -> Result<Expr, String> {
    render_rec_node(
        RecFamily::Structural,
        name,
        node,
        case,
        RecCall::unary(&RecBodyExpr::Pred),
        named,
    )
}

/// Mint side B for a structural-recursion emission: the two abstract-ih case
/// terms and the recursive-argument function, each rendered from the
/// RECOGNIZED dataflow (never from the plan) and each FULL-KERNEL-CHECKED in
/// a clone of `env`.
///
/// `body` is
/// [`trust_types::admissible_body::recognize_structural_rec`]'s reading of the
/// EMITTED body — never the plan's shape — for the module-doc reason: side B
/// must be a reading of what was emitted.
///
/// # Errors
///
/// A `String` detail, which `emit::admit_lowering` wraps in
/// [`crate::emit::EmitRefusal::ReflectionRejected`]:
///
/// * the recognized tree violates a structural precondition of the fragment
///   (re-stated here rather than inherited — this producer must be sound
///   alone);
/// * a node has no reading at its site (the fail-closed vocabulary);
/// * a kernel constant the rendering names is absent from `env`;
/// * the kernel refused one of the minted definitions.
///
/// All four are producer-chain defects, not user-actionable refusals, and
/// there is no degraded rendering.
pub fn reflect_structural_rec(
    env: &Environment,
    name: &str,
    body: &StructuralRecBody,
) -> Result<ReflectedStructuralRec, String> {
    // ── 1. Structural preconditions ────────────────────────────────────────
    //
    // Re-stated here fail-closed even though `recognize_structural_rec` already
    // enforces them, because the controls call this function DIRECTLY: on the
    // fast lane the recognizer is not in front of it. The arity guard on the
    // step is the one the render arms cannot supply — a step with zero or two
    // recursive results renders perfectly well and means something else.
    if body.base.contains(&RecBodyExpr::Rec) || body.base.contains(&RecBodyExpr::Pred) {
        return Err(format!(
            "cannot reflect the structural recursion emitted for `{name}`: its zero-case \
             value contains the self-call result or the predecessor, neither of which has a \
             reading under `n := 0`. This is a producer-chain defect; please report it."
        ));
    }
    if body.step.count(&RecBodyExpr::Rec) != 1 {
        return Err(format!(
            "cannot reflect the structural recursion emitted for `{name}`: its succ-case \
             value contains {} self-call result(s) where the single-step fragment admits \
             exactly one. A body with none is not a recursion (route it through the \
             non-recursive lane, `check_faithful`); a body with several is outside this \
             fragment and must not be reflected as though it were inside it. This is a \
             producer-chain defect; please report it.",
            body.step.count(&RecBodyExpr::Rec)
        ));
    }
    if body.rec_arg.contains(&RecBodyExpr::Rec) {
        return Err(format!(
            "cannot reflect the structural recursion emitted for `{name}`: its self-call \
             argument contains the self-call result. An argument computed from the call's \
             own result is not a structural recursion and side A's kernel termination \
             evidence would not transfer to it. This is a producer-chain defect; please \
             report it."
        ));
    }

    // ── 2. Render, recording every constant the terms name ─────────────────
    //
    // `Nat` is seeded because the binder types below always name it.
    let mut named = BTreeSet::from(["Nat"]);
    let eq_zero = render(name, &body.base, Site::RecZero, &mut named)?;
    let eq_succ = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            render(name, &body.step, Site::RecSuccValue, &mut named)?,
        ),
    );
    let rec_arg = Expr::lam(
        BinderInfo::Default,
        nat(),
        render(name, &body.rec_arg, Site::RecSuccArg, &mut named)?,
    );

    // ── 3. Environment preflight ───────────────────────────────────────────
    //
    // The kernel check below already refuses a term naming an absent constant,
    // but as an opaque type-checking failure about a term nobody wrote. This
    // says WHAT is missing (v7/D3). It is DEMAND-DRIVEN — exactly the
    // constants step 2 actually named — so it never refuses an environment
    // that lacks something this body does not use (`Nat.add`, for a body with
    // no `Add` node).
    for &constant in &named {
        if env.get_const(&Name::from_string(constant)).is_none() {
            return Err(format!(
                "cannot reflect the structural recursion emitted for `{name}`: the kernel \
                 environment has no `{constant}`, which the rendering names. This is a \
                 producer-chain defect, not a user error: side B is being minted against an \
                 environment that does not carry the `Nat` prelude the fragment is stated \
                 over. Please report it."
            ));
        }
    }

    // ── 4. FULL kernel check of each minted term, in a CLONE ───────────────
    //
    // `emit.rs`'s step 3 states this contract; it is also what makes the gate's
    // `is_def_eq` a judgment about typed terms. The names use the same
    // non-namespace `_` suffix discipline as `emit::reflection_name`, and never
    // enter the real environment.
    let mut scratch = env.clone();
    let prefix = format!("{name}_trust_clean_origin_reflection");
    for (suffix, type_, value) in [
        ("eq_zero", nat(), eq_zero.clone()),
        ("eq_succ", Expr::arrow(nat(), Expr::arrow(nat(), nat())), eq_succ.clone()),
        ("rec_arg", Expr::arrow(nat(), nat()), rec_arg.clone()),
    ] {
        scratch
            .add_decl(Declaration::Definition {
                name: Name::from_string(&format!("{prefix}_{suffix}")),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })
            .map_err(|refusal| {
                format!(
                    "cannot reflect the structural recursion emitted for `{name}`: the kernel \
                     refused the reflected `{suffix}` term: {refusal:?}. This is a \
                     producer-chain defect, not a user error, and there is no degraded \
                     rendering — an unchecked term must never reach the per-equation gate, \
                     where it would be put to `is_def_eq` untyped. Please report it."
                )
            })?;
    }

    Ok(ReflectedStructuralRec {
        cases: vec![
            ReflectedCase { constructor: "Nat.zero".to_owned(), value: eq_zero },
            ReflectedCase { constructor: "Nat.succ".to_owned(), value: eq_succ },
        ],
        rec_arg,
    })
}

#[cfg(test)]
mod tests {
    //! The reconciliation's own coverage. `control_7` exercises this producer
    //! through the whole route; these pin the checks that route cannot reach —
    //! the structural preconditions of step 1, which exist precisely because
    //! the fast lane calls this function with the recognizer removed. The
    //! step-arity guard is the one implementation B lacked entirely: it renders
    //! a zero-`Rec` and a two-`Rec` step without complaint.

    use clean_kernel::Environment;

    use super::{RecBodyExpr, StructuralRecBody, reflect_structural_rec};

    fn trio(base: RecBodyExpr, step: RecBodyExpr, rec_arg: RecBodyExpr) -> StructuralRecBody {
        StructuralRecBody { base, step, rec_arg }
    }

    fn add(left: RecBodyExpr, right: RecBodyExpr) -> RecBodyExpr {
        RecBodyExpr::Add(Box::new(left), Box::new(right))
    }

    #[test]
    fn the_tozero_trio_reflects_and_kernel_checks() {
        let env = Environment::with_prelude();
        let reflected = reflect_structural_rec(
            &env,
            "tozero",
            &trio(RecBodyExpr::NatConst(0), RecBodyExpr::Rec, RecBodyExpr::Pred),
        )
        .expect("the correct trio reflects and each term kernel-checks");
        assert_eq!(reflected.cases.len(), 2);
        assert_eq!(reflected.cases[0].constructor, "Nat.zero");
        assert_eq!(reflected.cases[1].constructor, "Nat.succ");
    }

    /// An `Add`-carrying trio names `Nat.add`; the demand-driven preflight must
    /// pass it and the kernel must accept the term.
    fn assert_reflects(body: &StructuralRecBody) {
        reflect_structural_rec(&Environment::with_prelude(), "f", body)
            .expect("an in-fragment trio must reflect");
    }

    #[test]
    fn an_add_step_reflects_through_nat_add() {
        assert_reflects(&trio(
            RecBodyExpr::NatConst(0),
            add(RecBodyExpr::Rec, RecBodyExpr::NatConst(2)),
            RecBodyExpr::Pred,
        ));
    }

    /// THE gap between the two implementations: the render arms are total over
    /// a step with no recursive result and over one with two, so only an
    /// explicit arity guard refuses them.
    #[test]
    fn a_step_without_exactly_one_recursive_result_is_refused() {
        let env = Environment::with_prelude();
        for step in [
            RecBodyExpr::NatConst(1),
            add(RecBodyExpr::Decreasing, RecBodyExpr::NatConst(1)),
            add(RecBodyExpr::Rec, RecBodyExpr::Rec),
        ] {
            let detail = reflect_structural_rec(
                &env,
                "f",
                &trio(RecBodyExpr::NatConst(0), step, RecBodyExpr::Pred),
            )
            .expect_err("a step outside the single-step fragment must not reflect");
            assert!(
                detail.contains("succ-case value") && detail.contains("exactly one"),
                "the refusal must name the position and the contract: {detail}"
            );
            assert!(detail.contains('`'), "the refusal must name the declaration: {detail}");
        }
    }

    #[test]
    fn the_zero_case_may_not_read_the_recursion_or_the_predecessor() {
        let env = Environment::with_prelude();
        let bases =
            [RecBodyExpr::Rec, RecBodyExpr::Pred, add(RecBodyExpr::NatConst(1), RecBodyExpr::Pred)];
        for base in bases {
            let detail =
                reflect_structural_rec(&env, "f", &trio(base, RecBodyExpr::Rec, RecBodyExpr::Pred))
                    .expect_err("no zero-case reading exists for either node");
            assert!(detail.contains("zero-case value"), "must name the position: {detail}");
        }
    }

    #[test]
    fn the_self_call_argument_may_not_read_the_recursion() {
        let detail = reflect_structural_rec(
            &Environment::with_prelude(),
            "f",
            &trio(RecBodyExpr::NatConst(0), RecBodyExpr::Rec, RecBodyExpr::Rec),
        )
        .expect_err("an argument computed from the call's own result is not structural");
        assert!(detail.contains("self-call argument"), "must name the position: {detail}");
    }
}
