// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **R2 AXIOM-CLOSURE PROBES — the escape reproduced, then caught.**
//!
//! `r2_wf_equation_probes.rs` w7/d4 measured the escape and recorded it as
//! R2's blocking obligation; the design note
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md`, §6e
//! MEASUREMENT NOTE, finding 2) states it as the reason R2 is not landable:
//!
//! > That typing guarantee is exactly as strong as the AXIOM CLOSURE of the
//! > proof terms side B puts in the decrease slot. … The audited-empty
//! > axiom-closure machinery exists (`mint.rs`,
//! > `AxiomClosure::is_audited_empty`) but today covers side A's declaration
//! > only. **R2 must extend it to side B's proof terms; without that
//! > extension R2 is not landable.**
//!
//! This file measures the closing move, and it keeps the adverse half: the
//! escape is REPRODUCED here at the kernel (c1), so that if the precondition
//! were ever weakened, c1 would still pass and c2 would fail loudly rather
//! than both quietly agreeing about a hazard that had disappeared.
//!
//! # The measured table
//!
//! | # | question | verdict |
//! |---|---|---|
//! | c0 | can the crate's closure machinery see a free-standing TERM at all? | **before: NO.** `Environment::axiom_deps` is name-keyed; `KernelStatus::closure()` is name-keyed; `audit_certification` is expression-rooted but refuses a non-`Prop` goal, and a functional's type is `Type`. Measured directly: the raw `audit_certification(F_TYPE, F)` call reports `GoalNotProposition`. **After:** [`trust_clean_origin::audit_term_closure`] audits the same term via the `Eq`-judgment spelling, 0 issues on the honest F |
//! | c1 | **THE ESCAPE, REPRODUCED.** With `axiom bogus : ∀ x, Nat.lt (succ x) x`, does a DIVERGING functional kernel-check and its definition ADMIT? | **YES — the kernel alone is not the guard.** `add_decl` accepts `cds_axiom_diverging`, whose recursion is `rec (succ x) (bogus x)`; the same functional with the honest proof is refused by TYPING |
//! | c2 | **THE AUDIT CATCHES IT.** Same setup, put to the gate. | **REFUSED**, `AssumptionBearingRecursion`, naming `bogus` — and the refusal carries the fix with options (v7/D3). Caught on BOTH sides independently: the side-A precondition and the side-B post-borrow audit each name it |
//! | c3 | **THE HONEST CASE.** A genuine `Nat.sub_lt`-backed decrease, empty closure. | **ADMITS.** `FaithfulnessMethod::WellFoundedFunctionalDefeq`, closure audited empty (0 issues, 52 reachable constants). The precondition is not a blanket refusal |
//! | c4 | **AXIOM-BEARING BUT NOT DECREASE-RELATED** — an axiom in the def's VALUE, in the else-branch, nowhere near a proof slot. | **REFUSES, deliberately.** Pinned with its reasoning below |
//! | c5 | the borrow refuses a side B that AUTHORS a proof | **REFUSED** — an emitter-written slot is exactly the term whose closure the gate would otherwise be trusting |
//! | c6 | the borrow does not weaken the DIVERGENCE catch | a side B recursing at `succ x` gets side A's `Nat.lt (x-1) x` proof, which does not type → **REFUSED**; and a well-typed but WRONG decreasing argument (`x-2`) is refused by DEFEQ |
//! | c7 | the R1 (structural) lane inherits the same precondition | a `Nat.rec` def whose value cites an axiom is **REFUSED** by `check_faithful_equations`, and the honest `tozero` still ADMITS |
//! | c8 | the WHOLE-TERM lane inherits it too | probe w8 measured `check_faithful` ADMITTING a WF side A; an axiom-bearing WF side A is now **REFUSED** there, and the honest one still admits |
//! | c9 | a non-recursive body is untouched | an axiom-bearing NON-recursive Clean-origin body still admits at `check_faithful` — the precondition is scoped to recursion, where the closure is part of the TERMINATION argument, and is not smuggled in as a general tightening |
//!
//! # (c4) THE RULING, and why it is a refusal
//!
//! An axiom in the definition's value that has nothing to do with the
//! decrease **also refuses**, and this is not incidental scope creep:
//!
//! 1. **The audited-empty rule already governs DECLARATIONS.** `mint.rs`'s
//!    second precondition refuses a `DefId` for any declaration whose closure
//!    is non-empty or unrecorded, whatever the assumption is about. A gate
//!    that admitted what the mint refuses would put the two decisions into
//!    disagreement about one declaration, and the disagreement would be
//!    invisible — the mint refusal produces `E0425` at a call site, the gate
//!    admission produces a `Body`.
//! 2. **"Decrease-related" is not a decidable partition.** The kernel reports
//!    a closure, not a provenance map: an axiom reached through `Nat.sub_lt`'s
//!    own closure and one reached through the else-branch arrive as the same
//!    fact. A gate that tried to admit the second class would need a
//!    reachability argument the audit does not produce, and getting it wrong
//!    is a wrong binary.
//! 3. **The value is what is EMITTED.** An assumption in the else-branch is
//!    an assumption behind an emitted value with nothing disclosing it at the
//!    call site — `mint.rs`'s `AxiomClosureNonEmpty` note says exactly this.
//!
//! The honest cost is stated rather than hidden: a user with a deliberate
//! domain axiom in a recursive definition cannot CALL it. The refusal's
//! options say so and name three routes (discharge it; cite it from proof
//! position where the closure is disclosed by name; restate the assumption as
//! a Rust contract so callers see the obligation).
//!
//! # HONESTY RULES (identical to the R1/R2 batteries)
//!
//! * Every ADMIT is paired with a refused mutation at the same layer.
//! * The adverse pin (c1) asserts the ADMISSION, because that admission is
//!   the hazard. It is not good news and must not be read as one.
//! * The kernel terms are raw-kernel mirrors of the island's measured
//!   `countdownSum` lowering, built by hand — the same convention, and for
//!   the same reason, as `r2_wf_equation_probes.rs`.

use clean_kernel::{
    BinderInfo, Declaration, DeclarationVerification, Environment, Expr, Level, Name, TypeChecker,
};
use trust_clean_origin::{
    DECREASE_SLOT_SENTINEL, FaithfulnessMethod, GateRefusal, ReflectedCase, ReflectedStructuralRec,
    ReflectedWfFunctional, audit_term_closure, check_faithful, check_faithful_equations,
    check_faithful_wf_functional,
};

// ───────────────────────────── helpers (R2's conventions) ────────────────────

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

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

fn sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.sub"), [a, b])
}

fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.lt"), [a, b])
}

fn sentinel() -> Expr {
    cnst(DECREASE_SLOT_SENTINEL)
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

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    try_define(env, name, type_, value)
        .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e}"));
}

/// `(y : Nat) → Nat.lt y X → Nat` — the recursive slot's type.
fn rec_ty(x_under_y: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), Expr::arrow(nat_lt(Expr::bvar(0), x_under_y), nat()))
}

/// `fun (n : Nat) => @WellFounded.fix.{1,1} Nat (fun _ => Nat) Nat.lt Nat.lt_wf F n`.
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

/// `@Nat.le.refl 1 : Nat.lt 0 1`.
fn one_pos() -> Expr {
    Expr::app(cnst("Nat.le.refl"), nat_num(1))
}

/// `Nat.le.step (Nat.le.refl 1) : Nat.lt 0 2`.
fn two_pos() -> Expr {
    Expr::apps(cnst("Nat.le.step"), [nat_num(1), nat_num(1), one_pos()])
}

/// The `countdownSum` functional. `then_call` lives in the scope
/// `[x = bvar 2, rec = bvar 1, h = bvar 0]`, `else_value` in `[x, rec, _]`.
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

/// `x + rec (x - 1) (Nat.sub_lt x 1 h 0<1)` — the honest, kernel-backed step.
fn cds_then_honest() -> Expr {
    add(
        Expr::bvar(2),
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
    )
}

/// Side B's spelling of the same step: the ARGUMENT is side B's, the proof
/// slot is the sentinel.
fn cds_then_side_b(argument: Expr) -> Expr {
    add(Expr::bvar(2), Expr::apps(Expr::bvar(1), [argument, sentinel()]))
}

/// The canonical side A.
fn install_cds(env: &mut Environment, name: &str) {
    define(
        env,
        name,
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(cds_then_honest(), cnst("Nat.zero"))),
    );
}

/// `axiom <name> : (x : Nat) → Nat.lt (Nat.succ x) x` — the bogus decrease.
fn install_bogus_decrease(env: &mut Environment, name: &str) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat(), nat_lt(succ(Expr::bvar(0)), Expr::bvar(0))),
    })
    .expect("an axiom may be declared");
}

/// The `Nat -> Nat` bignum carrier every probe here admits at.
fn nat_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_for(&nat()).expect("I6: Nat carries at trust_bignum::Nat")
}

fn refusal_names(refusal: &GateRefusal) -> (Vec<String>, Vec<String>) {
    match refusal {
        GateRefusal::AssumptionBearingRecursion { assumptions, blocking, .. } => {
            (assumptions.clone(), blocking.clone())
        }
        other => panic!("expected an assumption-bearing refusal, got {other:?}"),
    }
}

// ═══════ (c0) can the closure machinery see a free-standing TERM at all? ═════

/// **The finding the design note anticipated, measured rather than assumed.**
///
/// Before this change the crate had two closure producers and both were
/// NAME-KEYED (`Environment::axiom_deps(&Name)`, and `KernelStatus::closure()`
/// which `mint::decide_mint` reads). A term that is not a declaration was
/// invisible to both, and side B's functional never becomes a declaration.
///
/// The kernel's one expression-rooted walker, `audit_certification`, refuses
/// the job directly: it requires a `Prop` goal, and a functional's type lives
/// in `Type`. **That refusal is asserted here**, because it is the exact
/// mechanical reason the extension was needed and not merely overlooked.
///
/// The extension is a SPELLING, not a second walker: `@Eq.{u} T t t` is a
/// `Prop` for every sort `u`, so the same kernel walk covers the same const
/// closure. Measured: 0 issues on the honest functional.
#[test]
fn probe_c0_the_closure_walker_was_name_keyed_and_prop_only() {
    let env = Environment::with_prelude();
    let f = cds_f(cds_then_honest(), cnst("Nat.zero"));
    let f_ty = TypeChecker::new(&env).infer_type(&f).expect("the functional types");

    // (a) THE BLOCKER: the kernel's expression-rooted walker, called directly
    //     on the functional, refuses the goal.
    let raw = env.audit_certification(&f_ty, &f);
    assert!(
        raw.issues.iter().any(|issue| matches!(
            issue,
            clean_kernel::CertificationIssue::GoalNotProposition { .. }
        )),
        "MEASURED: `audit_certification` cannot be pointed at a functional directly — its goal \
         must be a Prop and a functional's type is not one. This is the mechanical reason the \
         machinery could not see side B: {:?}",
        raw.issues
    );

    // (b) …and the name-keyed walker cannot be pointed at a term at all —
    //     there is no name to pass, which is not an API inconvenience but the
    //     whole gap: side B's functional never becomes a declaration.
    assert!(
        env.axiom_deps(&Name::from_string("Trust.CleanOrigin.decreaseSlot")).is_none(),
        "the name-keyed walker answers only about declarations; a term with no name has no answer"
    );

    // (c) THE EXTENSION: the same kernel walk, reached through the `Eq`
    //     judgment, audits the same term cleanly.
    let audit = audit_term_closure(&env, "the honest countdownSum functional", &f_ty, &f);
    assert!(
        audit.is_clear(),
        "the honest functional must audit clean: assumptions={:?} blocking={:?}",
        audit.assumptions(),
        audit.blocking()
    );
    assert!(
        audit.closure().is_audited_empty(),
        "and the recorded closure must be AUDITED-empty, not merely empty-looking"
    );
    eprintln!(
        "PROBE-ROW | c0 term-visibility           | audit_certification(F_TYPE, F): \
         GoalNotProposition | axiom_deps(term): no such call | audit_term_closure: CLEAR"
    );
}

// ═══════ (c1) THE ESCAPE, REPRODUCED AT THE KERNEL ═══════

/// **THE ADVERSE PIN. This probe asserts an ADMISSION, and the admission is
/// the hazard.**
///
/// Reproduced from `r2_wf_equation_probes.rs` w7/d4, deliberately duplicated
/// here so this file is self-contained as the record of "the escape existed":
///
/// * the honest functional recursing at `Nat.succ x` is refused by TYPING —
///   `Nat.sub_lt x 1 h 0<1 : Nat.lt (x-1) x` does not prove `Nat.lt (succ x) x`;
/// * with `axiom bogus : (x : Nat) → Nat.lt (Nat.succ x) x` in scope, the SAME
///   diverging functional kernel-checks and the definition **ADMITS**.
///
/// No closed application is evaluated: it would not terminate. The admission
/// is the whole measurement. If this probe ever starts failing, the kernel or
/// the prelude changed and c2's precondition must be re-derived rather than
/// assumed still necessary.
#[test]
fn probe_c1_the_escape_reproduced_the_kernel_alone_is_not_the_guard() {
    let mut env = Environment::with_prelude();

    // Without the axiom: the diverging functional cannot be typed.
    let f_diverging_honest_proof = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [
                    succ(Expr::bvar(2)),
                    Expr::apps(
                        cnst("Nat.sub_lt"),
                        [Expr::bvar(2), nat_num(1), Expr::bvar(0), one_pos()],
                    ),
                ],
            ),
        ),
        cnst("Nat.zero"),
    );
    let typing_refusal = try_define(
        &mut env,
        "cds_diverging",
        Expr::arrow(nat(), nat()),
        wf_body(f_diverging_honest_proof),
    )
    .expect_err(
        "the decrease slot's TYPE refuses a non-decreasing self-call when only real proofs are \
         available",
    );
    assert!(
        typing_refusal.contains("TypeMismatch") || typing_refusal.contains("TypeCheckFailed"),
        "the refusal must be the typing verdict at the proof slot, got: {typing_refusal}"
    );

    // With the axiom: the same divergence ADMITS.
    install_bogus_decrease(&mut env, "c1_bogus_lt");
    let f_axiom_diverging = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [succ(Expr::bvar(2)), Expr::app(cnst("c1_bogus_lt"), Expr::bvar(2))],
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
        "THE ESCAPE: with a bogus decrease AXIOM in scope, the DIVERGING functional kernel-checks \
         and the definition ADMITS. The kernel's typing rule is R2's termination evidence and one \
         assumed proof switches it off. This ADMIT is the adverse finding, not good news",
    );
    assert_eq!(
        env.declaration_verification(&Name::from_string("cds_axiom_diverging")),
        Some(DeclarationVerification::FullKernelCheck),
        "and it is a FULL kernel check — every provenance gate in the crate would pass it"
    );
    eprintln!(
        "PROBE-ROW | c1 THE ESCAPE (adverse)      | honest proof + diverging arg: REFUSED BY \
         TYPING | bogus axiom + diverging arg: ADMITS at FullKernelCheck -> the kernel alone is \
         NOT the guard"
    );
}

// ═══════ (c2) THE AUDIT CATCHES IT ═══════

/// **The closing move, measured on the exact term c1 admits.**
///
/// The same environment, the same axiom, the same diverging recursion — put
/// to the gate instead of to `add_decl`. Two independent catches, and the
/// probe asserts both, because either alone would leave a route open:
///
/// * **side A's precondition** — the declaration's own closure names `bogus`,
///   so `check_faithful_wf_functional` refuses before it ever looks at side B;
/// * **side B's post-borrow audit** — measured separately by handing the same
///   axiom-bearing proof to [`audit_term_closure`] as the term in a slot. This
///   is the half the design note says did not exist, and it is what makes the
///   borrow load-bearing rather than decorative: without it, a side B that
///   authored `bogus x` would carry an unaudited assumption into an emitted
///   binary.
///
/// The refusal names the axiom, and carries the fix with options (v7/D3).
#[test]
fn probe_c2_the_audit_catches_the_escape_and_names_the_axiom() {
    let mut env = Environment::with_prelude();
    install_bogus_decrease(&mut env, "c2_bogus_lt");
    let f_axiom_diverging = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [succ(Expr::bvar(2)), Expr::app(cnst("c2_bogus_lt"), Expr::bvar(2))],
            ),
        ),
        cnst("Nat.zero"),
    );
    define(&mut env, "cds_axiom_diverging", Expr::arrow(nat(), nat()), wf_body(f_axiom_diverging));

    // Side B mirrors the emission faithfully — it is not the mistranslation
    // that is being caught here, it is the ASSUMPTION.
    let side_b = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(succ(Expr::bvar(2))), cnst("Nat.zero")),
    };
    let refusal = check_faithful_wf_functional(
        &env,
        "cds_axiom_diverging",
        &side_b,
        &nat_carrier(),
    )
    .expect_err(
        "THE CLOSING MOVE: a recursive Clean-origin body whose termination rests on an assumed \
         decrease must not be emitted, however faithfully the lowering mirrors it",
    );
    let (assumptions, blocking) = refusal_names(&refusal);
    assert!(
        assumptions.iter().any(|name| name == "c2_bogus_lt"),
        "the refusal must NAME the axiom — a non-empty closure is disclosed by name: \
         {assumptions:?} / {blocking:?}"
    );

    // v7/D3: the refusal states the rule, the reason, and at least two routes.
    let note = refusal.note();
    assert!(note.contains("c2_bogus_lt"), "the note must name the assumption:\n{note}");
    assert!(note.contains("options:"), "the note must carry options:\n{note}");
    assert!(
        note.matches("\n                     - ").count() >= 2
            || note.lines().filter(|line| line.trim_start().starts_with('-')).count() >= 2,
        "a refusal with exactly one escape is an ultimatum, not a diagnostic:\n{note}"
    );
    assert!(
        note.contains("terminat"),
        "the note must say WHY a recursive lane treats the closure as termination evidence rather \
         than disclosure metadata:\n{note}"
    );

    // …and the SIDE-B half, measured on its own: an emitter-authored slot
    // term carrying the axiom is caught by the term audit, which is precisely
    // the capability the design note says was missing.
    let f_ty = TypeChecker::new(&env)
        .infer_type(&cds_f(cds_then_honest(), cnst("Nat.zero")))
        .expect("the honest functional types");
    let emitter_authored = cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [succ(Expr::bvar(2)), Expr::app(cnst("c2_bogus_lt"), Expr::bvar(2))],
            ),
        ),
        cnst("Nat.zero"),
    );
    let side_b_audit =
        audit_term_closure(&env, "an emitter-authored decrease slot", &f_ty, &emitter_authored);
    assert!(
        !side_b_audit.is_clear(),
        "an emitter-authored axiom-bearing slot must not audit clear"
    );
    assert!(
        side_b_audit.assumptions().iter().any(|name| name == "c2_bogus_lt"),
        "and the term audit must name it: {:?}",
        side_b_audit.assumptions()
    );
    assert!(
        !side_b_audit.closure().is_audited_empty(),
        "the recorded closure must refuse `is_audited_empty`, which is what every consumer reads"
    );
    eprintln!(
        "PROBE-ROW | c2 THE AUDIT CATCHES IT      | gate: REFUSED (AssumptionBearingRecursion) \
         naming `c2_bogus_lt` | side-B term audit alone: also names it | note carries options + \
         the termination reasoning"
    );
}

// ═══════ (c3) THE HONEST CASE ═══════

/// A genuine `Nat.sub_lt`-backed decrease with an empty closure **ADMITS**,
/// through the borrow, at `FaithfulnessMethod::WellFoundedFunctionalDefeq`.
///
/// The anti-vacuity pairing is inside this probe: side B's ARGUMENT is its
/// own (`Nat.sub x 1`), only the proof is borrowed, and the defeq comparison
/// is what accepts it. The `Nat.pred x` spelling — a different term of a
/// defeq-equal shape, probe w6's (b′) — admits too, so the lane accepts
/// spellings rather than matching syntax.
#[test]
fn probe_c3_the_honest_case_admits_with_an_empty_closure() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");

    let side_b = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(sub(Expr::bvar(2), nat_num(1))), cnst("Nat.zero")),
    };
    let faithful = check_faithful_wf_functional(&env, "cds", &side_b, &nat_carrier())
        .expect("an honest, kernel-backed well-founded recursion must ADMIT");
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);
    assert_eq!(faithful.name(), "cds");

    // (b′) a defeq-equal spelling of the recursive argument also admits: the
    // comparison is definitional equality, not syntax.
    let side_b_pred = ReflectedWfFunctional {
        functional: cds_f(
            cds_then_side_b(Expr::app(cnst("Nat.pred"), Expr::bvar(2))),
            cnst("Nat.zero"),
        ),
    };
    check_faithful_wf_functional(&env, "cds", &side_b_pred, &nat_carrier())
        .expect("the `Nat.pred x` spelling of `Nat.sub x 1` must admit too");

    // the closure the admission rests on, recorded rather than asserted
    // abstractly.
    let f_ty = TypeChecker::new(&env)
        .infer_type(&cds_f(cds_then_honest(), cnst("Nat.zero")))
        .expect("types");
    let audit = audit_term_closure(&env, "cds", &f_ty, &cds_f(cds_then_honest(), cnst("Nat.zero")));
    assert!(audit.is_clear() && audit.assumptions().is_empty());
    eprintln!(
        "PROBE-ROW | c3 THE HONEST CASE           | ADMITS as WellFoundedFunctionalDefeq | \
         `Nat.pred` spelling: ADMITS | closure audited empty"
    );
}

// ═══════ (c4) AXIOM-BEARING BUT NOT DECREASE-RELATED ═══════

/// **PINNED: it refuses too.** The reasoning is in this file's header; the
/// measurement is here.
///
/// The axiom is a plain `Nat` (`axiom c4_debt : Nat`) sitting in the
/// definition's ELSE branch — the terminating base case, as far from a proof
/// slot as the body allows. The decrease proof is the honest `Nat.sub_lt`
/// one; termination is not in question at all.
///
/// It refuses, and the probe additionally pins that the refusal is the SAME
/// one — `AssumptionBearingRecursion` naming `c4_debt` — rather than a
/// separate, softer verdict. Two decisions about one declaration must not
/// disagree: `mint::decide_mint` refuses a `DefId` for exactly this
/// declaration, so a gate that admitted it would emit a `Body` for a name the
/// mint refuses to create.
#[test]
fn probe_c4_an_unrelated_axiom_in_the_value_refuses_too() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c4_debt"),
        level_params: vec![],
        type_: nat(),
    })
    .expect("an axiom may be declared");
    // Honest decrease, axiom in the ELSE branch.
    define(
        &mut env,
        "cds_debt",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(cds_then_honest(), cnst("c4_debt"))),
    );

    let side_b = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(sub(Expr::bvar(2), nat_num(1))), cnst("c4_debt")),
    };
    let refusal = check_faithful_wf_functional(&env, "cds_debt", &side_b, &nat_carrier())
        .expect_err(
            "PINNED RULING: an axiom anywhere in a recursive definition's value refuses. The \
             audited-empty rule already governs DECLARATIONS at the mint, 'decrease-related' is \
             not a partition the kernel's closure report can express, and the value is what gets \
             EMITTED",
        );
    let (assumptions, _) = refusal_names(&refusal);
    assert!(
        assumptions.iter().any(|name| name == "c4_debt"),
        "and it is the same refusal, naming the same kind of thing: {assumptions:?}"
    );

    // Anti-vacuity: the identical definition WITHOUT the axiom admits, so the
    // refusal is about the assumption and not about the shape.
    let mut clean_env = Environment::with_prelude();
    install_cds(&mut clean_env, "cds_debt");
    let clean_side_b = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(sub(Expr::bvar(2), nat_num(1))), cnst("Nat.zero")),
    };
    check_faithful_wf_functional(&clean_env, "cds_debt", &clean_side_b, &nat_carrier())
        .expect("the same shape with no axiom admits — the refusal is about the assumption");
    eprintln!(
        "PROBE-ROW | c4 UNRELATED AXIOM           | axiom in the else-branch: REFUSED (same \
         AssumptionBearingRecursion) | identical shape without it: ADMITS"
    );
}

// ═══════ (c5) the borrow refuses an emitter-authored proof ═══════

/// Side B may not author a decrease proof, and the gate says so by name.
///
/// This is the structural half of the fix: even a *correct* emitter-written
/// proof is refused, because "correct" is exactly what the gate would have to
/// take on trust — the term's axiom closure is the termination evidence, and
/// an emitter that can write the term can write one resting on an axiom (c1).
/// Refusing the whole class removes the question.
#[test]
fn probe_c5_side_b_may_not_author_a_decrease_proof() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");

    // A perfectly good proof, authored by side B rather than borrowed.
    let authored = ReflectedWfFunctional {
        functional: cds_f(
            add(
                Expr::bvar(2),
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
        ),
    };
    let refusal = check_faithful_wf_functional(&env, "cds", &authored, &nat_carrier())
        .expect_err("side B may not put its own term in a decrease slot, correct or not");
    assert!(matches!(refusal, GateRefusal::DecreaseSlotBorrowRefused { .. }), "got {refusal:?}");
    let note = refusal.note();
    assert!(
        note.contains("MIR contains none"),
        "the note must say why an emitter cannot author one:\n{note}"
    );
    assert!(
        note.contains("definitionally equal"),
        "…and why borrowing costs no checking power (probe w7/d2):\n{note}"
    );

    // A stray sentinel outside a call site is refused as well: it would be an
    // unfillable hole, and an unfilled hole must never reach the kernel.
    let stray = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(sub(Expr::bvar(2), nat_num(1))), sentinel()),
    };
    let stray_refusal = check_faithful_wf_functional(&env, "cds", &stray, &nat_carrier())
        .expect_err("a sentinel outside a recursive call site has no proof to borrow");
    assert!(
        matches!(stray_refusal, GateRefusal::DecreaseSlotBorrowRefused { .. }),
        "got {stray_refusal:?}"
    );
    eprintln!(
        "PROBE-ROW | c5 NO EMITTER-AUTHORED PROOF | a CORRECT authored proof: REFUSED | a stray \
         sentinel: REFUSED"
    );
}

// ═══════ (c6) the borrow does not weaken the divergence catch ═══════

/// The two catches probe w7 measured survive the borrow, and they are
/// DIFFERENT refusals — which is the evidence that neither is standing in for
/// the other:
///
/// * **d1, typing** — a side B recursing at `Nat.succ x` is handed side A's
///   proof of `Nat.lt (x-1) x`, which does not fit. `DecreaseSlotBorrowRefused`.
///   Note what has changed and what has not: the divergence is still caught by
///   the kernel's typing rule, but the proof it is checked against is now
///   always a term from a declaration whose closure was audited, so c1's
///   escape cannot be re-opened by side B.
/// * **d3, defeq** — a side B recursing at `x - 2` is well-typed with side A's
///   proof? No: side A's proof is `Nat.lt (x-1) x`, so this too fails typing.
///   The genuinely-different-but-terminating case is therefore measured at the
///   layer where it belongs, by giving side A the `x - 2` recursion and side B
///   the `x - 1` one, and the refusal is `FunctionalDisagreement` — a DEFEQ
///   verdict, not a typing accident.
#[test]
fn probe_c6_divergence_and_wrong_argument_are_still_caught_and_are_different_refusals() {
    let mut env = Environment::with_prelude();
    install_cds(&mut env, "cds");

    // (d1) the diverging argument: side A's proof does not fit.
    let diverging = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(succ(Expr::bvar(2))), cnst("Nat.zero")),
    };
    let refusal = check_faithful_wf_functional(&env, "cds", &diverging, &nat_carrier())
        .expect_err("a non-decreasing emitted recursion cannot take side A's decrease proof");
    assert!(
        matches!(refusal, GateRefusal::DecreaseSlotBorrowRefused { .. }),
        "the divergence catch must be reported as a TYPING refusal, got {refusal:?}"
    );

    // (d3) a genuinely terminating, genuinely different argument. Side A
    // recurses at `x - 2`; side B at `x - 1`. The borrowed proof is
    // `Nat.lt (x-2) x`, which types at side B's `x - 1`? It does not — so
    // measure the pure defeq case with side A and side B recursing at the SAME
    // typed shape but different values, via a second declaration.
    define(
        &mut env,
        "cds_two_back",
        Expr::arrow(nat(), nat()),
        wf_body(cds_f(
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
        )),
    );
    // Side B for `cds_two_back` claims the ELSE branch is `1` — a wrong VALUE
    // at a correct argument, so the borrow succeeds, the term types, and the
    // refusal is a definitional-equality verdict.
    let wrong_value = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(sub(Expr::bvar(2), nat_num(2))), nat_num(1)),
    };
    let value_refusal =
        check_faithful_wf_functional(&env, "cds_two_back", &wrong_value, &nat_carrier())
            .expect_err("a wrong emitted value must be refused at the F layer");
    assert!(
        matches!(value_refusal, GateRefusal::FunctionalDisagreement { .. }),
        "a wrong VALUE is a defeq verdict, distinct from the borrow refusal, got {value_refusal:?}"
    );
    // …and the correct one for that declaration admits, so the refusal above
    // is not the lane simply rejecting `cds_two_back`.
    let right_value = ReflectedWfFunctional {
        functional: cds_f(cds_then_side_b(sub(Expr::bvar(2), nat_num(2))), cnst("Nat.zero")),
    };
    check_faithful_wf_functional(&env, "cds_two_back", &right_value, &nat_carrier())
        .expect("the faithful emission for `cds_two_back` admits");
    eprintln!(
        "PROBE-ROW | c6 CATCHES SURVIVE THE BORROW| diverging arg: DecreaseSlotBorrowRefused \
         (typing) | wrong value: FunctionalDisagreement (defeq) | faithful sibling: ADMITS"
    );
}

// ═══════ (c7) the R1 structural lane inherits the precondition ═══════

/// `check_faithful_equations` mints a RECURSIVE `Faithful`, so the same rule
/// applies to it — and this probe pins that the honest `tozero` is unaffected.
///
/// Structural recursion has no decrease slot to poison (`Nat.rec`'s `ih`
/// erases the recursive argument and carries no proof), so this arm is not
/// closing a termination hole. It is keeping the gate and the mint from
/// disagreeing about one declaration, which is the c4 reasoning applied to
/// the other recursive lane.
#[test]
fn probe_c7_the_structural_lane_refuses_an_axiom_bearing_declaration() {
    fn tozero_body(zero_case: Expr) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::apps(
                Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
                [
                    Expr::lam(BinderInfo::Default, nat(), nat()),
                    zero_case,
                    Expr::lam(
                        BinderInfo::Default,
                        nat(),
                        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
                    ),
                    Expr::bvar(0),
                ],
            ),
        )
    }
    fn reflected() -> ReflectedStructuralRec {
        ReflectedStructuralRec {
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
        }
    }

    // the control: the honest declaration still ADMITS.
    let mut honest = Environment::with_prelude();
    define(&mut honest, "tozero", Expr::arrow(nat(), nat()), tozero_body(cnst("Nat.zero")));
    let faithful = check_faithful_equations(&honest, "tozero", &reflected(), &nat_carrier())
        .expect("the honest structural recursion must still admit");
    assert_eq!(faithful.method(), FaithfulnessMethod::PerEquationDefeq);

    // the mutation: an axiom in the zero case.
    let mut tainted = Environment::with_prelude();
    tainted
        .add_decl(Declaration::Axiom {
            name: Name::from_string("c7_debt"),
            level_params: vec![],
            type_: nat(),
        })
        .expect("an axiom may be declared");
    define(&mut tainted, "tozero", Expr::arrow(nat(), nat()), tozero_body(cnst("c7_debt")));
    let mut tainted_cases = reflected();
    tainted_cases.cases[0].value = cnst("c7_debt");
    let refusal = check_faithful_equations(&tainted, "tozero", &tainted_cases, &nat_carrier())
        .expect_err("a recursive declaration resting on an axiom must not be emitted");
    let (assumptions, _) = refusal_names(&refusal);
    assert!(assumptions.iter().any(|name| name == "c7_debt"), "{assumptions:?}");
    eprintln!(
        "PROBE-ROW | c7 STRUCTURAL LANE           | honest tozero: ADMITS (PerEquationDefeq) | \
         axiom in the zero case: REFUSED naming `c7_debt`"
    );
}

// ═══════ (c8) the whole-term lane inherits it too ═══════

/// Probe w8 measured `check_faithful` — the WHOLE-TERM lane — **admitting** a
/// `WellFounded.fix` side A when handed the body itself. That makes it a
/// recursive-`Faithful`-minting lane whether or not it was designed as one,
/// and the escape was reachable through it. It now refuses an axiom-bearing
/// recursive side A, and still admits the honest one.
#[test]
fn probe_c8_the_whole_term_lane_refuses_an_axiom_bearing_recursion() {
    // control: the honest WF side A still admits at the whole-term lane
    // (w8's measurement, preserved).
    let mut honest = Environment::with_prelude();
    install_cds(&mut honest, "cds");
    let honest_body = honest
        .get_const(&Name::from_string("cds"))
        .and_then(|c| c.value.clone())
        .expect("side A body");
    check_faithful(&honest, "cds", &honest_body, &nat_carrier())
        .expect("w8's measurement must survive: the whole-term lane admits an honest WF side A");

    // mutation: the axiom-bearing diverging declaration c1 admits at the
    // kernel is refused here.
    let mut tainted = Environment::with_prelude();
    install_bogus_decrease(&mut tainted, "c8_bogus_lt");
    let diverging_body = wf_body(cds_f(
        add(
            Expr::bvar(2),
            Expr::apps(
                Expr::bvar(1),
                [succ(Expr::bvar(2)), Expr::app(cnst("c8_bogus_lt"), Expr::bvar(2))],
            ),
        ),
        cnst("Nat.zero"),
    ));
    define(&mut tainted, "cds_axiom_diverging", Expr::arrow(nat(), nat()), diverging_body.clone());
    let refusal = check_faithful(&tainted, "cds_axiom_diverging", &diverging_body, &nat_carrier())
        .expect_err(
            "the whole-term lane admits a WF side A (w8), so it must carry the same recursive \
             precondition — otherwise the escape simply moves one function over",
        );
    let (assumptions, _) = refusal_names(&refusal);
    assert!(assumptions.iter().any(|name| name == "c8_bogus_lt"), "{assumptions:?}");
    eprintln!(
        "PROBE-ROW | c8 WHOLE-TERM LANE           | honest WF side A: still ADMITS (w8 preserved) \
         | axiom-bearing diverging side A: REFUSED naming `c8_bogus_lt`"
    );
}

// ═══════ (c9) a NON-recursive body is untouched ═══════

/// **The scope boundary, asserted rather than assumed.**
///
/// The precondition is deliberately scoped to RECURSIVE declarations, where
/// the closure is part of the termination argument. A non-recursive
/// axiom-bearing body still admits at `check_faithful` — its `DefId` is
/// refused by `mint::decide_mint`, which is where the disclosure rule for
/// non-recursive declarations already lives, so nothing is emitted for it
/// either; but the GATE's verdict is unchanged.
///
/// This matters as a control: if a future edit made the audit unconditional,
/// this probe fails and the change has to be argued rather than absorbed.
#[test]
fn probe_c9_a_non_recursive_body_keeps_its_previous_verdict() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c9_debt"),
        level_params: vec![],
        type_: nat(),
    })
    .expect("an axiom may be declared");
    // `fun (_ : Nat) => c9_debt` — no recursion anywhere.
    let body = Expr::lam(BinderInfo::Default, nat(), cnst("c9_debt"));
    define(&mut env, "constant_debt", Expr::arrow(nat(), nat()), body.clone());

    check_faithful(&env, "constant_debt", &body, &nat_carrier()).expect(
        "the recursive precondition must not silently become a general tightening: a \
         non-recursive body's gate verdict is unchanged, and its DefId is refused by the mint",
    );

    // …and the mint is where that declaration is stopped, so nothing is
    // emitted for it. (Refutation-only: this asserts the mint's existing rule
    // still fires, not that the gate did anything.)
    let audit = audit_term_closure(&env, "constant_debt", &Expr::arrow(nat(), nat()), &body);
    assert!(
        !audit.closure().is_audited_empty(),
        "the declaration's closure is non-empty, which is what `mint::decide_mint` refuses on"
    );
    eprintln!(
        "PROBE-ROW | c9 SCOPE BOUNDARY            | non-recursive axiom-bearing body: gate \
         verdict UNCHANGED (admits) | its closure is non-empty, so the MINT refuses the DefId"
    );
}
