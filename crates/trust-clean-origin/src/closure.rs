// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The axiom-closure audit — ONE walker, extended from DECLARATIONS to
//! TERMS.**
//!
//! # Why this module exists (the R2 blocker, verbatim from the design)
//!
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`, the §6e
//! MEASUREMENT NOTE (2026-08-21), finding 2:
//!
//! > That typing guarantee is exactly as strong as the AXIOM CLOSURE of the
//! > proof terms side B puts in the decrease slot. Measured: with
//! > `axiom bogus : ∀ x, Nat.lt (succ x) x` in scope, a DIVERGING functional
//! > kernel-checks and the definition ADMITS. The audited-empty axiom-closure
//! > machinery exists (`mint.rs`, `AxiomClosure::is_audited_empty`) but today
//! > covers side A's declaration only. **R2 must extend it to side B's proof
//! > terms; without that extension R2 is not landable.**
//!
//! A well-founded functional's recursive slot has type
//! `rec : (y : α) → r y x → C y`. The kernel's own TYPING RULE refuses a
//! diverging off-by-one, because no proof of `Nat.lt (succ x) x` exists to
//! fill the slot — *unless one is assumed*. So on the WF lane the kernel type
//! check is not the guard; **the kernel type check plus an audited-empty
//! axiom closure over the terms in the slots** is.
//!
//! # THE MEASURED FINDING THIS MODULE RECORDS
//!
//! The closure machinery that existed before this module was **name-keyed**,
//! and that is exactly why it could not see side B:
//!
//! | producer | rooted at | can it see a free-standing term? |
//! |---|---|---|
//! | `clean_kernel::Environment::axiom_deps(&Name)` | a DECLARATION's type+value | **no** — a term that is not a declaration is invisible |
//! | `trust_certify::clean_island` → `KernelStatus::closure()` | a DECLARATION | **no** |
//! | `crate::mint::decide_mint` | reads the above | **no** |
//! | `clean_kernel::Environment::audit_certification(goal, term)` | two EXPRESSIONS | **yes**, but only for a `Prop`-sorted goal |
//!
//! Side B's functional is not a declaration and never becomes one; its type
//! (`(x : Nat) → ((y : Nat) → Nat.lt y x → Nat) → Nat`) lives in `Type`, not
//! `Prop`. Both name-keyed routes are therefore structurally unable to see
//! it, and `audit_certification` — the one expression-rooted walker, and the
//! one [`AxiomClosure::audited`]'s own documentation names as the meaning of
//! "audited" — rejects the goal as `GoalNotProposition`.
//!
//! **The smallest honest extension, and it is a spelling not a new walker:**
//! for a term `t : T` at any sort, the judgment `@Eq.{u} T t t` **is** a
//! `Prop` whatever `T`'s sort is, and `@Eq.refl.{u} T t` proves it. Auditing
//! that judgment walks the const closure of `T` and of `t` — every constant
//! in every decrease slot included — through the kernel's own unfiltered,
//! strict-recheck walker. No second traversal is written here.
//! [`audit_term_closure`] is that spelling; [`audit_proof_closure`] is the
//! direct call for the lanes that already have a `Prop` goal and a witness.
//!
//! # Why `audit_certification` and not the legacy `axiom_deps`
//!
//! `trust_symbols::AxiomClosure` documents the rule this module obeys:
//!
//! > `clean_kernel`'s `axiom_deps(&Name)` returns a *name list* and never
//! > re-typechecks, so it cannot see `StructuralOnly`, `MissingValue` or
//! > `NonCanonicalFoundation` — a structurally-inserted theorem has an empty
//! > `axiom_deps` and is not thereby clean. **A producer holding only
//! > `axiom_deps` must pass `AxiomClosure::unrecorded`.**
//! > `AxiomClosure::audited` means `Environment::audit_certification`
//! > (equivalently `cert_meter::grade`) returned a positive grade.
//!
//! The kernel says the same thing from its side: `audit_certification` is
//! documented as the replacement for "the legacy `axiom_deps(name)` pattern",
//! and it re-runs the full declaration checker on every reachable stored
//! declaration. This module is therefore the crate's **only** producer of an
//! `AxiomClosure::audited`, and `gate.rs`'s structural-induction lane — which
//! used the legacy install-a-theorem-in-a-clone-then-`axiom_deps` idiom, and
//! could only ever have justified `unrecorded` — is routed through it too.
//!
//! # Fail-closed mapping
//!
//! The kernel reports *issues*, of which only two are assumptions:
//!
//! * `NonFoundationalAxiom` → [`Assumption::domain_axiom`];
//! * `TrustMarker` → [`Assumption::trust_marker`].
//!
//! **Every other issue means the audit did not complete cleanly**, which is
//! not the same fact as "assumptions were found" and must not be reported as
//! an empty closure. Those land in [`ClosureAudit::blocking`] and force the
//! recorded closure to [`AxiomClosure::unrecorded`] — the state that is never
//! certifiable. The assumption NAMES are still retained for disclosure, so a
//! refusal can say what it saw even when it cannot claim to have seen
//! everything.

use clean_kernel::{CertificationIssue, Environment, Expr, Level, Name, TypeChecker};
use trust_symbols::{Assumption, AxiomClosure};

/// The result of one closure audit.
///
/// Deliberately richer than an [`AxiomClosure`]: v7/D3 requires a refusal to
/// name the fix, and "this proof cites `bogus`" and "this proof reaches a
/// structurally-inserted declaration" are different conversations with the
/// author even though both refuse.
#[derive(Debug, Clone)]
pub struct ClosureAudit {
    subject: String,
    closure: AxiomClosure,
    assumptions: Vec<String>,
    blocking: Vec<String>,
}

impl ClosureAudit {
    /// What was audited, in operator-facing words.
    #[must_use]
    pub fn subject(&self) -> &str {
        &self.subject
    }

    /// The closure as `trust-symbols` records it.
    ///
    /// [`AxiomClosure::unrecorded`] whenever the audit could not complete
    /// cleanly, per this module's fail-closed mapping — so a caller that
    /// consults only [`AxiomClosure::is_audited_empty`] still fails closed.
    #[must_use]
    pub fn closure(&self) -> &AxiomClosure {
        &self.closure
    }

    /// Every assumption NAME the audit saw, sorted.
    ///
    /// Populated even when [`Self::closure`] is `unrecorded`: an incomplete
    /// audit that nevertheless spotted `sorry` should say so.
    #[must_use]
    pub fn assumptions(&self) -> &[String] {
        &self.assumptions
    }

    /// Certification-blocking findings that are **not** assumptions —
    /// structural insertion, missing values, staged headers, dependency
    /// cycles, a rejected term, a non-canonical foundation.
    #[must_use]
    pub fn blocking(&self) -> &[String] {
        &self.blocking
    }

    /// The one predicate a gate may act on: the audit RAN, completed, and
    /// found nothing.
    #[must_use]
    pub fn is_clear(&self) -> bool {
        self.closure.is_audited_empty() && self.blocking.is_empty()
    }
}

/// Audit a proof judgment `witness : statement`, `statement` a `Prop`.
///
/// The direct call: this is the shape `Environment::audit_certification` was
/// written for, and the shape `gate.rs`'s structural-induction fallback
/// already has in hand.
#[must_use]
pub fn audit_proof_closure(
    env: &Environment,
    subject: &str,
    statement: &Expr,
    witness: &Expr,
) -> ClosureAudit {
    classify(subject, env.audit_certification(statement, witness))
}

/// Audit an arbitrary term `term : ty`, **at any sort** — the extension side B
/// needs.
///
/// # The `Eq`-judgment spelling, and why it is not a loophole
///
/// `audit_certification` requires a `Prop` goal, and a functional's type is
/// not one. `@Eq.{u} ty term term` is a `Prop` for every sort `u`, and
/// `@Eq.refl.{u} ty term` is its proof, so the pair is a well-formed proof
/// judgment whose const closure is exactly `ty`'s ∪ `term`'s. The audit is
/// therefore the same walk over the same set, not a weaker one:
///
/// * `infer_sort(goal)` forces `ty` to be a well-formed type and `term : ty`
///   — a term that does not have the claimed type cannot even reach the walk;
/// * `check_type(Eq.refl ty term, Eq ty term term)` re-checks the same fact
///   independently, and a failure is reported as `TermRejected`;
/// * the closure walk is the kernel's own, unfiltered, with a strict recheck
///   of every reachable stored declaration.
///
/// The reflexive judgment is trivial ON PURPOSE. This function is not asking
/// the kernel to *prove* anything about `term`; it is asking the kernel what
/// `term` RESTS ON. A non-trivial goal would conflate the two questions and
/// let a hard proof search failure read as a clean closure.
#[must_use]
pub fn audit_term_closure(
    env: &Environment,
    subject: &str,
    ty: &Expr,
    term: &Expr,
) -> ClosureAudit {
    let checker = TypeChecker::new(env);
    let Ok(sort) = checker.infer_sort(ty) else {
        return ClosureAudit {
            subject: subject.to_owned(),
            closure: AxiomClosure::unrecorded(),
            assumptions: Vec::new(),
            blocking: vec![
                "the type the term was to be audited at is not a well-formed type, so no \
                 closure could be walked"
                    .to_owned(),
            ],
        };
    };
    drop(checker);

    let goal = eq_judgment(&sort, ty, term, term);
    let witness = Expr::apps(
        Expr::const_(Name::interned("Eq.refl"), vec![sort]),
        [ty.clone(), term.clone()],
    );
    classify(subject, env.audit_certification(&goal, &witness))
}

/// `@Eq.{u} ty lhs rhs`.
fn eq_judgment(sort: &Level, ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::interned("Eq"), vec![sort.clone()]),
        [ty.clone(), lhs.clone(), rhs.clone()],
    )
}

/// Split the kernel's issue list into assumptions and audit-blocking findings.
///
/// The `#[non_exhaustive]`-in-spirit arm is the wildcard: a
/// `CertificationIssue` variant added upstream lands in `blocking`, which
/// refuses. A new kernel hazard must never default into "no assumptions".
fn classify(subject: &str, audit: clean_kernel::CertificationAudit) -> ClosureAudit {
    let mut assumptions: Vec<Assumption> = Vec::new();
    let mut blocking: Vec<String> = Vec::new();

    for issue in &audit.issues {
        match issue {
            CertificationIssue::NonFoundationalAxiom { name } => {
                match Assumption::domain_axiom(name.to_string()) {
                    Ok(assumption) => assumptions.push(assumption),
                    // An unnameable assumption cannot be disclosed by name, so
                    // it is recorded as a blocking finding rather than dropped.
                    Err(error) => blocking.push(format!("an unnameable domain axiom: {error}")),
                }
            }
            CertificationIssue::TrustMarker { name } => {
                match Assumption::trust_marker(name.to_string()) {
                    Ok(assumption) => assumptions.push(assumption),
                    Err(error) => blocking.push(format!("an unnameable trust marker: {error}")),
                }
            }
            other => blocking.push(render_issue(other)),
        }
    }

    let mut names: Vec<String> =
        assumptions.iter().map(|assumption| assumption.name().to_owned()).collect();
    names.sort_unstable();
    names.dedup();

    // FAIL-CLOSED: an audit that hit a blocking finding did not complete, and
    // an incomplete audit is `unrecorded`, never "empty". This is the exact
    // softening `trust_symbols::AxiomClosure` forbids.
    let closure = if blocking.is_empty() {
        AxiomClosure::audited(assumptions)
    } else {
        AxiomClosure::unrecorded()
    };

    ClosureAudit { subject: subject.to_owned(), closure, assumptions: names, blocking }
}

/// One line per blocking finding, bounded: names and kernel-authored errors
/// only, never a rejected user-sized term.
fn render_issue(issue: &CertificationIssue) -> String {
    match issue {
        CertificationIssue::GoalNotProposition { error } => {
            format!("the audited judgment is not a proposition: {error}")
        }
        CertificationIssue::TermRejected { error } => {
            format!("the kernel rejected the audited term at its claimed type: {error}")
        }
        CertificationIssue::MissingDeclaration { name } => {
            format!("`{name}` is referenced but absent from the environment")
        }
        CertificationIssue::MissingValue { name } => {
            format!("`{name}` has no value, so its own closure is unavailable")
        }
        CertificationIssue::StructuralOnly { name } => {
            format!("`{name}` was inserted by structural validation only, not a kernel check")
        }
        CertificationIssue::Unchecked { name } => {
            format!("`{name}` entered the environment through an unchecked path")
        }
        CertificationIssue::NeedsRecheck { name } => {
            format!("`{name}` is a structural import still marked as needing a genuine recheck")
        }
        CertificationIssue::UnverifiedKernelObject { name } => {
            format!(
                "`{name}` is a value-less kernel object with no record that it passed the inductive checker"
            )
        }
        CertificationIssue::Unsafe { name } => format!("`{name}` is marked unsafe"),
        CertificationIssue::Partial { name } => format!("`{name}` is marked partial"),
        CertificationIssue::Staged { name } => {
            format!(
                "`{name}` is a provisional header staged by header-first elaboration, with no value behind it"
            )
        }
        CertificationIssue::NonCanonicalFoundation { name, detail } => {
            format!(
                "`{name}` is foundation-shaped but does not match the canonical declaration: {detail}"
            )
        }
        CertificationIssue::InvalidDeclaration { name, error } => {
            format!("re-running the declaration checker rejected `{name}`: {error}")
        }
        CertificationIssue::DependencyCycle { names } => {
            let listed: Vec<String> = names.iter().map(ToString::to_string).collect();
            format!("the reachable constant graph contains a cycle: {}", listed.join(" -> "))
        }
        // Assumptions are handled by the caller; reaching them here would be a
        // classification bug, so say so rather than swallow it.
        CertificationIssue::NonFoundationalAxiom { name }
        | CertificationIssue::TrustMarker { name } => {
            format!("INTERNAL: assumption `{name}` reached the blocking renderer")
        }
        // `CertificationIssue` is `#[non_exhaustive]`. A hazard the kernel
        // learns to report after this crate was written must BLOCK, never
        // vanish into an empty closure — that is the whole point of routing
        // every non-assumption issue through here.
        other => format!("an unrecognised certification hazard reported by the kernel: {other:?}"),
    }
}
