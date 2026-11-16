//! The zero-authority frontend firewall.
//!
//! Rust and Lean-compatible Clean are the two authoritative languages. TrustJS,
//! TrustPy, and TrustZig are admitted only as untrusted frontends, and the
//! ratified doctrine draws one line for them: frontend text, annotations, and
//! inferred intent may **propose** an artifact or an obligation, but may never
//! assert a proposition, introduce an unchecked assumption, or narrow the
//! evidence that judges the proposal.
//!
//! Prose cannot enforce that. This module is the enforcement, and it lives in
//! `trust-types` for the same reason [`crate::assumption`] does: it is the
//! shared dependency of the frontends that produce proposals, the router and
//! kernel lanes that admit them, and the repair loop that writes clauses back
//! into source, so the two ends of the contract cannot drift apart.
//!
//! Two mechanisms, in increasing order of strength:
//!
//! 1. [`ClaimProvenance`] is a *tag* every claim carries. It is checked by
//!    [`admit_role`] at an admission boundary: a frontend-tagged term is
//!    admissible as a [`ProofRole::Goal`] and nothing else. This mirrors the E6
//!    `trust_import_*` discipline — an imported program function becomes a
//!    kernel constant only through a step that re-checks it, never by assertion.
//! 2. [`FrontendProposal`] makes the same rule *structural*: it is the only
//!    carrier for frontend-derived material, and its only exit is
//!    [`FrontendProposal::into_goal`]. There is deliberately no
//!    `into_hypothesis`, no `into_axiom`, and no `Deref` — a caller cannot
//!    reach the payload except by first turning it into a goal, so the unsound
//!    use is unrepresentable rather than merely rejected.
//!
//! The third mechanism, a pinned and digest-checked fidelity manifest that
//! fixed a frontend's oracle, input domain, corpus and waivers before its
//! elaborator ran, had one user, `trust-js-autoform`; both were deleted on
//! 2026-11-10 with the other unused TrustJS crates (`git log` has them). A
//! frontend that ships again brings its fidelity evidence back with it.
//!
//! # What this module is not
//!
//! It is not a proof that a frontend is correct, and it is not evidence that
//! one has been reviewed. It is the structural guarantee that whatever a
//! frontend says lands on the *goal* side of the turnstile, where the kernel,
//! the router, and the fidelity ledger get to judge it.

use std::fmt;

use serde::{Deserialize, Serialize};


/// An untrusted, zero-authority source language.
///
/// Each of these elaborates fail-closed into a Rust + Lean/TrustIr artifact and
/// carries independently fixed fidelity evidence. None of them is authoritative
/// for a proposition, which is exactly what [`ClaimProvenance::Frontend`]
/// records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FrontendLanguage {
    /// TrustJS — JavaScript.
    JavaScript,
    /// TrustJS — TypeScript (erased to JavaScript before elaboration).
    TypeScript,
    /// TrustPy — Python.
    Python,
    /// TrustZig — Zig.
    Zig,
}

impl FrontendLanguage {
    /// The stable wire name, used in diagnostics and evidence records.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::JavaScript => "javascript",
            Self::TypeScript => "typescript",
            Self::Python => "python",
            Self::Zig => "zig",
        }
    }
}

impl fmt::Display for FrontendLanguage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Where a claim came from, for the purpose of deciding what it may do.
///
/// The default is [`ClaimProvenance::Authoritative`] so that existing Rust and
/// Clean material keeps exactly the authority it has today; only material that
/// explicitly tags itself as frontend-derived loses it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ClaimProvenance {
    /// Rust or Lean-compatible Clean: one of the two authoritative languages.
    #[default]
    Authoritative,
    /// An untrusted frontend. Proposes; never asserts.
    Frontend(FrontendLanguage),
}

impl ClaimProvenance {
    /// Whether material with this provenance may be believed without a proof.
    ///
    /// False for every frontend. Callers that would otherwise assume, assert,
    /// or axiomatize must consult this first.
    #[must_use]
    pub fn grants_proof_authority(self) -> bool {
        matches!(self, Self::Authoritative)
    }

    /// The frontend language, if this is frontend-derived.
    #[must_use]
    pub fn frontend(self) -> Option<FrontendLanguage> {
        match self {
            Self::Authoritative => None,
            Self::Frontend(lang) => Some(lang),
        }
    }

    /// Whether a proposal with this provenance must be surfaced to a reviewer
    /// rather than applied automatically.
    ///
    /// A frontend-proposed contract clause is an unverified semantic claim
    /// written in a language that is not authoritative for semantics. Applying
    /// it without review would let the frontend introduce, by the back door, the
    /// unchecked assumption the firewall exists to prevent.
    #[must_use]
    pub fn requires_review(self) -> bool {
        !self.grants_proof_authority()
    }
}

impl fmt::Display for ClaimProvenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Authoritative => f.write_str("authoritative"),
            Self::Frontend(lang) => write!(f, "frontend:{lang}"),
        }
    }
}

/// The role a term would play once admitted.
///
/// The distinction the firewall turns on is which side of the turnstile the
/// term lands on: a [`Goal`](ProofRole::Goal) is *checked*, everything else is
/// *believed*.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofRole {
    /// A proposition to be discharged. Believing it requires a proof, so a
    /// wrong goal costs a failed verification, never a false verdict.
    Goal,
    /// A proposition assumed while discharging something else — a precondition
    /// in a body proof, a loop invariant on entry, an assumed callee summary.
    /// A wrong hypothesis proves anything.
    Hypothesis,
    /// A proposition asserted into the kernel environment with no proof term.
    /// A wrong axiom is inconsistency.
    Axiom,
    /// A defining equation admitted into the kernel environment, making a
    /// constant unfold to a body. A wrong definition silently changes what
    /// every downstream statement means.
    DefiningEquation,
}

impl ProofRole {
    /// The stable wire name, used in diagnostics and evidence records.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Goal => "goal",
            Self::Hypothesis => "hypothesis",
            Self::Axiom => "axiom",
            Self::DefiningEquation => "defining-equation",
        }
    }

    /// Whether a term in this role is independently checked before it is
    /// believed. Only a goal is.
    #[must_use]
    pub fn is_checked(self) -> bool {
        matches!(self, Self::Goal)
    }
}

impl fmt::Display for ProofRole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Why the firewall refused an admission.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FirewallRejection {
    /// A frontend-derived term was offered in a role that is believed rather
    /// than checked.
    RoleForbidden {
        /// The frontend that produced the term.
        language: FrontendLanguage,
        /// The role it was offered in.
        role: ProofRole,
    },
}

impl fmt::Display for FirewallRejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RoleForbidden { language, role } => write!(
                f,
                "frontend firewall: a {language} term may only be a goal, never a {role} \
                 (an untrusted frontend proposes; it never asserts)"
            ),
        }
    }
}

impl std::error::Error for FirewallRejection {}

/// The admission check: may material with this provenance play this role?
///
/// This is the runtime half of the firewall, for boundaries that carry a role
/// as data (a router admitting an obligation, a kernel lane deciding between
/// checking a term and asserting it). Boundaries that know the role statically
/// should use [`FrontendProposal`] instead, where the wrong answer does not
/// compile.
///
/// # Errors
///
/// [`FirewallRejection::RoleForbidden`] when frontend-derived material is
/// offered in any role but [`ProofRole::Goal`].
pub fn admit_role(provenance: ClaimProvenance, role: ProofRole) -> Result<(), FirewallRejection> {
    match provenance {
        ClaimProvenance::Authoritative => Ok(()),
        ClaimProvenance::Frontend(language) => {
            if role.is_checked() {
                Ok(())
            } else {
                Err(FirewallRejection::RoleForbidden { language, role })
            }
        }
    }
}

/// Where a frontend proposal came from, precisely enough to audit it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrontendOrigin {
    /// The untrusted source language.
    pub language: FrontendLanguage,
    /// The source artifact — a path, a module key, a corpus case id.
    pub artifact: String,
    /// The elaborator that produced the proposal, named so a bad proposal is
    /// attributable to a component rather than to "the frontend".
    pub elaborator: String,
}

impl FrontendOrigin {
    /// Record a proposal's origin.
    #[must_use]
    pub fn new(
        language: FrontendLanguage,
        artifact: impl Into<String>,
        elaborator: impl Into<String>,
    ) -> Self {
        Self { language, artifact: artifact.into(), elaborator: elaborator.into() }
    }

    /// The provenance tag this origin carries.
    #[must_use]
    pub fn provenance(&self) -> ClaimProvenance {
        ClaimProvenance::Frontend(self.language)
    }
}

/// The only carrier for frontend-derived material crossing into Trust.
///
/// The payload is private and there is exactly one way out —
/// [`FrontendProposal::into_goal`]. A caller who wants the term as a
/// hypothesis, an axiom, or a defining equation has no method to call and no
/// field to read: the unsound use does not typecheck, so the firewall does not
/// depend on anyone remembering to check a tag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontendProposal<T> {
    origin: FrontendOrigin,
    payload: T,
}

impl<T> FrontendProposal<T> {
    /// Wrap frontend-derived material. Called by the elaborator that produced
    /// it, at the moment it is produced — before it can be confused with
    /// authoritative material.
    pub fn new(origin: FrontendOrigin, payload: T) -> Self {
        Self { origin, payload }
    }

    /// Where this proposal came from.
    #[must_use]
    pub fn origin(&self) -> &FrontendOrigin {
        &self.origin
    }

    /// The provenance tag, for boundaries that record it.
    #[must_use]
    pub fn provenance(&self) -> ClaimProvenance {
        self.origin.provenance()
    }

    /// Inspect the payload without admitting it. Inspection is always allowed —
    /// rendering a proposal into a diagnostic, hashing it, or diffing it makes
    /// no claim about its truth.
    #[must_use]
    pub fn inspect(&self) -> &T {
        &self.payload
    }

    /// The only exit: admit the proposal as a goal to be discharged.
    ///
    /// Deliberately infallible — a goal is the one role a frontend proposal may
    /// always take, because a wrong goal costs a failed verification rather than
    /// a false verdict.
    #[must_use]
    pub fn into_goal(self) -> ProofGoal<T> {
        ProofGoal {
            provenance: self.origin.provenance(),
            origin: Some(self.origin),
            payload: self.payload,
        }
    }

    /// Admit the proposal in a role chosen at runtime.
    ///
    /// Present for boundaries that receive the role as data. It can only ever
    /// return a [`ProofGoal`]; every other role is a [`FirewallRejection`].
    ///
    /// # Errors
    ///
    /// [`FirewallRejection::RoleForbidden`] for any role but
    /// [`ProofRole::Goal`].
    pub fn admit_as(self, role: ProofRole) -> Result<ProofGoal<T>, FirewallRejection> {
        admit_role(self.origin.provenance(), role)?;
        Ok(self.into_goal())
    }
}

/// Material admitted as a proposition to be discharged.
///
/// Carries its provenance forward so a downstream consumer that later wants to
/// assume rather than check it can still be refused by [`admit_role`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofGoal<T> {
    provenance: ClaimProvenance,
    origin: Option<FrontendOrigin>,
    payload: T,
}

impl<T> ProofGoal<T> {
    /// Admit authoritative material as a goal. The provenance stays
    /// authoritative, so nothing downstream is weakened by routing a Rust or
    /// Clean obligation through this type.
    pub fn authoritative(payload: T) -> Self {
        Self { provenance: ClaimProvenance::Authoritative, origin: None, payload }
    }

    /// The provenance of the goal's statement.
    #[must_use]
    pub fn provenance(&self) -> ClaimProvenance {
        self.provenance
    }

    /// The frontend origin, when the goal is frontend-derived.
    #[must_use]
    pub fn origin(&self) -> Option<&FrontendOrigin> {
        self.origin.as_ref()
    }

    /// The statement to discharge.
    #[must_use]
    pub fn statement(&self) -> &T {
        &self.payload
    }

    /// Consume the goal, yielding the statement to a solver or kernel lane.
    #[must_use]
    pub fn into_statement(self) -> T {
        self.payload
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn js_origin() -> FrontendOrigin {
        FrontendOrigin::new(FrontendLanguage::JavaScript, "case.js", "test")
    }

    #[test]
    fn frontend_term_is_rejected_as_a_hypothesis() {
        // The headline invariant: a frontend-derived term offered as something
        // that would be BELIEVED is refused, in every non-goal role.
        for role in [ProofRole::Hypothesis, ProofRole::Axiom, ProofRole::DefiningEquation] {
            let proposal = FrontendProposal::new(js_origin(), "x + 1 <= u32::MAX");
            let rejected = proposal.admit_as(role);
            assert_eq!(
                rejected,
                Err(FirewallRejection::RoleForbidden {
                    language: FrontendLanguage::JavaScript,
                    role,
                }),
                "a frontend term must never be admitted as a {role}"
            );
            assert!(
                admit_role(ClaimProvenance::Frontend(FrontendLanguage::JavaScript), role).is_err()
            );
        }
    }

    #[test]
    fn frontend_term_is_admissible_as_a_goal() {
        let proposal = FrontendProposal::new(js_origin(), "x + 1 <= u32::MAX");
        let goal = proposal.admit_as(ProofRole::Goal).expect("a goal is the permitted role");
        assert_eq!(goal.provenance(), ClaimProvenance::Frontend(FrontendLanguage::JavaScript));
        assert_eq!(goal.statement(), &"x + 1 <= u32::MAX");
        // The provenance survives admission, so a downstream consumer that
        // wants to ASSUME the discharged goal is still refused.
        assert!(admit_role(goal.provenance(), ProofRole::Hypothesis).is_err());
    }

    #[test]
    fn authoritative_material_keeps_every_role() {
        for role in
            [ProofRole::Goal, ProofRole::Hypothesis, ProofRole::Axiom, ProofRole::DefiningEquation]
        {
            assert!(admit_role(ClaimProvenance::Authoritative, role).is_ok());
        }
        assert!(ClaimProvenance::Authoritative.grants_proof_authority());
        assert!(!ClaimProvenance::default().requires_review());
    }

    #[test]
    fn every_frontend_language_loses_authority() {
        for lang in [
            FrontendLanguage::JavaScript,
            FrontendLanguage::TypeScript,
            FrontendLanguage::Python,
            FrontendLanguage::Zig,
        ] {
            let p = ClaimProvenance::Frontend(lang);
            assert!(!p.grants_proof_authority(), "{lang} must not grant proof authority");
            assert!(p.requires_review(), "{lang} proposals must default to review");
            assert_eq!(p.frontend(), Some(lang));
        }
    }
}
