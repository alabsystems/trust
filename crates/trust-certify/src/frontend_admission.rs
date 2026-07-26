//! The kernel half of the frontend firewall.
//!
//! [`trust_types::frontend_firewall`] fixes the vocabulary — an untrusted
//! frontend proposes, it never asserts. This module is where that rule meets the
//! Clean kernel, and it is deliberately the *only* route by which
//! frontend-derived material may reach an [`Environment`].
//!
//! # The shape, mirrored from E6
//!
//! E6 kernel-import does not believe a Rust function because an analysis says it
//! is total; it mints a `trust_import_*` constant only after `add_decl` has
//! FULLY KERNEL-CHECKED a defining equation, and a mistaken term is rejected
//! rather than admitted. The frontend rule is the same discipline one notch
//! stricter: a frontend statement is not admitted into the environment *at all*.
//! It becomes a goal, and the only way to believe it afterwards is to hand the
//! kernel a proof term that `check_type` accepts against it.
//!
//! Concretely, this module has:
//!
//! * [`kernel_admit`] — takes `&Environment`, not `&mut Environment`. A frontend
//!   proposal cannot extend the environment because this lane has no way to
//!   mutate one. `Declaration::Axiom`, `Declaration::Definition`,
//!   `add_skolem_axiom`, and the E6 `Admission` mint are all unreachable from
//!   here, so there is no frontend path to a hypothesis, an axiom, or a
//!   defining equation — not merely a checked one, an absent one.
//! * [`discharge_with_kernel_proof`] — the only way a [`FrontendGoal`] becomes
//!   believed. The proof term is supplied by an authoritative producer and
//!   re-checked by the kernel; a frontend that supplies its own proof still has
//!   to satisfy `check_type`, which is exactly the de Bruijn criterion the rest
//!   of this crate runs on.
//!
//! # What admission does check
//!
//! Well-formedness, and nothing else. A statement whose type is not a sort is
//! not a proposition at all, so admitting it as a goal would produce an
//! obligation that no solver could ever be right or wrong about. That fails
//! closed here rather than becoming a vacuous UNKNOWN downstream.

use clean_kernel::{Environment, Expr, TypeChecker};
use trust_types::frontend_firewall::{
    FirewallRejection, FrontendOrigin, FrontendProposal, ProofRole, admit_role,
};

/// Why a frontend proposal did not become a kernel goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrontendAdmissionError {
    /// The firewall refused the role — the proposal was offered as something
    /// the kernel would believe rather than check.
    Refused(FirewallRejection),
    /// The statement does not type as a proposition, so there is nothing to
    /// prove or refute about it.
    NotAProposition {
        /// The kernel's own diagnosis, verbatim.
        detail: String,
    },
}

impl std::fmt::Display for FrontendAdmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Refused(rejection) => write!(f, "{rejection}"),
            Self::NotAProposition { detail } => write!(
                f,
                "frontend firewall: the proposed statement is not a proposition ({detail})"
            ),
        }
    }
}

impl std::error::Error for FrontendAdmissionError {}

/// A frontend statement the kernel has judged well-formed, and which is *not*
/// in any environment.
///
/// The statement is readable (a diagnostic has to show it, a report has to hash
/// it) but there is no constructor that puts it anywhere the kernel would
/// consult it while checking something else.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontendGoal {
    origin: FrontendOrigin,
    statement: Expr,
}

impl FrontendGoal {
    /// Where the statement came from.
    #[must_use]
    pub fn origin(&self) -> &FrontendOrigin {
        &self.origin
    }

    /// The proposition to discharge.
    #[must_use]
    pub fn statement(&self) -> &Expr {
        &self.statement
    }
}

/// Admit a frontend-derived kernel term in `role`.
///
/// The `env` reference is shared, not exclusive, and that is the load-bearing
/// part: this signature is what makes "a frontend term never enters the
/// environment" a property of the type system rather than of a reviewer's
/// attention.
///
/// # Errors
///
/// [`FrontendAdmissionError::Refused`] for any role but [`ProofRole::Goal`];
/// [`FrontendAdmissionError::NotAProposition`] when the statement does not
/// type as a sort.
pub fn kernel_admit(
    env: &Environment,
    proposal: FrontendProposal<Expr>,
    role: ProofRole,
) -> Result<FrontendGoal, FrontendAdmissionError> {
    admit_role(proposal.provenance(), role).map_err(FrontendAdmissionError::Refused)?;
    let goal = proposal.into_goal();
    let origin = goal
        .origin()
        .cloned()
        .expect("a proposal admitted through the firewall carries its frontend origin");
    let statement = goal.into_statement();
    // The inferred universe level is not interesting; that the statement HAS
    // one is — a term that does not live in a sort is not a proposition.
    let _level = TypeChecker::new(env)
        .infer_sort(&statement)
        .map_err(|e| FrontendAdmissionError::NotAProposition { detail: format!("{e:?}") })?;
    Ok(FrontendGoal { origin, statement })
}

/// Discharge a frontend goal by kernel re-check.
///
/// `proof` comes from an authoritative producer — a solver reconstruction, an
/// island theorem, a `Eq.refl` the elaborator constructed. Wherever it came
/// from, the kernel is what decides: this returns `true` only when
/// `check_type` accepts the term against the goal, so a frontend cannot buy
/// belief with a term the kernel rejects.
#[must_use]
pub fn discharge_with_kernel_proof(env: &Environment, goal: &FrontendGoal, proof: &Expr) -> bool {
    TypeChecker::new(env).check_type(proof, goal.statement()).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;
    use clean_kernel::{Declaration, Level};
    use trust_types::frontend_firewall::FrontendLanguage;

    /// `Nat` and a `1 = 1` statement over it, in an environment with the
    /// prelude's `Eq`. Any well-formed proposition would do; this one has a
    /// proof term the kernel accepts and an obvious bogus alternative.
    fn env_and_statement() -> (Environment, Expr, Expr) {
        let env = Environment::with_prelude();
        let nat = Expr::const_(Name::from_string("Nat"), Vec::new());
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), Vec::new()),
            Expr::const_(Name::from_string("Nat.zero"), Vec::new()),
        );
        let eq_levels = vec![Level::succ(Level::zero())];
        let statement = Expr::apps(
            Expr::const_(Name::from_string("Eq"), eq_levels.clone()),
            [nat.clone(), one.clone(), one.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), eq_levels),
            [nat, one],
        );
        (env, statement, proof)
    }

    fn proposal(statement: Expr) -> FrontendProposal<Expr> {
        FrontendProposal::new(
            FrontendOrigin::new(FrontendLanguage::JavaScript, "case.js", "trust-js-autoform"),
            statement,
        )
    }

    #[test]
    fn frontend_term_is_rejected_as_a_hypothesis_at_the_kernel_boundary() {
        let (env, statement, _) = env_and_statement();
        for role in [ProofRole::Hypothesis, ProofRole::Axiom, ProofRole::DefiningEquation] {
            let err = kernel_admit(&env, proposal(statement.clone()), role)
                .expect_err("the kernel boundary must refuse a believed role");
            assert!(
                matches!(
                    err,
                    FrontendAdmissionError::Refused(FirewallRejection::RoleForbidden { .. })
                ),
                "role {role} produced {err}"
            );
        }
    }

    #[test]
    fn admission_as_a_goal_leaves_the_environment_untouched() {
        // The property that matters: a term the frontend proposed is NOT
        // something the kernel will later consult while checking anything else.
        let (env, statement, _) = env_and_statement();
        let before = env.get_const(&Name::from_string("Eq")).is_some();
        let goal = kernel_admit(&env, proposal(statement.clone()), ProofRole::Goal)
            .expect("a goal is the permitted role");
        assert_eq!(goal.statement(), &statement);
        assert_eq!(goal.origin().language, FrontendLanguage::JavaScript);
        // Nothing was added: the proposal's own statement is not reachable as a
        // constant, and the environment is otherwise as it was.
        assert!(env.get_const(&Name::from_string("trust_frontend_case_js")).is_none());
        assert_eq!(env.get_const(&Name::from_string("Eq")).is_some(), before);
    }

    #[test]
    fn a_goal_is_believed_only_when_the_kernel_accepts_a_proof() {
        let (env, statement, proof) = env_and_statement();
        let goal = kernel_admit(&env, proposal(statement), ProofRole::Goal).unwrap();
        assert!(discharge_with_kernel_proof(&env, &goal, &proof));
        // A frontend supplying its own "proof" gets no credit for it.
        let bogus = Expr::const_(Name::from_string("Nat.zero"), Vec::new());
        assert!(!discharge_with_kernel_proof(&env, &goal, &bogus));
    }

    #[test]
    fn a_non_proposition_fails_closed() {
        let env = Environment::with_prelude();
        // `Nat.zero` is a value, not a statement: there is nothing to prove.
        let value = Expr::const_(Name::from_string("Nat.zero"), Vec::new());
        let err = kernel_admit(&env, proposal(value), ProofRole::Goal).unwrap_err();
        assert!(matches!(err, FrontendAdmissionError::NotAProposition { .. }), "{err}");
    }

    #[test]
    fn an_axiom_the_frontend_wants_is_never_minted_even_when_true() {
        // The adversarial case: the statement is TRUE and the frontend asks for
        // it as an axiom to save the proof. Truth is not the question — who gets
        // to assert is.
        let (mut env, statement, proof) = env_and_statement();
        assert!(
            kernel_admit(&env, proposal(statement.clone()), ProofRole::Axiom).is_err(),
            "a true statement is still not a frontend's to assert"
        );
        // The authoritative route stays open, and it goes through the kernel.
        let name = Name::from_string("authoritative_one_eq_one");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: Vec::new(),
            type_: statement,
            value: proof,
        })
        .expect("the kernel accepts an authoritative proof");
        assert!(env.get_const(&name).is_some());
    }
}
