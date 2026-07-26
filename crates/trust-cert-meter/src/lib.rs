// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! The ONE honesty meter (review R2, `docs/design-review-2026-07-06.md`).
//!
//! Before this crate, 31 of 36 spikes carried private copies of the certification gate,
//! and most checked `axiom closure == ∅` — stricter than, and different from, the design:
//!
//! > Certified ⟺ the strict root judgment and complete reachable declaration
//! > closure pass Clean's kernel/provenance audit; only the exact canonical
//! > {propext, Quot.sound, Classical.choice} foundations are admitted, with
//! > sorry/trusted* always in the meter.
//! >   — design-trust-spec-language.md §8 (mirroring §3 L5)
//!
//! This crate is that sentence, once, with meta-tests. Trust markers (`sorry`,
//! `trusted*`) are always fatal to Certified; the three foundational axioms are not.

use clean_kernel::{CertificationIssue, Environment, Expr};

/// The design's foundational names, retained as a reporting compatibility
/// surface. Names alone confer no authority: `Environment::audit_certification`
/// verifies each foundation's exact canonical kind, arity, and statement.
pub const FOUNDATIONAL_AXIOMS: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// The grade of a (goal, term) pair under the design's §6/§8 meter.
///
/// `SolverValidated` and `Pending` are states of an *obligation* (no term yet), so they
/// are out of scope here: this meter grades terms. `Certified-auto` vs `Certified` is a
/// routing distinction (how the term was produced), not a gate distinction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Grade {
    /// `check_type` rejected the term (or registration failed).
    Rejected { error: String },
    /// The strict root judgment succeeds, but the canonical audit reaches
    /// trust markers or non-foundational axioms. The offending names are
    /// listed, sorted, deduplicated.
    Trusted { closure: Vec<String> },
    /// The Clean term/goal pair passes the complete strict certification
    /// audit. This is only a term grade: consumers must separately bind the
    /// exact goal and term to the canonical typed TrustIR obligation before it
    /// can affect a Rust VC result or license any check elision.
    Certified,
}

impl Grade {
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self, Grade::Certified)
    }
}

/// Grade `term` against `goal` through Clean's read-only strict certification
/// audit. The audit checks the root judgment and the complete reachable
/// type/value/provenance graph without cloning the environment or registering
/// a collision-prone synthetic theorem.
#[must_use]
pub fn grade(env: &Environment, goal: &Expr, term: &Expr) -> Grade {
    let audit = env.audit_certification(goal, term);
    if audit.is_certified() {
        return Grade::Certified;
    }

    // Only genuine named assumptions/trust markers map to Trusted. Every
    // authority/provenance/integrity failure is Rejected; in particular,
    // structural/unchecked/recheck-needed declarations and forged foundation
    // names can never be softened into a lower positive grade.
    let mut closure = Vec::new();
    for issue in &audit.issues {
        match issue {
            CertificationIssue::NonFoundationalAxiom { name }
            | CertificationIssue::TrustMarker { name } => closure.push(name.to_string()),
            _ => {
                return Grade::Rejected {
                    error: format!("strict certification audit failed: {:?}", audit.issues),
                };
            }
        }
    }
    closure.sort();
    closure.dedup();
    Grade::Trusted { closure }
}

#[cfg(test)]
mod tests {
    use clean_kernel::expr::BinderInfo;
    use clean_kernel::{Declaration, Level, Name, TypeChecker};

    use super::*;

    fn c(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), vec![])
    }
    fn nat() -> Expr {
        c("Nat")
    }
    fn eq_nat(a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]), [nat(), a, b])
    }
    fn refl(x: Expr) -> Expr {
        Expr::apps(Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]), [nat(), x])
    }
    fn true_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("initialize True/False");
        env
    }

    /// ∀ x:Nat, x = x  via λ x. Eq.refl x — pure, foundational-free → Certified.
    #[test]
    fn clean_proof_is_certified() {
        let env = Environment::with_prelude();
        let goal = Expr::pi(BinderInfo::Default, nat(), eq_nat(Expr::bvar(0), Expr::bvar(0)));
        let term = Expr::lam(BinderInfo::Default, nat(), refl(Expr::bvar(0)));
        assert_eq!(grade(&env, &goal, &term), Grade::Certified);
    }

    /// A `sorry`-filled goal must NEVER be Certified — markers are always fatal.
    #[test]
    fn sorry_is_trusted_not_certified() {
        let env = Environment::with_prelude();
        let goal = eq_nat(Expr::nat_lit(1), Expr::nat_lit(1));
        let term = Expr::app(Expr::const_str_levels("sorry", vec![Level::zero()]), goal.clone());
        let g = grade(&env, &goal, &term);
        match g {
            Grade::Trusted { closure } => assert!(
                closure.iter().any(|n| n.contains("sorry")),
                "closure must name sorry, got {closure:?}"
            ),
            other => panic!("sorry must grade Trusted, got {other:?}"),
        }
    }

    /// Foundation identity is owned by the kernel's canonical statement/kind
    /// checker, not by this crate's string list alone.
    #[test]
    fn foundational_names_match_kernel_registry() {
        for name in FOUNDATIONAL_AXIOMS {
            assert!(clean_kernel::is_foundational_axiom(&Name::from_string(name)));
        }
    }

    /// A foundation-shaped name is not authority. The declaration must
    /// exactly match the canonical declaration installed by Clean.
    #[test]
    fn foundational_name_spoof_is_rejected() {
        let mut env = true_env();
        let goal = c("True");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("propext"),
            level_params: vec![],
            type_: goal.clone(),
        })
        .expect("declare well-formed foundation-name spoof");

        let Grade::Rejected { error } = grade(&env, &goal, &c("propext")) else {
            panic!("a foundation-name spoof must be Rejected");
        };
        assert!(error.contains("NonCanonicalFoundation"), "error: {error}");
    }

    /// A DOMAIN axiom (same shape, non-foundational name) caps at Trusted.
    #[test]
    fn domain_axiom_caps_at_trusted() {
        let mut env = Environment::with_prelude();
        let goal_prop = eq_nat(Expr::nat_lit(3), Expr::nat_lit(3));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("nia_sound"),
            level_params: vec![],
            type_: goal_prop.clone(),
        })
        .expect("declare nia_sound");
        assert_eq!(
            grade(&env, &goal_prop, &c("nia_sound")),
            Grade::Trusted { closure: vec!["nia_sound".to_string()] }
        );
    }

    /// An ill-typed term is Rejected.
    #[test]
    fn ill_typed_is_rejected() {
        let env = Environment::with_prelude();
        let goal = eq_nat(Expr::nat_lit(1), Expr::nat_lit(2));
        let term = refl(Expr::nat_lit(1)); // proves 1=1, not 1=2
        assert!(matches!(grade(&env, &goal, &term), Grade::Rejected { .. }));
    }

    #[test]
    fn structural_only_proof_is_rejected_not_trusted() {
        let mut env = Environment::with_prelude();
        let goal = eq_nat(Expr::nat_lit(4), Expr::nat_lit(4));
        let name = Name::from_string("structural_proof");
        env.add_decl_structural(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: goal.clone(),
            value: refl(Expr::nat_lit(4)),
        })
        .expect("structural fixture");
        assert!(TypeChecker::new(&env).check_type(&c("structural_proof"), &goal).is_ok());
        assert!(matches!(grade(&env, &goal, &c("structural_proof")), Grade::Rejected { .. }));
    }

    #[test]
    fn user_declaration_named_like_legacy_synthetic_meter_cannot_collide() {
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("__cert_meter__"),
            level_params: vec![],
            type_: nat(),
            value: Expr::nat_lit(0),
            is_reducible: true,
        })
        .expect("the user-owned legacy name is valid");

        let goal = eq_nat(Expr::nat_lit(5), Expr::nat_lit(5));
        assert_eq!(grade(&env, &goal, &refl(Expr::nat_lit(5))), Grade::Certified);
        assert!(env.get_const(&Name::from_string("__cert_meter__")).is_some());
    }
}
