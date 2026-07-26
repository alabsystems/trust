//! WHOLE-ENVIRONMENT AXIOM CENSUS — closes the "silent admission slot" gap.
//!
//! The per-declaration modulo-3 gates (`env.axiom_deps(&name)` residue empty) are the
//! PRIMARY enforcement, but `axiom_deps` FILTERS every name the kernel classifies as
//! foundational (`clean_kernel::env::is_foundational_axiom` — a whitelist that is wider
//! than the 3 foundational axioms: it also contains kernel primitives like the `Quot`
//! quartet / `WellFounded.fix` AND historically-dead entries such as `proofIrrel` /
//! `Eq.refl` / `Char.decEq` / `String.decEq` that are no longer axioms). So a 4th axiom
//! REGISTERED UNDER A WHITELISTED NAME is INVISIBLE to every residue check — a proof
//! referencing it still reports an EMPTY residue and would certify "modulo 3". The
//! `smuggled_dead_whitelist_name_is_invisible_to_residue_but_caught_by_census` control
//! below DEMONSTRATES that hole is real, and this census is the instrument that closes
//! it.
//!
//! The census iterates every constant in an `Environment` and splits the
//! `ConstantKind::Axiom` population in two:
//!
//! * **Hidden slots (HARD FAIL unless allowed):** axiom-kind constants the kernel
//!   classifies as foundational. These are exactly the residue-invisible names. The ONLY
//!   allowed ones are the 3 foundational axioms `{propext, Quot.sound, Classical.choice}`
//!   (the scoring gate — `axioms::FOUNDATIONAL_AXIOMS`), the 4 `Quot` kernel primitives
//!   `{Quot, Quot.mk, Quot.ind, Quot.lift}`, and `WellFounded.fix` (both named "kernel
//!   primitives", TCB item 1 in `docs/TRUST-BASE-AND-SCOPE.md`). Anything else here is a
//!   modulo-3-invisible 4th trust root: TRIAGE, DON'T SUPPRESS.
//! * **Visible domain axioms (reported, inert):** axiom-kind constants the kernel does
//!   NOT classify as foundational (`sorryAx`, `trustedAy`/`trustedArith`, the mathverse
//!   `SetTheory.*` surface, monad/algebra stubs, …). The prelude ships HUNDREDS of these.
//!   They are inert for every certified verdict — any proof whose transitive closure
//!   reaches one gets a NON-EMPTY residue and fails closed — but they are part of the
//!   environment's honest description (see the TCB doc), so the census reports their
//!   count rather than pretending the base env is "3 axioms + Quot".
//!
//! HONEST SCOPE: the census covers the environments it is RUN ON — the base pipeline
//! environment builders AND the derived per-witness-family builders (which EXTEND a
//! base with additional registrations the base census alone would not see; each is
//! censused individually below, not assumed to be a clone). What keeps the in-between
//! honest: the live registration sites across mirsem.rs / trustir_anchor.rs /
//! clean_ground.rs register only `Definition` / `Theorem` / `Opaque` / inductive
//! declarations — never `Declaration::Axiom` (and an `Opaque` is NOT an
//! axiom-equivalent: its hidden value is kernel-type-checked and residue-walked) —
//! and the WITNESS declaration each verdict cites passes the
//! `axiom_deps`-residue-empty gate before anything is `ProvenModulo3` (intermediate
//! registrations are covered by the no-`Declaration::Axiom` discipline + this
//! census, not by per-decl residue gates). The census closes the remaining slot: a
//! whitelisted-NAME axiom the residue gate cannot see.

use clean_kernel::env::{ConstantKind, Environment, is_foundational_axiom};

/// The complete allowed HIDDEN-SLOT census (axiom-kind constants the residue filter
/// cannot see) for every Trust §6 pipeline environment: the 3 foundational axioms + the
/// `Quot` quartet (kernel primitives, TCB item 1). `WellFounded.fix` is deliberately
/// NOT allowed even though the kernel whitelists it: today it is a kernel-checked
/// `Definition`, so a future demotion to axiom-kind would silently open a
/// residue-invisible slot — the census failing on it forces a triage instead.
pub const CENSUS_ALLOWED_HIDDEN: [&str; 7] =
    ["Classical.choice", "Quot.sound", "propext", "Quot", "Quot.ind", "Quot.lift", "Quot.mk"];

/// The whole-environment axiom census result. `hidden_allowed` / `visible_domain` are
/// counts; `hidden_offenders` is the HARD-FAIL set — residue-invisible axiom-kind
/// constants outside [`CENSUS_ALLOWED_HIDDEN`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomCensus {
    /// Residue-invisible axiom-kind constants in the allowed set (≤ 8).
    pub hidden_allowed: usize,
    /// Residue-invisible axiom-kind constants OUTSIDE the allowed set — each one is a
    /// modulo-3-invisible 4th trust root. Sorted. MUST be empty.
    pub hidden_offenders: Vec<String>,
    /// Residue-VISIBLE axiom-kind constants (domain axioms / trust markers the kernel
    /// does not classify as foundational). Inert for certified verdicts — any reference
    /// surfaces in the residue — but reported honestly.
    pub visible_domain: usize,
}

impl AxiomCensus {
    /// Whether the census is sound: no residue-invisible axiom outside the allowed set.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        self.hidden_offenders.is_empty()
    }
}

/// Census every constant in `env`. See the module doc for the two-tier semantics.
#[must_use]
pub fn env_axiom_census(env: &Environment) -> AxiomCensus {
    let mut census =
        AxiomCensus { hidden_allowed: 0, hidden_offenders: Vec::new(), visible_domain: 0 };
    for c in env.constants() {
        if c.kind != ConstantKind::Axiom {
            continue;
        }
        if is_foundational_axiom(&c.name) {
            // Residue-INVISIBLE: `axiom_deps` filters this name, so the modulo-3 gate
            // cannot see it. It must be one of the allowed foundations/primitives.
            let name = c.name.to_string();
            if CENSUS_ALLOWED_HIDDEN.contains(&name.as_str()) {
                census.hidden_allowed += 1;
            } else {
                census.hidden_offenders.push(name);
            }
        } else {
            census.visible_domain += 1;
        }
    }
    census.hidden_offenders.sort();
    census
}

#[cfg(test)]
mod tests {
    use clean_kernel::env::Declaration;
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    use super::*;

    /// `Int.le 0 1` — a small well-typed Prop to hang smuggled axioms on.
    fn zero_le_one() -> Expr {
        let zero = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let one = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ),
        );
        Expr::apps(Expr::const_(Name::from_string("Int.le"), vec![]), [zero, one])
    }

    fn assert_census(label: &str, env: &Environment) {
        let census = env_axiom_census(env);
        eprintln!(
            "  census {label}: hidden-allowed={} visible-domain={} offenders={:?}",
            census.hidden_allowed, census.visible_domain, census.hidden_offenders,
        );
        assert!(
            census.is_sound(),
            "{label}: residue-INVISIBLE axiom-kind constants outside the allowed \
             foundations/primitives: {:?} — each is a modulo-3-invisible 4th trust root; \
             triage, don't suppress",
            census.hidden_offenders,
        );
    }

    /// THE CENSUS — every pipeline environment builder, BASE and DERIVED (the derived
    /// ones EXTEND a base with per-witness-family registrations the base census alone
    /// would not see), carries NO residue-invisible axiom-kind constant outside the 3
    /// foundational axioms + the `Quot` kernel primitives.
    /// The residue-VISIBLE domain-axiom population (mathverse stubs, trust markers) is
    /// reported honestly — it is inert for certified verdicts because any reference
    /// surfaces in the `axiom_deps` residue and fails closed.
    #[test]
    fn pipeline_envs_hidden_axiom_census_is_exactly_the_allowed_set() {
        // Base builders.
        assert_census("trustir_env", &crate::trustir_anchor::trustir_env().expect("trustir_env"));
        assert_census("mirsem_env", &crate::mirsem::mirsem_env().expect("mirsem_env"));
        assert_census(
            "mirsem_safety_env",
            &crate::mirsem::mirsem_safety_env().expect("mirsem_safety_env"),
        );
        assert_census(
            "mirsem_refinement_env",
            &crate::mirsem::mirsem_refinement_env().expect("mirsem_refinement_env"),
        );
        assert_census(
            "mirsem_loop_refinement_env",
            &crate::mirsem::mirsem_loop_refinement_env().expect("mirsem_loop_refinement_env"),
        );
        // Derived builders — each extends a base with additional registrations.
        assert_census(
            "mirsem_branch_refinement_env",
            &crate::mirsem::mirsem_branch_refinement_env().expect("mirsem_branch_refinement_env"),
        );
        assert_census(
            "mirsem_nested_branch_refinement_env",
            &crate::mirsem::mirsem_nested_branch_refinement_env()
                .expect("mirsem_nested_branch_refinement_env"),
        );
        assert_census(
            "loop_instance_env",
            &crate::mirsem::loop_instance_env().expect("loop_instance_env"),
        );
        assert_census(
            "nested_loop_env",
            &crate::mirsem::nested_loop_env().expect("nested_loop_env"),
        );
        assert_census("break_loop_env", &crate::mirsem::break_loop_env().expect("break_loop_env"));
        assert_census(
            "loop_total_correct_instance_env",
            &crate::mirsem::loop_total_correct_instance_env()
                .expect("loop_total_correct_instance_env"),
        );
        assert_census(
            "mirsem_whole_program_env",
            &crate::mirsem::mirsem_whole_program_env().expect("mirsem_whole_program_env"),
        );
        // Lane S — the trust-ir safety-VC adequacy tier's environment.
        assert_census(
            "trustir_safety_env",
            &crate::trustir_safety::trustir_safety_env().expect("trustir_safety_env"),
        );
        // Lane T — the trust-ir ranking/termination theory's environment.
        assert_census(
            "trustir_termination_env",
            &crate::trustir_termination::trustir_termination_env()
                .expect("trustir_termination_env"),
        );
        // The trust-ir CALL denotation's environment (call-spine residue #1 closure):
        // the `Call` inductive + `callResult`/`callCallee` + the proven
        // `callRefinesContract`, on which every per-call `callReturnInstance` lives.
        assert_census(
            "trustir_call_env",
            &crate::trustir_call::trustir_call_env().expect("trustir_call_env"),
        );
    }

    /// THE DISCRIMINATING CONTROL — the hole the census exists to close is REAL: an
    /// axiom registered under a DEAD kernel-whitelist name (`proofIrrel` — no longer a
    /// real axiom in Clean, but still on the foundational whitelist) is INVISIBLE to the
    /// residue gate (a theorem proved BY it reports an EMPTY residue — it would certify
    /// "modulo 3"), while the census CATCHES it. Both halves are asserted.
    #[test]
    fn smuggled_dead_whitelist_name_is_invisible_to_residue_but_caught_by_census() {
        let mut env = crate::trustir_anchor::trustir_env().expect("trustir_env");
        assert!(
            env.get_const(&Name::from_string("proofIrrel")).is_none(),
            "precondition: the pipeline env does not register `proofIrrel` — if this \
             changes, re-derive this control with another dead whitelist name",
        );
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("proofIrrel"),
            level_params: vec![],
            type_: zero_le_one(),
        })
        .expect("registering an axiom under a whitelisted name is legal — that is the hole");
        // A theorem "proved" by the smuggled axiom.
        let thm = Name::from_string("Trust.Census.launderedViaWhitelist");
        env.add_decl(Declaration::Theorem {
            name: thm.clone(),
            level_params: vec![],
            type_: zero_le_one(),
            value: Expr::const_(Name::from_string("proofIrrel"), vec![]),
        })
        .expect("the theorem type-checks — the axiom provides its type");
        // (1) The residue gate CANNOT see it: empty residue despite the 4th axiom.
        let residue = env.axiom_deps(&thm).expect("axiom closure computes");
        assert!(
            residue.is_empty(),
            "expected the whitelist hole (empty residue) — if the kernel now surfaces \
             dead-whitelist axioms, the census is belt-and-suspenders (got {residue:?})",
        );
        // (2) The census DOES see it.
        let census = env_axiom_census(&env);
        assert_eq!(
            census.hidden_offenders,
            vec!["proofIrrel".to_string()],
            "the census must catch the whitelisted-name smuggled axiom",
        );
    }

    /// NEGATIVE CONTROL (residue): a FRESH-name 4th axiom is caught by the PRIMARY
    /// per-decl gate — a theorem whose proof is the smuggled axiom reports it in
    /// `env.axiom_deps`, the exact signal every `check_*` maps to a
    /// non-`ProvenModulo3` verdict (`RefinementVerdict::Residue`). In-tree
    /// discriminating control (previously it lived only in the clean submodule).
    /// The census classifies it as residue-VISIBLE (not a hidden offender).
    #[test]
    fn smuggled_fresh_name_axiom_reaches_the_residue_verdict_path() {
        let mut env = crate::trustir_anchor::trustir_env().expect("trustir_env");
        let baseline = env_axiom_census(&env);
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Trust.Smuggled.bad"),
            level_params: vec![],
            type_: zero_le_one(),
        })
        .expect("register the smuggled axiom");
        let thm = Name::from_string("Trust.Smuggled.laundered");
        env.add_decl(Declaration::Theorem {
            name: thm.clone(),
            level_params: vec![],
            type_: zero_le_one(),
            value: Expr::const_(Name::from_string("Trust.Smuggled.bad"), vec![]),
        })
        .expect("the theorem type-checks — the axiom provides its type");
        let residue = env.axiom_deps(&thm).expect("axiom closure computes");
        assert!(
            residue.iter().any(|n| n.to_string() == "Trust.Smuggled.bad"),
            "the residue MUST name the smuggled axiom (got {residue:?}) — this is the \
             signal every check_* maps to a non-ProvenModulo3 verdict",
        );
        // The census books it as residue-visible (the residue gate covers it), with the
        // hidden-slot tier unchanged.
        let census = env_axiom_census(&env);
        assert_eq!(census.visible_domain, baseline.visible_domain + 1);
        assert_eq!(census.hidden_offenders, baseline.hidden_offenders);
    }
}
