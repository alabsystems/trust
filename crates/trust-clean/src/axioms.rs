// trust-clean/axioms.rs: transitive axiom-closure analysis — the `clean axioms` instrument.
//
// "Modulo 3 axioms" is the success metric for the whole Clean-dependent-types
// program (see docs/PLAN-clean-dependent-type-reflection.md). A proof is
// acceptable iff its transitive axiom closure is a subset of the three
// foundational Clean/Lean kernel axioms:
//
//     { propext, Quot.sound, Classical.choice }
//
// Every other axiom a proof leans on — a trusted `th-lemma.*` step, an unmapped
// solver rule, a `vc_`/`hypothesis_` local, or an unresolved (dangling)
// constant — is RESIDUAL TRUST that the reflection program must drive to zero.
// This module computes that closure over a kernel `ProofTerm` + `KernelContext`
// and reports the residual set. It is the measuring instrument every milestone
// is scored by; the CLI front-end is `src/bin/clean-axioms.rs`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use crate::kernel_check::{ContextEntry, KernelContext, ProofTerm};

// ---------------------------------------------------------------------------
// Foundational axioms
// ---------------------------------------------------------------------------

/// The three foundational axioms of the Clean/Lean kernel.
///
/// These mirror Lean 4's `#print axioms` foundational trio. A proof whose
/// transitive axiom closure is a subset of these — and which references no
/// unresolved constants — is "proven in Clean modulo 3 axioms", the success
/// state of the reflection plan. Note `funext` is intentionally absent: it is a
/// *theorem* derivable from `Quot.sound` + `propext`, not a foundational axiom.
pub const FOUNDATIONAL_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];

/// Returns `true` if `name` is one of the three foundational axioms.
#[must_use]
pub fn is_foundational(name: &str) -> bool {
    FOUNDATIONAL_AXIOMS.contains(&name)
}

// ---------------------------------------------------------------------------
// Axiom report
// ---------------------------------------------------------------------------

/// The result of an axiom-closure walk over a proof term.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AxiomReport {
    /// Every axiom (`ContextEntry::Axiom`) the term transitively depends on,
    /// foundational and residual alike. Sorted and deduplicated.
    pub axioms: BTreeSet<String>,
    /// `Const` names referenced by the proof but absent from the context.
    ///
    /// An unresolved constant is a soundness hole, not a stylistic nit: a proof
    /// that names a constant the kernel cannot resolve has not actually been
    /// checked against that constant's type. It is treated as disqualifying,
    /// exactly like a residual axiom.
    pub unresolved: BTreeSet<String>,
}

impl AxiomReport {
    /// The axioms beyond the foundational three — the residual trust the
    /// reflection program must drive to zero (trusted `th-lemma.*`, unmapped
    /// solver rules, VC-local hypotheses, etc.).
    #[must_use]
    pub fn residual(&self) -> BTreeSet<String> {
        self.axioms.iter().filter(|a| !is_foundational(a)).cloned().collect()
    }

    /// The subset of the foundational three actually used by this proof.
    #[must_use]
    pub fn foundational(&self) -> BTreeSet<String> {
        self.axioms.iter().filter(|a| is_foundational(a)).cloned().collect()
    }

    /// `true` iff the proof stands on at most the three foundational axioms and
    /// references no unresolved constants — i.e. "proven in Clean modulo 3
    /// axioms". This is the green light the whole plan is measured against.
    #[must_use]
    pub fn is_modulo_foundational(&self) -> bool {
        self.residual().is_empty() && self.unresolved.is_empty()
    }
}

/// Raised when a proof's axiom closure exceeds the allowed set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomViolation {
    /// Axioms outside the allowed set.
    pub residual: BTreeSet<String>,
    /// Constants the proof referenced but the kernel context could not resolve.
    pub unresolved: BTreeSet<String>,
}

// ---------------------------------------------------------------------------
// Closure computation
// ---------------------------------------------------------------------------

/// Compute the transitive axiom closure of `term` in `ctx`.
///
/// Walks every sub-term, resolving each `Const`:
/// - an `Axiom` contributes its name, and we recurse into its *type* (which may
///   reference further constants);
/// - a `Definition` is unfolded — we recurse into its type and its value;
/// - an unknown constant is recorded in `unresolved`.
///
/// Visited constants are memoized, so mutually-recursive or self-referential
/// definitions terminate. This mirrors Lean's `#print axioms`: the set of
/// `axiom`-marked declarations a term transitively depends on.
#[must_use]
pub fn axiom_closure(term: &ProofTerm, ctx: &KernelContext) -> AxiomReport {
    let mut report = AxiomReport::default();
    let mut visited: BTreeSet<String> = BTreeSet::new();
    walk(term, ctx, &mut report, &mut visited);
    report
}

fn walk(
    term: &ProofTerm,
    ctx: &KernelContext,
    report: &mut AxiomReport,
    visited: &mut BTreeSet<String>,
) {
    match term {
        ProofTerm::Var(_) | ProofTerm::Sort(_) => {}
        ProofTerm::App(f, a) => {
            walk(f, ctx, report, visited);
            walk(a, ctx, report, visited);
        }
        ProofTerm::Lambda { binder_type, body, .. } => {
            walk(binder_type, ctx, report, visited);
            walk(body, ctx, report, visited);
        }
        ProofTerm::Pi { domain, codomain, .. } => {
            walk(domain, ctx, report, visited);
            walk(codomain, ctx, report, visited);
        }
        ProofTerm::Const(name) => {
            // Memoize before resolving so cyclic definitions terminate.
            if !visited.insert(name.clone()) {
                return;
            }
            match ctx.lookup(name) {
                Some(ContextEntry::Axiom { ty }) => {
                    report.axioms.insert(name.clone());
                    walk(ty, ctx, report, visited);
                }
                Some(ContextEntry::Definition { ty, value }) => {
                    walk(ty, ctx, report, visited);
                    walk(value, ctx, report, visited);
                }
                None => {
                    report.unresolved.insert(name.clone());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Gates
// ---------------------------------------------------------------------------

/// Require that `term`'s axiom closure is a subset of the foundational three
/// (and has no unresolved constants) — the `--require-axioms 3` check.
///
/// # Errors
///
/// Returns [`AxiomViolation`] listing any residual axioms and unresolved
/// constants when the proof leans on more than the foundational three.
pub fn require_foundational(
    term: &ProofTerm,
    ctx: &KernelContext,
) -> Result<AxiomReport, AxiomViolation> {
    let report = axiom_closure(term, ctx);
    if report.is_modulo_foundational() {
        Ok(report)
    } else {
        Err(AxiomViolation { residual: report.residual(), unresolved: report.unresolved.clone() })
    }
}

/// Require that `term`'s axiom closure is a subset of `allowed` (and has no
/// unresolved constants). Generalizes [`require_foundational`] for callers that
/// want to permit a transitional, explicitly-named wider set.
///
/// # Errors
///
/// Returns [`AxiomViolation`] when the closure contains an axiom not in
/// `allowed`, or any unresolved constant.
pub fn require_axioms_subset(
    term: &ProofTerm,
    ctx: &KernelContext,
    allowed: &[&str],
) -> Result<AxiomReport, AxiomViolation> {
    let report = axiom_closure(term, ctx);
    let residual: BTreeSet<String> =
        report.axioms.iter().filter(|a| !allowed.contains(&a.as_str())).cloned().collect();
    if residual.is_empty() && report.unresolved.is_empty() {
        Ok(report)
    } else {
        Err(AxiomViolation { residual, unresolved: report.unresolved.clone() })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn prop() -> ProofTerm {
        ProofTerm::Sort(0)
    }

    fn const_ref(name: &str) -> ProofTerm {
        ProofTerm::Const(name.to_string())
    }

    fn app(f: ProofTerm, a: ProofTerm) -> ProofTerm {
        ProofTerm::App(Box::new(f), Box::new(a))
    }

    // -----------------------------------------------------------------------
    // Foundational-axiom identification
    // -----------------------------------------------------------------------

    #[test]
    fn foundational_set_is_exactly_three() {
        assert_eq!(FOUNDATIONAL_AXIOMS.len(), 3);
        assert!(is_foundational("propext"));
        assert!(is_foundational("Quot.sound"));
        assert!(is_foundational("Classical.choice"));
        // funext is derivable, not foundational.
        assert!(!is_foundational("funext"));
        assert!(!is_foundational("th-lemma.arith_0"));
    }

    // -----------------------------------------------------------------------
    // Closure: trivial terms have no axioms
    // -----------------------------------------------------------------------

    #[test]
    fn sort_and_var_have_empty_closure() {
        let ctx = KernelContext::new();
        let report = axiom_closure(&prop(), &ctx);
        assert!(report.axioms.is_empty());
        assert!(report.unresolved.is_empty());
        assert!(report.is_modulo_foundational());
    }

    // -----------------------------------------------------------------------
    // Closure: a proof leaning only on foundational axioms is clean
    // -----------------------------------------------------------------------

    #[test]
    fn foundational_only_proof_is_clean() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("propext", prop()).unwrap();
        ctx.add_axiom("Quot.sound", prop()).unwrap();
        // term: propext applied to Quot.sound (shape irrelevant to the closure)
        let term = app(const_ref("propext"), const_ref("Quot.sound"));
        let report = axiom_closure(&term, &ctx);
        assert_eq!(report.axioms, ["Quot.sound".to_string(), "propext".to_string()].into());
        assert!(report.residual().is_empty());
        assert!(report.is_modulo_foundational());
    }

    // -----------------------------------------------------------------------
    // Closure: a residual (trusted) axiom is flagged, not clean
    // -----------------------------------------------------------------------

    #[test]
    fn residual_axiom_is_flagged() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("propext", prop()).unwrap();
        ctx.add_axiom("th-lemma.arith_0", prop()).unwrap();
        let term = app(const_ref("propext"), const_ref("th-lemma.arith_0"));
        let report = axiom_closure(&term, &ctx);
        assert_eq!(report.foundational(), ["propext".to_string()].into());
        assert_eq!(report.residual(), ["th-lemma.arith_0".to_string()].into());
        assert!(!report.is_modulo_foundational(), "trusted th-lemma must disqualify the proof");
    }

    // -----------------------------------------------------------------------
    // Closure: transitivity through a definition body
    // -----------------------------------------------------------------------

    #[test]
    fn closure_is_transitive_through_definitions() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("th-lemma.bv_5", prop()).unwrap();
        // def lemma : Prop := th-lemma.bv_5
        ctx.add_definition("lemma", prop(), const_ref("th-lemma.bv_5")).unwrap();
        // The proof only mentions `lemma`, but the axiom must surface transitively.
        let report = axiom_closure(&const_ref("lemma"), &ctx);
        assert_eq!(report.axioms, ["th-lemma.bv_5".to_string()].into());
        assert!(!report.is_modulo_foundational());
    }

    // -----------------------------------------------------------------------
    // Closure: an axiom's *type* contributes too
    // -----------------------------------------------------------------------

    #[test]
    fn axiom_type_dependencies_are_followed() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("Classical.choice", prop()).unwrap();
        // axiom weird : Classical.choice   (type references another axiom)
        ctx.add_axiom("weird", const_ref("Classical.choice")).unwrap();
        let report = axiom_closure(&const_ref("weird"), &ctx);
        assert!(report.axioms.contains("weird"));
        assert!(report.axioms.contains("Classical.choice"));
    }

    // -----------------------------------------------------------------------
    // Closure: unresolved constant is a soundness hole
    // -----------------------------------------------------------------------

    #[test]
    fn unresolved_constant_is_recorded_and_disqualifies() {
        let ctx = KernelContext::new();
        let report = axiom_closure(&const_ref("ghost"), &ctx);
        assert!(report.axioms.is_empty());
        assert_eq!(report.unresolved, ["ghost".to_string()].into());
        assert!(!report.is_modulo_foundational(), "dangling constant is not a checked proof");
    }

    // -----------------------------------------------------------------------
    // Closure: cyclic definitions terminate
    // -----------------------------------------------------------------------

    #[test]
    fn cyclic_definitions_terminate() {
        let mut ctx = KernelContext::new();
        // def a := b ; def b := a  (degenerate, but must not loop)
        ctx.add_definition("a", prop(), const_ref("b")).unwrap();
        ctx.add_definition("b", prop(), const_ref("a")).unwrap();
        let report = axiom_closure(&const_ref("a"), &ctx);
        assert!(report.axioms.is_empty());
        assert!(report.unresolved.is_empty());
    }

    // -----------------------------------------------------------------------
    // Gates
    // -----------------------------------------------------------------------

    #[test]
    fn require_foundational_accepts_clean_and_rejects_residual() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("propext", prop()).unwrap();
        ctx.add_axiom("th-lemma.x", prop()).unwrap();

        let clean = require_foundational(&const_ref("propext"), &ctx);
        assert!(clean.is_ok());

        let dirty = require_foundational(&const_ref("th-lemma.x"), &ctx);
        let err = dirty.expect_err("residual axiom must be rejected");
        assert_eq!(err.residual, ["th-lemma.x".to_string()].into());
    }

    #[test]
    fn require_axioms_subset_permits_named_wider_set() {
        let mut ctx = KernelContext::new();
        ctx.add_axiom("th-lemma.x", prop()).unwrap();
        // Transitionally allow this th-lemma explicitly.
        let ok = require_axioms_subset(&const_ref("th-lemma.x"), &ctx, &["th-lemma.x"]);
        assert!(ok.is_ok());
        // But not a different one.
        let bad = require_axioms_subset(&const_ref("th-lemma.x"), &ctx, &["th-lemma.y"]);
        assert!(bad.is_err());
    }
}
