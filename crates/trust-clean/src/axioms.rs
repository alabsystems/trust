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
// The three are the KERNEL's declarations, never the supplied context's
// (2026-09-28). Before then the closure classified a foundation by NAME, so a
// context declaring `propext : False`, `Quot.sound : False`, or `sorryAx` as a
// Definition read CLEAN. Now a `KernelContext` refuses every kernel-owned name
// (`kernel_check::reserved_declaration_refusal`: no ProofTerm declaration can be
// the canonical one), and a term's undeclared reference to one of the three
// resolves to the kernel's own axiom.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use serde::Deserialize;
use trust_types::fx::FxHashSet;

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
        self.unresolved.is_empty() && self.axioms.iter().all(|a| is_foundational(a))
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
/// - an undeclared foundational name (`propext`, `Quot.sound`,
///   `Classical.choice`) is the KERNEL's canonical axiom and contributes its
///   name. A `KernelContext` can never declare one
///   ([`crate::kernel_check::reserved_declaration_refusal`]), so the name cannot
///   denote anything else; its canonical statement names kernel inductives
///   (`Iff`, `Eq`, `Nonempty`, `Quot`), not context constants, so its type is
///   not walked;
/// - any other unknown constant is recorded in `unresolved`.
///
/// Visited constants are memoized, so mutually-recursive or self-referential
/// definitions terminate. This mirrors Lean's `#print axioms`: the set of
/// `axiom`-marked declarations a term transitively depends on.
#[must_use]
pub fn axiom_closure(term: &ProofTerm, ctx: &KernelContext) -> AxiomReport {
    let mut report = AxiomReport::default();
    let mut visited: FxHashSet<&str> = FxHashSet::default();
    let mut stack: Vec<&ProofTerm> = vec![term];

    while let Some(cur) = stack.pop() {
        match cur {
            ProofTerm::Var(_) | ProofTerm::Sort(_) => {}
            ProofTerm::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            ProofTerm::Lambda { binder_type, body, .. } => {
                stack.push(body);
                stack.push(binder_type);
            }
            ProofTerm::Pi { domain, codomain, .. } => {
                stack.push(codomain);
                stack.push(domain);
            }
            ProofTerm::Const(name) => {
                // Memoize before resolving so cyclic definitions terminate.
                if !visited.insert(name.as_str()) {
                    continue;
                }
                match ctx.lookup(name) {
                    Some(ContextEntry::Axiom { ty }) => {
                        report.axioms.insert(name.clone());
                        stack.push(ty);
                    }
                    Some(ContextEntry::Definition { ty, value }) => {
                        stack.push(value);
                        stack.push(ty);
                    }
                    None if is_foundational(name) => {
                        report.axioms.insert(name.clone());
                    }
                    None => {
                        report.unresolved.insert(name.clone());
                    }
                }
            }
        }
    }

    report
}

// ---------------------------------------------------------------------------
// Supplied obligations (the `clean-axioms` input)
// ---------------------------------------------------------------------------

/// One named entry of a supplied kernel context.
#[derive(Debug, Clone, Deserialize)]
pub struct SuppliedContextEntry {
    /// The constant's name.
    pub name: String,
    /// Its declaration.
    pub entry: ContextEntry,
}

/// A proof obligation to audit: a proof term plus the context it is checked
/// in — the `clean-axioms` input format.
#[derive(Debug, Clone, Deserialize)]
pub struct SuppliedObligation {
    /// The proof term.
    pub term: ProofTerm,
    /// The context, in declaration order.
    #[serde(default)]
    pub context: Vec<SuppliedContextEntry>,
}

/// Build the `KernelContext` a supplied obligation declares, or REFUSE it.
///
/// Every entry goes through [`KernelContext::add_axiom`] /
/// [`KernelContext::add_definition`], which refuse a duplicate and every
/// kernel-owned name — a foundation redeclared (in this term language never
/// canonically) or a trust marker in any kind. A refused context has no
/// closure to report: it is not NOT-CLEAN, it is not an input the instrument
/// can judge.
///
/// # Errors
///
/// A message naming the first refused entry and why.
pub fn build_supplied_context(entries: Vec<SuppliedContextEntry>) -> Result<KernelContext, String> {
    let mut ctx = KernelContext::new();
    for e in entries {
        let res = match e.entry {
            ContextEntry::Axiom { ty } => ctx.add_axiom(&e.name, ty),
            ContextEntry::Definition { ty, value } => ctx.add_definition(&e.name, ty, value),
        };
        res.map_err(|err| format!("context REFUSED at entry '{}': {err}", e.name))?;
    }
    Ok(ctx)
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
        let residual = report.residual();
        Err(AxiomViolation { residual, unresolved: report.unresolved })
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
        Err(AxiomViolation { residual, unresolved: report.unresolved })
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
        // The foundations are the kernel's: the context declares neither.
        let ctx = KernelContext::new();
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
        // axiom P : Prop ; axiom weird : P   (the type references another axiom)
        ctx.add_axiom("P", prop()).unwrap();
        ctx.add_axiom("weird", const_ref("P")).unwrap();
        let report = axiom_closure(&const_ref("weird"), &ctx);
        assert_eq!(report.axioms, ["P".to_string(), "weird".to_string()].into());
        // Since 2026-09-29 an axiom's type must be a well-formed type over the
        // entries before it (`kernel_check::axiom_refusal`). This test used to
        // declare `weird : Classical.choice`: a foundation is never a context
        // entry, so that type is unknown to the kernel (and a proof, not a
        // type) and is refused — as a definition over a foundation already was.
        let err = ctx.add_axiom("weirder", const_ref("Classical.choice")).unwrap_err();
        assert!(err.to_string().contains("unknown constant: Classical.choice"), "{err}");
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
    fn cyclic_or_self_referential_definitions_cannot_enter_a_context() {
        // Before 2026-09-29 `def a := b ; def b := a` was accepted (the walk's
        // memo only kept it from looping) and read CLEAN — a proof term of any
        // type, resting on nothing. Each definition is now kernel-checked
        // against the entries BEFORE it, so neither a cycle nor `x := x` can
        // be built.
        let mut ctx = KernelContext::new();
        let err =
            ctx.add_definition("a", prop(), const_ref("b")).expect_err("`b` is not declared yet");
        assert!(err.to_string().contains("unknown constant: b"), "{err}");
        let err = ctx.add_definition("x", prop(), const_ref("x")).expect_err("self-reference");
        assert!(err.to_string().contains("refers to itself"), "{err}");
        assert!(ctx.is_empty(), "a refused definition leaves no entry behind");
        // The walk's memo still terminates on a (well-typed) diamond.
        ctx.add_axiom("P", prop()).unwrap();
        ctx.add_definition("q", prop(), const_ref("P")).unwrap();
        ctx.add_definition("r", prop(), const_ref("q")).unwrap();
        let report = axiom_closure(&app(const_ref("r"), const_ref("q")), &ctx);
        assert_eq!(report.axioms, ["P".to_string()].into());
        assert!(report.unresolved.is_empty());
    }

    // -----------------------------------------------------------------------
    // Gates
    // -----------------------------------------------------------------------

    #[test]
    fn require_foundational_accepts_clean_and_rejects_residual() {
        let mut ctx = KernelContext::new();
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

    // -----------------------------------------------------------------------
    // Supplied contexts (2026-09-28): the instrument no longer trusts a
    // context's NAMES. Fixtures: `fixtures/clean-axioms/` (the clean-sorry
    // reviewer's `ax*_` inputs verbatim, plus trust-marker and control cases).
    // -----------------------------------------------------------------------

    fn supplied(json: &str) -> SuppliedObligation {
        serde_json::from_str(json).expect("fixture parses as a clean-axioms obligation")
    }

    macro_rules! fixture {
        ($name:literal) => {
            supplied(include_str!(concat!("../fixtures/clean-axioms/", $name, ".json")))
        };
    }

    /// Before the fix each of these read CLEAN: the context's `False` is a
    /// Definition (so it is not an axiom), and the only axiom in the closure is
    /// a counterfeit carrying a foundational NAME. Now the context is REFUSED
    /// at the counterfeit's entry.
    #[test]
    fn supplied_fixture_counterfeit_foundation_is_refused() {
        for (obligation, entry) in [
            (fixture!("ax2_propext_false"), "propext"),
            (fixture!("ax2_quotsound_alias"), "Quot.sound"),
            (fixture!("ax_propext_false"), "propext"),
            (fixture!("ax_quotsound_alias"), "Quot.sound"),
            (fixture!("choice_definition"), "Classical.choice"),
        ] {
            let err = build_supplied_context(obligation.context)
                .expect_err(&format!("a context redeclaring `{entry}` must be refused"));
            assert!(err.contains("context REFUSED"), "{err}");
            assert!(err.contains(&format!("entry '{entry}'")), "{err}");
            assert!(err.contains("kernel-owned foundation"), "{err}");
        }
    }

    /// A trust marker is refused by name in ANY declaration kind.
    #[test]
    fn supplied_fixture_trust_marker_is_refused_in_any_kind() {
        for (obligation, entry, kind) in [
            (fixture!("sorryax_definition"), "sorryAx", "a Definition"),
            (fixture!("trustedAy_axiom"), "trustedAy", "an Axiom"),
        ] {
            let err = build_supplied_context(obligation.context)
                .expect_err(&format!("a context declaring `{entry}` must be refused"));
            assert!(err.contains(&format!("entry '{entry}'")), "{err}");
            assert!(err.contains("trust marker") && err.contains(kind), "{err}");
        }
    }

    /// Control: `proofIrrel` is NOT kernel-owned (proof irrelevance is a
    /// definitional rule, not an axiom), so the reviewer's `ax_proofirrel`
    /// context builds — and reads NOT CLEAN, with both axioms residual.
    #[test]
    fn supplied_fixture_non_kernel_axiom_is_residual_not_refused() {
        let obligation = fixture!("ax_proofirrel");
        let ctx = build_supplied_context(obligation.context).expect("no kernel-owned name");
        let report = axiom_closure(&obligation.term, &ctx);
        assert_eq!(report.residual(), ["False".to_string(), "proofIrrel".to_string()].into());
        assert!(!report.is_modulo_foundational());
    }

    /// Control: the three foundations referenced WITHOUT a declaration are the
    /// kernel's own axioms — CLEAN, all three reported as used.
    #[test]
    fn supplied_fixture_undeclared_foundations_are_the_kernels() {
        let obligation = fixture!("kernel_foundations_undeclared");
        let ctx = build_supplied_context(obligation.context).expect("empty context");
        let report = require_foundational(&obligation.term, &ctx).expect("CLEAN");
        assert_eq!(report.foundational(), FOUNDATIONAL_AXIOMS.map(String::from).into());
        assert!(report.unresolved.is_empty());
    }

    /// The second route (cb/track-b review, 2026-09-28): a context DEFINITION
    /// was never type-checked, so `mySorry : False := Sort 0` under a name no
    /// reserved list knows, or `x : Prop := x`, read CLEAN. Each is now refused
    /// at its entry, naming why; so are a cycle and a top-universe value.
    #[test]
    fn supplied_fixture_unchecked_definitions_are_refused() {
        for (obligation, entry, why) in [
            (fixture!("def_ill_typed_mysorry"), "mySorry", "not its declared type"),
            (fixture!("def_self_reference"), "x", "refers to itself"),
            (fixture!("def_cycle"), "a", "unknown constant: b"),
            (fixture!("def_universe_overflow"), "bad", "universe level overflow"),
        ] {
            let err = build_supplied_context(obligation.context)
                .expect_err(&format!("an unchecked `{entry}` must refuse the context"));
            assert!(err.contains("context REFUSED"), "{err}");
            assert!(err.contains(&format!("entry '{entry}'")), "{err}");
            assert!(err.contains(why), "{entry}: {err}");
        }
    }

    /// Controls: well-typed definitions still build — a definitions-only chain
    /// reads CLEAN; one over declared axioms reads NOT CLEAN (they are residual).
    #[test]
    fn supplied_fixture_well_typed_definitions_build() {
        let obligation = fixture!("def_clean_chain");
        let ctx = build_supplied_context(obligation.context).expect("well-typed");
        let report = require_foundational(&obligation.term, &ctx).expect("CLEAN");
        assert!(report.axioms.is_empty());
        let obligation = fixture!("def_well_typed_chain");
        let ctx = build_supplied_context(obligation.context).expect("well-typed");
        let report = axiom_closure(&obligation.term, &ctx);
        assert_eq!(report.residual(), ["P".to_string(), "p".to_string()].into());
        assert!(!report.is_modulo_foundational());
    }

    /// de Bruijn (2026-09-29, the cb/track-b round-2 reviewer's `rvB2/ax`
    /// probes): the kernel returned a local's type without lifting it past the
    /// binders bound after it. Each REFUSED fixture read `CLEAN ✓` before: the
    /// value types (under the unlifted lookup) as the declared type, a
    /// proposition that holds of nothing (`∀Q:Prop, Q`; `∀Q R:Prop, R`) —
    /// or, for `debruijn_dep_confuse`, `P a → Q b`, whose declared type the
    /// same bug could not even form. `debruijn_open_axiom` is the `Const` rule's
    /// side of it: a context type is returned unshifted, so it must be closed.
    #[test]
    fn supplied_fixture_de_bruijn_attacks_are_refused() {
        for (obligation, entry, why) in [
            (fixture!("debruijn_shift_false"), "K", "not its declared type"),
            (fixture!("debruijn_shift_false_inline"), "bad", "not its declared type"),
            (fixture!("debruijn_shift_false_deep"), "bad", "not its declared type"),
            (fixture!("debruijn_dep_confuse"), "confuse", "not its declared type"),
            (fixture!("debruijn_open_axiom"), "ax", "declared type of axiom `ax`"),
        ] {
            let err = build_supplied_context(obligation.context)
                .expect_err(&format!("`{entry}` must refuse the context"));
            assert!(err.contains("context REFUSED"), "{err}");
            assert!(err.contains(&format!("entry '{entry}'")), "{err}");
            assert!(err.contains(why), "{entry}: {err}");
        }
    }

    /// The controls the same bug REFUSED: each definition at its true type,
    /// over nested and dependent binders, builds and reads CLEAN (no axioms).
    #[test]
    fn supplied_fixture_de_bruijn_true_types_build() {
        for (name, obligation) in [
            ("debruijn_poly_id", fixture!("debruijn_poly_id")),
            ("debruijn_k_true_type", fixture!("debruijn_k_true_type")),
            ("debruijn_compose", fixture!("debruijn_compose")),
            ("debruijn_dep_hyp", fixture!("debruijn_dep_hyp")),
        ] {
            let ctx = build_supplied_context(obligation.context)
                .unwrap_or_else(|e| panic!("{name} is well-typed: {e}"));
            let report = require_foundational(&obligation.term, &ctx).expect("CLEAN");
            assert!(report.axioms.is_empty(), "{name}");
        }
    }

    /// Control: an undeclared trust marker is NOT the kernel's to vouch for —
    /// it stays unresolved, and the report is NOT CLEAN.
    #[test]
    fn supplied_fixture_undeclared_trust_marker_is_unresolved() {
        let obligation = fixture!("sorryax_undeclared");
        let ctx = build_supplied_context(obligation.context).expect("empty context");
        let report = axiom_closure(&obligation.term, &ctx);
        assert_eq!(report.unresolved, ["sorryAx".to_string()].into());
        assert!(!report.is_modulo_foundational());
    }

    /// Only the three resolve without a declaration: an undeclared quotient
    /// primitive is still a dangling constant.
    #[test]
    fn only_the_three_foundations_resolve_undeclared() {
        let ctx = KernelContext::new();
        let report = axiom_closure(&app(const_ref("Quot.mk"), const_ref("Quot.lift")), &ctx);
        assert_eq!(report.unresolved, ["Quot.lift".to_string(), "Quot.mk".to_string()].into());
        assert!(report.axioms.is_empty());
        assert!(!report.is_modulo_foundational());
    }
}
