// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The multi-axis grade record — capabilities as evidence, not a single badge.
//!
//! The two-language spec-surface design (§7, R-U) replaces the single
//! total-order [`AssuranceLevel`] with a **product of independent axes**:
//! proof validation × axiom closure × coverage bound × executability ×
//! reflection tier. `Certified` stops being an enum variant and becomes the
//! *composite name* for "kernel-rechecked ∧ no non-foundational axiom closure"
//! ([`GradeRecord::is_certified`]).
//!
//! Two normative rules ride along from the design:
//!
//! 1. **No legacy verdict may gain standing in translation** (§7 schema
//!    note). [`GradeRecord::from_legacy`] fills the axes the legacy enum
//!    never recorded with explicit `Unrecorded`/`Unlinked` values — never
//!    with claims. The round-trip [`GradeRecord::to_legacy`] ∘
//!    [`GradeRecord::from_legacy`] is the identity (pinned by tests), which
//!    is what "lossless" means here.
//! 2. **Optimizations never inspect a grade string** (review P4, adopted).
//!    UB-check elision requires `Certified` on BOTH the obligation and its
//!    reflection tier, and is minted as a kernel capability for a specific
//!    site — this record is *evidence bookkeeping*, deliberately exposing no
//!    `licenses_ub_elision()` helper.
//!
//! The compatibility [`crate::ProofEvidence::grade`] and
//! [`crate::ProofStrength::grade`] views are consumed at the authoritative
//! human-report boundary (`trust-report` terminal/text/HTML rendering), where
//! all five axes are displayed. The stable JSON verdict schema remains legacy
//! compatible; rendering a derived grade never participates in verdict,
//! publication, cache, or code-generation decisions.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::result::AssuranceLevel;

/// Axis 1 — what kind of validation stands behind the verdict.
///
/// This is the *kind* of evidence; numeric bounds live on the
/// [`CoverageBound`] axis so that "bounded to depth N" is not conflated with
/// "how the bounded exploration was validated".
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofValidation {
    /// A proof term was independently reconstructed and re-checked by the
    /// Clean CIC kernel. (Legacy `Certified`.)
    KernelRechecked,
    /// The solver's proof was accepted by an SMT-level strict proof checker
    /// (defense-in-depth, trusted code, below kernel recheck). (Legacy
    /// `SmtBacked`.)
    SolverValidated,
    /// Sound by construction or independently validated complete analysis,
    /// without a kernel-checked term (e.g. a sound abstract-interpretation
    /// verdict). (Legacy `Sound`.)
    SoundAnalysis,
    /// A bare solver verdict accepted inside the trusted TCB — standing rests
    /// on trusting the engine. (Legacy `Trusted`.)
    TrustedVerdict,
    /// Exhaustive exploration up to an explicit bound; no violation found
    /// within it. Pair with [`CoverageBound::UnwindBounded`]. (Legacy
    /// `BoundedSound`.)
    BoundedExploration,
    /// Exhaustive check of a finite model instance; pair with
    /// [`CoverageBound::ModelBounded`]. (The `Finite-Model-Checked(M)` grade
    /// of the design; no legacy equivalent — legacy collapsed it into
    /// `BoundedSound`/`Trusted`.)
    FiniteModelCheck,
    /// Best-effort / heuristic evidence — no formal guarantee. (Legacy
    /// `Heuristic`.)
    HeuristicOnly,
    /// The engine claimed a verdict but nothing validated it. (Legacy
    /// `Unchecked`.)
    Unvalidated,
    /// No verification evidence yet (queued, skipped, or unattempted). (No
    /// legacy equivalent — legacy encoded absence out-of-band.)
    Pending,
}

/// Axis 2 — the axiom closure the verdict depends on.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AxiomClosure {
    /// Proven from the kernel's axiom floor alone — nothing assumed.
    Empty,
    /// Named assumptions in the closure: every `assume`, Clean `axiom`,
    /// `sorry`-hole ancestor, or wrapper axiom, by stable name. Dependent
    /// grades are capped at trusted standing with the axioms named (E8).
    Named(BTreeSet<String>),
    /// The producing pipeline did not record closure information. Distinct
    /// from [`AxiomClosure::Empty`] — an import must never gain "empty
    /// closure" standing by omission.
    Unrecorded,
}

/// Axis 3 — how much of the input/behavior space the evidence covers.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CoverageBound {
    /// All inputs / unbounded behavior.
    Unbounded,
    /// Bounded exploration (loop unwinding / path depth) up to `depth`.
    UnwindBounded { depth: u64 },
    /// A finite model instance of size `size` (e.g. a temporal model with a
    /// concrete instance bound).
    ModelBounded { size: u64 },
    /// The producing pipeline did not record a coverage bound.
    Unrecorded,
}

/// Axis 4 — whether the clause carries certified runtime evidence (§1.1: a
/// kernel-certified decision procedure `monitor(args, out) = true ↔ P`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Executability {
    /// A certified monitor exists; `targo trust test` installs it, and checks
    /// it only when the associated clause is reached by a selected test.
    Monitored,
    /// A certified E5 scalar evaluator exists; authenticated test artifacts
    /// combine it with exact loop/recursion transition provenance to check
    /// strict descent when the measured edge is reached.
    Measured,
    /// No certified monitor — the clause's only evidence lanes are static.
    /// Never approximated by code that returns `true`.
    Unmonitored,
    /// The producing pipeline did not record monitor status.
    Unrecorded,
}

/// Axis 5 — which reflection fragment links the discharged obligation to the
/// program's actual semantics (§9: a proof of the generated VC alone is not a
/// proof about program behavior).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReflectionTier {
    /// The obligation ↔ semantics link is covered by the numbered reflection
    /// fragment (Fragment-1 today; the number is the fragment id, not a
    /// quality score).
    Fragment(u16),
    /// No reflection coverage — the verdict is about the VC, not yet about
    /// the compiled program. Fails the UB-elision gate by construction.
    Unlinked,
    /// The producing pipeline did not record reflection information.
    Unrecorded,
}

/// The §7 grade record: a product of independent evidence axes, replacing the
/// single [`AssuranceLevel`] ladder. See the module docs for the two
/// normative rules (lossless legacy mapping; no grade-string-driven
/// optimization).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GradeRecord {
    /// What kind of validation stands behind the verdict.
    pub validation: ProofValidation,
    /// The axiom closure the verdict depends on.
    pub axiom_closure: AxiomClosure,
    /// How much of the input/behavior space the evidence covers.
    pub coverage: CoverageBound,
    /// Certified-monitor status of the clause (§1.1).
    pub executability: Executability,
    /// Reflection fragment linking the obligation to program semantics (§9).
    pub reflection: ReflectionTier,
}

impl GradeRecord {
    /// `Certified` as the design defines it: kernel-rechecked with an empty
    /// axiom closure (§7). A composite predicate — deliberately not an enum
    /// variant, so nothing can stamp it without both axes actually holding.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.validation, ProofValidation::KernelRechecked)
            && matches!(self.axiom_closure, AxiomClosure::Empty)
    }

    /// Attach the independently transported certified-monitor disposition to
    /// this static-evidence grade.
    ///
    /// The executability axis is orthogonal to proof validation: a statically
    /// proved clause may be unmonitored, and a clause with a certified monitor
    /// may still have an open static obligation.  Keeping this as an explicit
    /// refinement prevents report code from inferring runtime coverage from a
    /// proof strength (or vice versa).
    #[must_use]
    pub fn with_monitor_evidence(
        mut self,
        monitor: Option<&crate::result::TransportMonitorEvidence>,
    ) -> Self {
        self.executability =
            monitor.map_or(Executability::Unrecorded, |monitor| monitor.status.executability());
        self
    }

    /// Lossless import of a legacy [`AssuranceLevel`]. Axes the legacy enum
    /// never carried are filled with `Unrecorded`/`Unlinked` — never with
    /// claims (§7: "no legacy verdict may gain standing in translation").
    ///
    /// The one deliberate exception: legacy `Certified` maps to an **empty**
    /// axiom closure, because that is the legacy variant's documented meaning
    /// ("clean kernel independently verified" — the kernel lane never stamps
    /// `Certified` over an assumption; assumptions were `Trusted`). The
    /// round-trip back to legacy is the identity either way.
    #[must_use]
    pub fn from_legacy(level: &AssuranceLevel) -> Self {
        let (validation, coverage) = match level {
            AssuranceLevel::Sound => (ProofValidation::SoundAnalysis, CoverageBound::Unbounded),
            AssuranceLevel::BoundedSound { depth } => (
                ProofValidation::BoundedExploration,
                CoverageBound::UnwindBounded { depth: *depth },
            ),
            AssuranceLevel::Heuristic => {
                (ProofValidation::HeuristicOnly, CoverageBound::Unrecorded)
            }
            AssuranceLevel::Unchecked => (ProofValidation::Unvalidated, CoverageBound::Unrecorded),
            AssuranceLevel::Trusted => (ProofValidation::TrustedVerdict, CoverageBound::Unrecorded),
            AssuranceLevel::SmtBacked => {
                (ProofValidation::SolverValidated, CoverageBound::Unrecorded)
            }
            AssuranceLevel::Certified => {
                (ProofValidation::KernelRechecked, CoverageBound::Unbounded)
            }
        };
        let axiom_closure = match level {
            AssuranceLevel::Certified => AxiomClosure::Empty,
            _ => AxiomClosure::Unrecorded,
        };
        Self {
            validation,
            axiom_closure,
            coverage,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// Lossless import of a legacy `(reasoning, assurance)` evidence pair
    /// ([`crate::ProofEvidence`] / [`crate::ProofStrength`]).
    ///
    /// The assurance level drives every axis exactly as [`Self::from_legacy`];
    /// the reasoning kind may then refine **only the coverage axis** — a
    /// bounded technique (BMC, symbolic execution, neural bounding) records
    /// its bound honestly even where the legacy level lost it (e.g. a `Sound`
    /// verdict stamped by a bounded engine). Refinement never touches the
    /// validation or closure axes, so standing cannot change and the
    /// legacy projection is unaffected.
    #[must_use]
    pub fn from_legacy_evidence(
        reasoning: &crate::result::ReasoningKind,
        assurance: &AssuranceLevel,
    ) -> Self {
        let mut record = Self::from_legacy(assurance);
        if let crate::result::ReasoningKind::BoundedModelCheck { depth } = reasoning {
            if matches!(record.coverage, CoverageBound::Unrecorded | CoverageBound::Unbounded) {
                record.coverage = CoverageBound::UnwindBounded { depth: *depth };
            }
        }
        record
    }

    // ---- R-U Phase C: named constructors (§7) --------------------------
    //
    // These are the grade-native minting API that call sites migrate ONTO,
    // replacing ad-hoc `AssuranceLevel::` construction. Each is defined so
    // that `.to_legacy()` projects to exactly the legacy level it names — the
    // `named_constructor_projects_to_its_legacy_level` test pins this — so a
    // mechanical migration is verdict-identical by construction. Axes the
    // named level does not speak to stay `Unrecorded`/`Unlinked`, never a
    // claim.

    /// Kernel-rechecked with no non-foundational assumptions — represented by
    /// [`AxiomClosure::Empty`] after validator-owned canonical foundations are
    /// excluded. This is the only constructor that yields `is_certified()`.
    /// Projects to `Certified`.
    #[must_use]
    pub fn kernel_certified() -> Self {
        Self {
            validation: ProofValidation::KernelRechecked,
            axiom_closure: AxiomClosure::Empty,
            coverage: CoverageBound::Unbounded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// Kernel-rechecked but resting on a named assumption closure (E8). A real
    /// proof, but not `Certified`. Projects to `Trusted`.
    #[must_use]
    pub fn kernel_trusted(axioms: impl IntoIterator<Item = String>) -> Self {
        Self {
            validation: ProofValidation::KernelRechecked,
            axiom_closure: AxiomClosure::Named(axioms.into_iter().collect()),
            coverage: CoverageBound::Unrecorded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// Discharged by a solver whose UNSAT result was not independently
    /// kernel-rechecked. Projects to `SmtBacked`.
    #[must_use]
    pub fn smt_backed() -> Self {
        Self {
            validation: ProofValidation::SolverValidated,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::Unrecorded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// A sound static analysis over the unbounded input space (no solver
    /// certificate). Projects to `Sound`.
    #[must_use]
    pub fn sound_analysis() -> Self {
        Self {
            validation: ProofValidation::SoundAnalysis,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::Unbounded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// Explored to a finite unwind/model bound with no violation found; the
    /// bound is recorded honestly. Projects to `BoundedSound { depth }`.
    #[must_use]
    pub fn bounded(depth: u64) -> Self {
        Self {
            validation: ProofValidation::BoundedExploration,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::UnwindBounded { depth },
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// A verdict taken on trust (an external tool's say-so, no replayable
    /// evidence). Projects to `Trusted`.
    #[must_use]
    pub fn trusted_verdict() -> Self {
        Self {
            validation: ProofValidation::TrustedVerdict,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::Unrecorded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// Heuristic evidence with no formal guarantee. Projects to `Heuristic`.
    #[must_use]
    pub fn heuristic() -> Self {
        Self {
            validation: ProofValidation::HeuristicOnly,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::Unrecorded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    /// No validation at all — the fail-closed floor. Projects to `Unchecked`.
    #[must_use]
    pub fn unchecked() -> Self {
        Self {
            validation: ProofValidation::Unvalidated,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::Unrecorded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        }
    }

    // ---- R-U Phase C: axis queries -------------------------------------
    //
    // The semantic predicates call sites migrate ONTO, replacing `match`es
    // and `strength_order()` comparisons on the legacy enum. Each reads one
    // axis directly rather than round-tripping through `AssuranceLevel`.

    /// Whether the coverage axis records a finite bound (BMC depth / model
    /// size) rather than the unbounded input space.
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        matches!(
            self.coverage,
            CoverageBound::UnwindBounded { .. } | CoverageBound::ModelBounded { .. }
        )
    }

    /// The recorded finite bound, if any (unwind depth or model size).
    #[must_use]
    pub fn bounded_depth(&self) -> Option<u64> {
        match self.coverage {
            CoverageBound::UnwindBounded { depth } => Some(depth),
            CoverageBound::ModelBounded { size } => Some(size),
            CoverageBound::Unbounded | CoverageBound::Unrecorded => None,
        }
    }

    /// The reporting floor: a positive result is reportable as *proved* only
    /// at `SmtBacked` strength or above (kernel recheck with an empty closure,
    /// solver validation, or sound unbounded analysis). Defined as the
    /// projection crossing the legacy floor, so it is **provably identical**
    /// to the legacy `strength_order() >= SmtBacked` gate — not an
    /// axis-shaped approximation of it. The distinction matters at exactly one
    /// point: a kernel-rechecked proof resting on a *named* axiom closure
    /// projects to `Trusted` (below the floor), and must NOT be reported as
    /// proved even though its validation axis is `KernelRechecked`. An axis
    /// query that keyed on `validation` alone would fail OPEN there.
    /// Pinned by `reporting_floor_matches_legacy`.
    #[must_use]
    pub fn meets_reporting_floor(&self) -> bool {
        self.to_legacy().strength_order() >= AssuranceLevel::SmtBacked.strength_order()
    }

    /// Project the record back onto the legacy ladder — the compatibility
    /// view for consumers not yet migrated. Total, and the inverse of
    /// [`Self::from_legacy`] on its image (pinned by round-trip tests).
    ///
    /// Standing can only be *lost* here (the projection is monotone
    /// downward): a kernel-rechecked verdict whose closure is non-empty or
    /// unrecorded projects to `Trusted`/`SmtBacked`, never to `Certified`.
    #[must_use]
    pub fn to_legacy(&self) -> AssuranceLevel {
        match &self.validation {
            ProofValidation::KernelRechecked => match &self.axiom_closure {
                // Certified = kernel-rechecked ∧ empty closure, exactly.
                AxiomClosure::Empty => AssuranceLevel::Certified,
                // A named or unrecorded closure caps at Trusted (E8): the
                // proof is real but rests on assumptions (or unknown ones).
                AxiomClosure::Named(_) | AxiomClosure::Unrecorded => AssuranceLevel::Trusted,
            },
            ProofValidation::SolverValidated => AssuranceLevel::SmtBacked,
            ProofValidation::SoundAnalysis => AssuranceLevel::Sound,
            ProofValidation::TrustedVerdict => AssuranceLevel::Trusted,
            ProofValidation::BoundedExploration | ProofValidation::FiniteModelCheck => {
                let depth = match &self.coverage {
                    CoverageBound::UnwindBounded { depth } => *depth,
                    CoverageBound::ModelBounded { size } => *size,
                    CoverageBound::Unbounded | CoverageBound::Unrecorded => 0,
                };
                AssuranceLevel::BoundedSound { depth }
            }
            ProofValidation::HeuristicOnly => AssuranceLevel::Heuristic,
            ProofValidation::Unvalidated | ProofValidation::Pending => AssuranceLevel::Unchecked,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn all_legacy_variants() -> Vec<AssuranceLevel> {
        vec![
            AssuranceLevel::Sound,
            AssuranceLevel::BoundedSound { depth: 42 },
            AssuranceLevel::Heuristic,
            AssuranceLevel::Unchecked,
            AssuranceLevel::Trusted,
            AssuranceLevel::SmtBacked,
            AssuranceLevel::Certified,
        ]
    }

    /// R-U gate: the legacy → record → legacy round-trip is the identity for
    /// every legacy variant — the "lossless" requirement, mechanically.
    #[test]
    fn legacy_round_trip_is_identity() {
        for level in all_legacy_variants() {
            let record = GradeRecord::from_legacy(&level);
            assert_eq!(
                record.to_legacy(),
                level,
                "round-trip must be identity for {level:?} (got {record:?})"
            );
        }
    }

    /// R-U Phase C: every named constructor projects to exactly the legacy
    /// level it names, so a mechanical `AssuranceLevel::X` → `GradeRecord::x()`
    /// migration is verdict-identical under `.to_legacy()`.
    #[test]
    fn named_constructor_projects_to_its_legacy_level() {
        assert_eq!(GradeRecord::kernel_certified().to_legacy(), AssuranceLevel::Certified);
        assert_eq!(
            GradeRecord::kernel_trusted(["ax".to_string()]).to_legacy(),
            AssuranceLevel::Trusted
        );
        assert_eq!(GradeRecord::smt_backed().to_legacy(), AssuranceLevel::SmtBacked);
        assert_eq!(GradeRecord::sound_analysis().to_legacy(), AssuranceLevel::Sound);
        assert_eq!(GradeRecord::bounded(7).to_legacy(), AssuranceLevel::BoundedSound { depth: 7 });
        assert_eq!(GradeRecord::trusted_verdict().to_legacy(), AssuranceLevel::Trusted);
        assert_eq!(GradeRecord::heuristic().to_legacy(), AssuranceLevel::Heuristic);
        assert_eq!(GradeRecord::unchecked().to_legacy(), AssuranceLevel::Unchecked);
    }

    /// Only `kernel_certified()` satisfies the composite `is_certified`
    /// predicate — in particular a kernel proof under a named axiom does not.
    #[test]
    fn only_kernel_certified_constructor_is_certified() {
        assert!(GradeRecord::kernel_certified().is_certified());
        assert!(!GradeRecord::kernel_trusted(["ax".to_string()]).is_certified());
        assert!(!GradeRecord::smt_backed().is_certified());
        assert!(!GradeRecord::sound_analysis().is_certified());
    }

    /// The grade's reporting floor is byte-identical to the legacy floor
    /// (`strength_order() >= SmtBacked`) for every legacy variant AND for the
    /// one grade the legacy enum cannot spell: a kernel proof under a named
    /// axiom (KernelRechecked ∧ non-empty closure), which must sit BELOW the
    /// floor. This is the fail-open trap an axis-only query would fall into.
    #[test]
    fn reporting_floor_matches_legacy() {
        let floor = AssuranceLevel::SmtBacked.strength_order();
        for level in all_legacy_variants() {
            let record = GradeRecord::from_legacy(&level);
            assert_eq!(
                record.meets_reporting_floor(),
                level.strength_order() >= floor,
                "floor disagreement for {level:?}"
            );
        }
        // The non-legacy-spellable grade: kernel-rechecked under a named
        // axiom projects to Trusted (order 1) — below the floor. An axis
        // query keyed on `validation == KernelRechecked` would report it as
        // meeting the floor: a fail-open bug this test forbids.
        let kernel_trusted = GradeRecord::kernel_trusted(["assumed_lemma".to_string()]);
        assert_eq!(kernel_trusted.to_legacy(), AssuranceLevel::Trusted);
        assert!(!kernel_trusted.meets_reporting_floor());
    }

    /// The bounded-depth axis query round-trips the recorded bound and is
    /// `None` exactly for the unbounded/unrecorded coverage variants.
    #[test]
    fn bounded_depth_axis_query() {
        assert_eq!(GradeRecord::bounded(13).bounded_depth(), Some(13));
        assert!(GradeRecord::bounded(13).is_bounded());
        assert_eq!(GradeRecord::sound_analysis().bounded_depth(), None);
        assert!(!GradeRecord::sound_analysis().is_bounded());
        assert_eq!(GradeRecord::kernel_certified().bounded_depth(), None);
    }

    /// §7: no legacy verdict may gain standing — only legacy `Certified`
    /// satisfies the composite `is_certified` predicate after import.
    #[test]
    fn no_legacy_verdict_gains_certified_standing() {
        for level in all_legacy_variants() {
            let record = GradeRecord::from_legacy(&level);
            assert_eq!(
                record.is_certified(),
                matches!(level, AssuranceLevel::Certified),
                "standing changed in translation for {level:?}"
            );
        }
    }

    /// The strength order of the projected legacy view never exceeds the
    /// original's — translation is monotone non-increasing.
    #[test]
    fn projection_never_increases_strength() {
        for level in all_legacy_variants() {
            let record = GradeRecord::from_legacy(&level);
            assert!(
                record.to_legacy().strength_order() <= level.strength_order(),
                "strength grew in translation for {level:?}"
            );
        }
    }

    /// E8 as a type-level fact: a kernel-rechecked proof over a named axiom
    /// closure is NOT certified and projects to `Trusted` with the axioms
    /// still recorded on the record.
    #[test]
    fn named_axioms_cap_kernel_proofs_at_trusted() {
        let record = GradeRecord {
            validation: ProofValidation::KernelRechecked,
            axiom_closure: AxiomClosure::Named(
                ["user_axiom_scale_bound".to_string()].into_iter().collect(),
            ),
            coverage: CoverageBound::Unbounded,
            executability: Executability::Unmonitored,
            reflection: ReflectionTier::Fragment(1),
        };
        assert!(!record.is_certified());
        assert_eq!(record.to_legacy(), AssuranceLevel::Trusted);
    }

    /// An UNRECORDED closure must behave like a named one for standing (an
    /// import cannot claim empty-closure by omission).
    #[test]
    fn unrecorded_closure_is_not_certified() {
        let record = GradeRecord {
            validation: ProofValidation::KernelRechecked,
            axiom_closure: AxiomClosure::Unrecorded,
            coverage: CoverageBound::Unbounded,
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        };
        assert!(!record.is_certified());
        assert_eq!(record.to_legacy(), AssuranceLevel::Trusted);
    }

    /// Finite-model evidence (the ty lane) projects onto the bounded rung of
    /// the legacy ladder — it must never read as unbounded soundness.
    #[test]
    fn finite_model_projects_to_bounded() {
        let record = GradeRecord {
            validation: ProofValidation::FiniteModelCheck,
            axiom_closure: AxiomClosure::Empty,
            coverage: CoverageBound::ModelBounded { size: 5 },
            executability: Executability::Unrecorded,
            reflection: ReflectionTier::Unrecorded,
        };
        assert_eq!(record.to_legacy(), AssuranceLevel::BoundedSound { depth: 5 });
    }

    /// Evidence import: bounded reasoning refines the coverage axis but can
    /// never change standing — projection reproduces the original assurance
    /// for every (reasoning, assurance) pair.
    #[test]
    fn evidence_refinement_preserves_standing() {
        use crate::result::ReasoningKind;
        let reasonings = [
            ReasoningKind::Smt,
            ReasoningKind::BoundedModelCheck { depth: 9 },
            ReasoningKind::AbstractInterpretation,
        ];
        for level in all_legacy_variants() {
            for reasoning in &reasonings {
                let record = GradeRecord::from_legacy_evidence(reasoning, &level);
                assert_eq!(
                    record.to_legacy(),
                    level,
                    "standing changed for ({reasoning:?}, {level:?})"
                );
                assert_eq!(
                    record.is_certified(),
                    matches!(level, AssuranceLevel::Certified),
                    "certification changed for ({reasoning:?}, {level:?})"
                );
            }
        }
        // The refinement itself: a bounded engine's Sound verdict records its
        // bound on the coverage axis (where the legacy ladder lost it).
        let refined = GradeRecord::from_legacy_evidence(
            &ReasoningKind::BoundedModelCheck { depth: 9 },
            &AssuranceLevel::Sound,
        );
        assert_eq!(refined.coverage, CoverageBound::UnwindBounded { depth: 9 });
    }

    /// The record round-trips through serde like its neighbors in result.rs.
    #[test]
    fn grade_record_serde_round_trip() {
        let record = GradeRecord {
            validation: ProofValidation::BoundedExploration,
            axiom_closure: AxiomClosure::Named(["a1".to_string()].into_iter().collect()),
            coverage: CoverageBound::UnwindBounded { depth: 7 },
            executability: Executability::Monitored,
            reflection: ReflectionTier::Fragment(1),
        };
        let json = serde_json::to_string(&record).expect("serialize");
        let back: GradeRecord = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, record);
    }

    /// E4 static discharge does not imply per-iteration execution. The
    /// compiler has an exact certified loop-placement lane, but a row with no
    /// matching placement evidence is still carried as explicitly unmonitored
    /// rather than being left ambiguous or upgraded from its proof strength.
    #[test]
    fn unmatched_e4_monitor_row_refines_only_executability() {
        use crate::result::{TransportMonitorEvidence, TransportMonitorStatus};

        let monitor = TransportMonitorEvidence {
            status: TransportMonitorStatus::Unmonitored,
            reason: "no kernel-certified loop monitor evidence matched this row".into(),
            predicate_digest: format!("sha256:{}", "d".repeat(64)),
        };
        let baseline = GradeRecord::smt_backed();
        let refined = baseline.clone().with_monitor_evidence(Some(&monitor));

        assert_eq!(refined.executability, Executability::Unmonitored);
        assert_eq!(refined.validation, baseline.validation);
        assert_eq!(refined.axiom_closure, baseline.axiom_closure);
        assert_eq!(refined.coverage, baseline.coverage);
        assert_eq!(refined.reflection, baseline.reflection);
        assert_eq!(refined.to_legacy(), baseline.to_legacy());
    }

    #[test]
    fn e5_measured_transport_preserves_its_distinct_executability() {
        use crate::result::{TransportMonitorEvidence, TransportMonitorStatus};

        let measure = TransportMonitorEvidence {
            status: TransportMonitorStatus::Measured,
            reason: "kernel-bound scalar plus authenticated transition placement".into(),
            predicate_digest: format!("sha256:{}", "e".repeat(64)),
        };
        let baseline = GradeRecord::smt_backed();
        let refined = baseline.clone().with_monitor_evidence(Some(&measure));

        assert_eq!(refined.executability, Executability::Measured);
        assert_eq!(refined.validation, baseline.validation);
        assert_eq!(refined.to_legacy(), baseline.to_legacy());
    }
}
