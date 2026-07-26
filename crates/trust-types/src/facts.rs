// trust-types/facts.rs: remembered facts for cross-function spec composition
//
// This module provides a small, reusable in-memory model for proof facts
// discovered by the verifier and reused at call sites. The first slice is
// intentionally conservative: call-site discharge is exact formula matching
// only, which keeps the data model sound and easy for later compiler passes
// to extend.

use serde::{Deserialize, Serialize};

use crate::{Formula, ProofStrength};

/// Stable identifier for a remembered fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FactId(pub usize);

/// A postcondition that has been proved and can be reused as a note.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvedPostcondition {
    /// Function that proved the postcondition.
    pub function: String,
    /// Solver that proved the fact.
    pub solver: String,
    /// Strength of the proof.
    pub strength: ProofStrength,
}

/// Origin information for a remembered fact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FactSource {
    /// A proved postcondition from another function.
    ProvedPostcondition(ProvedPostcondition),
    /// An explicitly recorded assumption.
    Assumption { label: String },
    /// A manually imported note.
    Note { note: String },
}

impl FactSource {
    fn is_proved_postcondition_for(&self, _callee: &str) -> bool {
        // AUTHORITY BOUNDARY: `FactMemory`, `ProvedPostcondition`, and
        // `ProofStrength` are public, serde-constructible metadata.  Neither a
        // `Sound`/`Certified` label nor the solver/name strings carry a
        // replayable proof bound to this exact callee contract and predicate.
        // Until that evidence is transported and independently replayed, a
        // remembered fact is reporting/diagnostic state only and must never
        // suppress a caller VC.
        false
    }

    /// Returns true when this source is a reusable proved postcondition.
    pub fn is_reusable_proved_postcondition(&self) -> bool {
        false
    }

    /// Returns true when this source is a reusable proved postcondition for
    /// the named callee.
    pub fn is_reusable_proved_postcondition_for(&self, callee: &str) -> bool {
        self.is_proved_postcondition_for(callee)
    }
}

/// A remembered fact available for later call-site reasoning.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnownFact {
    pub id: FactId,
    pub predicate: Formula,
    pub source: FactSource,
}

/// In-memory store for remembered facts.
///
/// The store is append-only. Facts remain non-authoritative metadata until a
/// future evidence-bearing API can replay a proof bound to the exact callee,
/// contract, and predicate; exact formula/name matching alone is not proof.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactMemory {
    facts: Vec<KnownFact>,
}

/// Result of checking a call-site requirement against remembered facts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CallSiteSatisfaction {
    /// A remembered fact discharged the requirement.
    SatisfiedFromNotes { fact_id: FactId, source: FactSource },
    /// No remembered fact was sufficient, so a solver is still needed.
    RequiresSolver { callee: String },
}

/// Trust: How a verification condition was resolved.
///
/// Three costs from the design doc:
/// - Known from notes (free) — a proved postcondition satisfies this VC
/// - Solver proves it (costs time) — the standard solver path
/// - Solver can't (runtime check or error) — unproved
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcDisposition {
    /// Satisfied from compiler notes — no solver call needed.
    /// The cheapest outcome: a previously proved postcondition discharges the requirement.
    SatisfiedFromNotes { fact_id: FactId, source: FactSource },
    /// Requires a solver call — the standard verification path.
    RequiresSolver,
    /// An explicit assumption was injected by a caller that already has a
    /// sound, scoped assumption model.
    SolverWithAssumption { fact_id: FactId, source: FactSource },
}

impl FactMemory {
    /// Create an empty fact memory.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of remembered facts.
    pub fn len(&self) -> usize {
        self.facts.len()
    }

    /// Returns true when no facts have been remembered.
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// Returns all remembered facts in insertion order.
    pub fn facts(&self) -> &[KnownFact] {
        &self.facts
    }

    /// Returns a single fact by id.
    pub fn fact(&self, id: FactId) -> Option<&KnownFact> {
        self.facts.iter().find(|fact| fact.id == id)
    }

    /// Remember a proved postcondition so later call sites can reuse it.
    pub fn remember_proved_postcondition(
        &mut self,
        function: impl Into<String>,
        predicate: Formula,
        solver: impl Into<String>,
        strength: ProofStrength,
    ) -> FactId {
        self.insert(KnownFact {
            id: FactId(self.facts.len()),
            predicate,
            source: FactSource::ProvedPostcondition(ProvedPostcondition {
                function: function.into(),
                solver: solver.into(),
                strength,
            }),
        })
    }

    /// Remember an explicit assumption as a reusable fact.
    pub fn remember_assumption(&mut self, predicate: Formula, label: impl Into<String>) -> FactId {
        self.insert(KnownFact {
            id: FactId(self.facts.len()),
            predicate,
            source: FactSource::Assumption { label: label.into() },
        })
    }

    /// Remember a manual note as a reusable fact.
    pub fn remember_note(&mut self, predicate: Formula, note: impl Into<String>) -> FactId {
        self.insert(KnownFact {
            id: FactId(self.facts.len()),
            predicate,
            source: FactSource::Note { note: note.into() },
        })
    }

    /// Check whether a call-site requirement is already satisfied from notes.
    ///
    /// All current fact variants are public metadata and therefore never enough
    /// to discharge the requirement. They remain available for reporting and a
    /// future scoped, replayable evidence model.
    pub fn satisfy_call_site(
        &self,
        callee: impl Into<String>,
        _requirement: &Formula,
    ) -> CallSiteSatisfaction {
        let callee = callee.into();
        CallSiteSatisfaction::RequiresSolver { callee }
    }

    fn insert(&mut self, fact: KnownFact) -> FactId {
        let id = fact.id;
        self.facts.push(fact);
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AssuranceLevel;

    fn ge(lhs: Formula, rhs: Formula) -> Formula {
        Formula::Ge(Box::new(lhs), Box::new(rhs))
    }

    #[test]
    fn test_public_sound_postcondition_is_metadata_only() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(0));

        let fact_id = memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(memory.len(), 1);

        let fact = memory.fact(fact_id).expect("remembered metadata");
        assert!(matches!(fact.source, FactSource::ProvedPostcondition(_)));
        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() },
            "a public Sound label must not suppress solver dispatch"
        );
    }

    #[test]
    fn test_same_formula_different_callee_requires_solver() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(
            memory.satisfy_call_site("sqrt", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "sqrt".to_string() }
        );
    }

    #[test]
    fn test_smt_backed_assurance_requires_solver() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(0));
        memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "ay",
            ProofStrength {
                reasoning: crate::ReasoningKind::Smt,
                assurance: AssuranceLevel::SmtBacked,
            },
        );

        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() }
        );
    }

    #[test]
    fn test_forgeable_certified_assurance_requires_solver() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(0));
        memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "claimed-clean",
            ProofStrength::smt_unsat_certified(),
        );

        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() }
        );
    }

    #[test]
    fn test_satisfy_call_site_requires_solver_without_match() {
        let memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(1));

        let satisfaction = memory.satisfy_call_site("sqrt", &requirement);
        assert_eq!(
            satisfaction,
            CallSiteSatisfaction::RequiresSolver { callee: "sqrt".to_string() }
        );
    }

    #[test]
    fn test_no_public_fact_variant_wins_authority() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("x".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_note(requirement.clone(), "manual note");
        memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() }
        );
    }

    #[test]
    fn test_assumption_exact_match_still_requires_solver() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("x".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_assumption(requirement.clone(), "caller precondition");

        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() }
        );
    }

    #[test]
    fn test_note_exact_match_still_requires_solver() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("x".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_note(requirement.clone(), "manual note");

        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() }
        );
    }

    #[test]
    fn test_bounded_postcondition_exact_match_still_requires_solver() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("x".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "bmc",
            ProofStrength::bounded(64),
        );

        assert_eq!(
            memory.satisfy_call_site("parse", &requirement),
            CallSiteSatisfaction::RequiresSolver { callee: "parse".to_string() }
        );
    }

    #[test]
    fn test_serialization_roundtrip() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("len".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_assumption(requirement, "len is non-negative");

        let json = serde_json::to_string(&memory).expect("serialize");
        let round: FactMemory = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(round.len(), 1);
        assert_eq!(
            round.facts()[0].source,
            FactSource::Assumption { label: "len is non-negative".to_string() }
        );
    }
}
