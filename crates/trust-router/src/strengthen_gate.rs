// trust-router/strengthen_gate.rs: fail-closed admissibility gate for inferred-
// precondition strengthening (#540 — "never allow vacuous"; now also "never allow
// UNSOUND").
//
// Candidate generation may run by default, but this authority gate currently
// admits NO verdict flips. Without this gate the older strengthen loop was a
// verified NO-OP: `strengthen_failed_vcs` conjoined an *uninterpreted*
// `Formula::Var("__precond_…", Bool)` that shares no symbol with the goal, so the
// solver picks its value freely and no verdict ever changes. Turning that into a
// REAL assumption is sound ONLY if the assumption is (a) connected to the program,
// (b) itself proven (DISCHARGED), and (c) necessary — otherwise the verifier would
// discharge a FALSE obligation, the single worst outcome for a proof-carrying
// compiler.
//
// SOUNDNESS MODEL (assume-guarantee). The discharge of an inferred precondition `P`
// is the proof obligation `R ⟹ P`, where `R = func.preconditions` is the function's
// gate-approved declared contract (which the contract system enforces at every call
// site as `¬(R[actuals])`, so `R` holds at entry). Proving `R ⟹ P` (i.e. the
// violation `R ∧ ¬P` is UNSAT) means `P` holds at entry, so assuming `P` is sound.
//
// This gate is the pure, decidable chokepoint that decides whether a strengthened
// `Proved` may be ATTRIBUTED to the original obligation. The legacy structural
// decision remains unit-tested, but production attribution is currently HARD-
// BLOCKED: `AssuranceLevel::Certified` and `VerificationResult::Proved` are public
// data and can be forged without a certificate. Until a sealed token binds the
// exact VC digest to replayed kernel evidence, the public entry point always
// rejects and the caller keeps the original honest verdict.
//
// LEGACY STRUCTURAL MODEL (retained in tests): even a future sealed certificate
// is not sufficient unless it binds the right formula. The discharge must be
// structurally `R' ∧ ¬P` with `R' ⊆ R`, so it proves at most the declared
// contract entails `P`, nothing weaker or unrelated.
//
// Scope note: the MIR-context guards (assumable-fragment, formal-index binding,
// staleness-safe versioned conjunction, debug-name shadow check) live in
// `trust-mir-extract`/`trust-vcgen` where the MIR is in scope. This gate is the
// second, independent layer over the goal/assumption formulas and the verdicts.

#[cfg(test)]
use trust_types::AssuranceLevel;
use trust_types::{Formula, VerificationResult};

/// Whether the ITERATIVE, single-function strengthening loop may authorize a
/// verdict change. STILL FALSE — it has no sealed evidence carrier.
///
/// SCOPE — read this before flipping it. This constant governs the in-compiler
/// strengthen loop (trust-loop / trust-strengthen: abstract domains, CEGIS, and
/// LLM proposers) and [`is_admissible_strengthening`] below. It does NOT govern
/// R1 whole-program caller propagation ([`crate::strengthen_whole_program`]),
/// which was split off onto its own decision path when R1 gained real sealed,
/// kernel-replayed evidence (2026-07-14) and needs no switch of its own.
///
/// The split is deliberate and load-bearing: the two lanes were previously fused
/// on this one constant, so restoring R1 would ALSO have silently switched a
/// CEGIS/LLM proposer loop on inside the shipped compiler — a capability nobody
/// asked for and whose evidence story is unrelated. Keep them separate. Enabling
/// THIS lane requires giving it its own sealed carrier and changing
/// [`is_admissible_strengthening`] to consume it; flipping the constant alone is
/// not sufficient, because that function still rejects unconditionally.
pub const STRENGTHENING_AUTHORITY_AVAILABLE: bool = false;

/// Why a proposed strengthening was rejected. Every variant ⇒ the original
/// obligation's verdict stands (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Inadmissible {
    /// Production strengthening authority is disabled until a private/sealed
    /// certificate token binds the exact strengthened and discharge VC digests
    /// to replayed kernel evidence. A public `Certified` enum label is not such
    /// evidence and cannot authorize a flip.
    SealedCertificationUnavailable,
    /// The assumption's free variables are empty or not a subset of the goal's —
    /// it does not constrain the program. This is exactly the #540 `__precond_…`
    /// atom (disjoint symbols), and any other disconnected hypothesis.
    Disconnected,
    /// The strengthened formula's proof is not kernel-`Certified` (a bare,
    /// unvalidated solver "unsat" is not enough).
    StrengthenedNotCertified,
    /// The original obligation did not genuinely `Failed` — no real counterexample
    /// for the assumption to rule out (an `Unknown`/`Timeout` does not establish
    /// necessity).
    NotNecessary,
    /// There is no discharge obligation, or one is not `Certified`. Empty ⇒ reject:
    /// assuming an un-proven fact is unsound.
    Undischarged,
    /// A discharge obligation is `Certified`, but its FORMULA is not the expected
    /// `R' ∧ ¬P` (with `R' ⊆ gated_requires` and `¬P` present) — i.e. it proves
    /// something other than "the declared contract entails the assumption". This
    /// catches a `Certified` proof of an unrelated VC masquerading as a discharge.
    DischargeFormulaMismatch,
}

/// The verdicts a strengthening attribution depends on (the discharge obligations
/// are passed separately, with their formulas, to `is_admissible_strengthening`).
pub struct StrengthenProofState<'a> {
    /// Verdict on the ORIGINAL violation formula (must be `Failed` for necessity).
    pub original_result: &'a VerificationResult,
    /// Verdict on the gated, versioned, re-vcgen'd strengthened VC (must be
    /// `Certified`).
    pub strengthened_result: &'a VerificationResult,
}

/// Legacy structural-model predicate: whether a result carries the public
/// `Certified` label. This is test-only and deliberately NON-AUTHORITATIVE;
/// the label is publicly constructible and does not prove payload replay.
#[cfg(test)]
fn has_certified_label(r: &VerificationResult) -> bool {
    matches!(
        r.clone().require_assurance(AssuranceLevel::Certified),
        VerificationResult::Proved { .. }
    )
}

/// Whether `obligation` is structurally `R' ∧ ¬P` with `¬P` present and every other
/// conjunct a member of `gated_requires` (`R' ⊆ R`). Proving such an obligation UNSAT
/// establishes `R ⟹ P` (or something stronger — fewer assumptions), which is sound.
/// Any other shape is rejected: it does not establish entailment of `P` by the
/// declared contract.
#[cfg(test)]
fn discharge_formula_ok(
    obligation: &Formula,
    assumption: &Formula,
    gated_requires: &[Formula],
) -> bool {
    let not_p = Formula::Not(Box::new(assumption.clone()));
    let Formula::And(conjuncts) = obligation else {
        // The discharge VC is always built as `And(R' ++ [¬P])`; a bare `¬P` would
        // be `And([¬P])`. Anything that is not an `And` is not our obligation.
        return false;
    };
    if !conjuncts.contains(&not_p) {
        return false; // must actually negate THIS assumption
    }
    // Every conjunct other than `¬P` must be part of the declared contract.
    conjuncts.iter().all(|c| *c == not_p || gated_requires.contains(c))
}

/// Production authority gate for a proposed strengthened verdict.
///
/// This currently always returns
/// [`Inadmissible::SealedCertificationUnavailable`]. The structural inputs are
/// retained so the eventual sealed certificate can be checked against this
/// exact decision boundary, but public assurance labels cannot authorize it.
///
/// - `added_assumption` — `P`, the inferred precondition.
/// - `goal_violation` — `V`, the original violation formula.
/// - `gated_requires` — `R`, the function's gate-approved declared contract
///   (`func.preconditions` after `gate_contract_preconditions`).
/// - `discharge_obligations` — the `(formula, verdict)` pairs proving `R ⟹ P`; each
///   formula must be `R' ∧ ¬P`; its future sealed evidence must bind that exact
///   formula digest.
pub fn is_admissible_strengthening(
    added_assumption: &Formula,
    goal_violation: &Formula,
    gated_requires: &[Formula],
    discharge_obligations: &[(Formula, VerificationResult)],
    st: &StrengthenProofState<'_>,
) -> Result<(), Inadmissible> {
    // HARD AUTHORITY BLOCK: all inputs below are public, forgeable data. Do
    // not inspect them as proof authority until this API receives a sealed
    // token created only after exact-digest validation and kernel replay.
    let _ = (added_assumption, goal_violation, gated_requires, discharge_obligations, st);
    Err(Inadmissible::SealedCertificationUnavailable)
}

/// Exercise the pre-existing structural model without granting production
/// authority. This stays test-only so no caller can accidentally bypass the
/// sealed-certificate hard block in [`is_admissible_strengthening`].
#[cfg(test)]
fn structurally_admissible_strengthening(
    added_assumption: &Formula,
    goal_violation: &Formula,
    gated_requires: &[Formula],
    discharge_obligations: &[(Formula, VerificationResult)],
    st: &StrengthenProofState<'_>,
) -> Result<(), Inadmissible> {
    // (1) CONNECTEDNESS — the assumption must constrain the goal's own variables.
    //     Rejects the #540 uninterpreted `__precond_…` atom (disjoint symbols).
    let avars = added_assumption.free_variables();
    if avars.is_empty() || !avars.is_subset(&goal_violation.free_variables()) {
        return Err(Inadmissible::Disconnected);
    }
    // (2) The strengthened formula must itself be kernel-CERTIFIED.
    if !has_certified_label(st.strengthened_result) {
        return Err(Inadmissible::StrengthenedNotCertified);
    }
    // (3) NECESSITY — a real counterexample existed (Failed), not merely "not proved".
    if !st.original_result.is_failed() {
        return Err(Inadmissible::NotNecessary);
    }
    // (4) DISCHARGE — ≥1 obligation; each CERTIFIED *and* structurally `R' ∧ ¬P`.
    //     Empty ⇒ reject (no sound source). A Certified verdict alone is not enough:
    //     its FORMULA must prove the declared contract entails `P` (FIX 2).
    if discharge_obligations.is_empty() {
        return Err(Inadmissible::Undischarged);
    }
    for (formula, verdict) in discharge_obligations {
        if !has_certified_label(verdict) {
            return Err(Inadmissible::Undischarged);
        }
        if !discharge_formula_ok(formula, added_assumption, gated_requires) {
            return Err(Inadmissible::DischargeFormulaMismatch);
        }
    }
    Ok(())
}

/// Owned carrier the compiler-side wiring fills per failed VC, then submits to
/// the production hard block. `discharge_obligations` is `(¬(R⟹P) formula,
/// its router verdict)`; none of these public fields is certificate authority.
pub struct StrengthenRecord {
    pub assumption: Formula,
    pub goal_violation: Formula,
    pub gated_requires: Vec<Formula>,
    pub discharge_obligations: Vec<(Formula, VerificationResult)>,
    pub original_result: VerificationResult,
    pub strengthened_result: VerificationResult,
}

impl StrengthenRecord {
    /// Submit this record to [`is_admissible_strengthening`]. This remains
    /// fail-closed until the API also carries sealed, digest-bound evidence.
    pub fn admit(&self) -> Result<(), Inadmissible> {
        let st = StrengthenProofState {
            original_result: &self.original_result,
            strengthened_result: &self.strengthened_result,
        };
        is_admissible_strengthening(
            &self.assumption,
            &self.goal_violation,
            &self.gated_requires,
            &self.discharge_obligations,
            &st,
        )
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{ProofStrength, VerificationResult, parse_spec_expr};

    use super::*;

    fn certified() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_certified(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }
    fn unvalidated() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_unvalidated(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }
    fn failed() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None }
    }
    fn unknown() -> VerificationResult {
        VerificationResult::Unknown { solver: "ay".into(), time_ms: 1, reason: String::new() }
    }
    fn f(s: &str) -> Formula {
        parse_spec_expr(s).expect("parses")
    }
    // R := "a <= 100"; P := "a < 200" (R ⟹ P); V over {a}.
    fn r() -> Formula {
        f("a <= 100")
    }
    fn p() -> Formula {
        f("a < 200")
    }
    fn v() -> Formula {
        f("a > 300")
    }
    // The well-formed discharge obligation `R ∧ ¬P`.
    fn good_obligation() -> Formula {
        Formula::And(vec![r(), Formula::Not(Box::new(p()))])
    }
    fn st<'a>(
        orig: &'a VerificationResult,
        strong: &'a VerificationResult,
    ) -> StrengthenProofState<'a> {
        StrengthenProofState { original_result: orig, strengthened_result: strong }
    }

    // (ii) VACUITY CONTROL — a disconnected assumption (the #540 shape) is rejected
    // even when every verdict/formula is otherwise perfect.
    #[test]
    fn disconnected_assumption_is_rejected() {
        let other = f("b < 5"); // {b} ⊄ {a}
        let oblig = [(Formula::And(vec![r(), Formula::Not(Box::new(other.clone()))]), certified())];
        assert_eq!(
            structurally_admissible_strengthening(
                &other,
                &v(),
                &[r()],
                &oblig,
                &st(&failed(), &certified()),
            ),
            Err(Inadmissible::Disconnected)
        );
    }

    // (i) SOUNDNESS CONTROL — a real, connected P with NO discharge obligation must
    // be REJECTED. Assuming an un-proven fact is the catastrophic case.
    #[test]
    fn undischarged_is_rejected() {
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &[],
                &st(&failed(), &certified()),
            ),
            Err(Inadmissible::Undischarged)
        );
    }

    // (i-a) SOUNDNESS CONTROL — no declared contract (R = ∅) and no obligation ⇒ reject.
    #[test]
    fn no_contract_source_is_rejected() {
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[],
                &[],
                &st(&failed(), &certified()),
            ),
            Err(Inadmissible::Undischarged)
        );
    }

    // (i-b) SOUNDNESS CONTROL — a discharge "proved" only by an UNVALIDATED solver
    // unsat must be REJECTED (`is_proved` would have wrongly accepted it).
    #[test]
    fn unvalidated_discharge_is_rejected() {
        let oblig = [(good_obligation(), unvalidated())];
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &oblig,
                &st(&failed(), &certified()),
            ),
            Err(Inadmissible::Undischarged)
        );
    }

    // (i-c) SOUNDNESS CONTROL (FIX 2) — a CERTIFIED verdict whose discharge FORMULA
    // is not `R ∧ ¬P` (an unrelated/wrong VC) must be REJECTED. This is the hole the
    // formula cross-check closes: a real proof of the wrong thing is not a discharge.
    #[test]
    fn discharge_formula_mismatch_is_rejected() {
        // Certified, but negates a DIFFERENT predicate than P (¬"a<999" ≠ ¬P).
        let wrong = Formula::And(vec![r(), Formula::Not(Box::new(f("a < 999")))]);
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &[(wrong, certified())],
                &st(&failed(), &certified())
            ),
            Err(Inadmissible::DischargeFormulaMismatch)
        );
        // Certified, ¬P present, but an EXTRA conjunct not in the declared contract.
        let extra = Formula::And(vec![r(), f("a > 0"), Formula::Not(Box::new(p()))]);
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &[(extra, certified())],
                &st(&failed(), &certified())
            ),
            Err(Inadmissible::DischargeFormulaMismatch)
        );
    }

    // (i-d) SOUNDNESS CONTROL — the strengthened proof itself must be Certified.
    #[test]
    fn unvalidated_strengthened_is_rejected() {
        let oblig = [(good_obligation(), certified())];
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &oblig,
                &st(&failed(), &unvalidated()),
            ),
            Err(Inadmissible::StrengthenedNotCertified)
        );
    }

    // (i-e) NECESSITY CONTROL — if the original did not genuinely fail, reject.
    #[test]
    fn not_necessary_is_rejected() {
        let oblig = [(good_obligation(), certified())];
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &oblig,
                &st(&unknown(), &certified()),
            ),
            Err(Inadmissible::NotNecessary)
        );
    }

    // (iii) POSITIVE — fails alone; connected P; strengthened Certified; the declared
    // contract `R` entails `P` via a Certified, structurally-correct `R ∧ ¬P` ⇒ admitted.
    #[test]
    fn contract_entailed_precondition_is_admitted() {
        assert!(p().free_variables().is_subset(&v().free_variables()));
        let oblig = [(good_obligation(), certified())];
        assert_eq!(
            structurally_admissible_strengthening(
                &p(),
                &v(),
                &[r()],
                &oblig,
                &st(&failed(), &certified()),
            ),
            Ok(())
        );
    }

    /// A forged public `Certified` label with no payload cannot authorize the
    /// production gate, even when every structural input is otherwise valid.
    #[test]
    fn forged_certified_label_without_payload_is_hard_blocked() {
        let oblig = [(good_obligation(), certified())];
        assert_eq!(
            is_admissible_strengthening(&p(), &v(), &[r()], &oblig, &st(&failed(), &certified()),),
            Err(Inadmissible::SealedCertificationUnavailable)
        );
    }

    /// The owned carrier reaches the same production hard block.
    #[test]
    fn record_admit_is_hard_blocked() {
        let rec = StrengthenRecord {
            assumption: p(),
            goal_violation: v(),
            gated_requires: vec![r()],
            discharge_obligations: vec![(good_obligation(), certified())],
            original_result: failed(),
            strengthened_result: certified(),
        };
        assert_eq!(rec.admit(), Err(Inadmissible::SealedCertificationUnavailable));
    }
}
