//! Sealed-authority S3: the gate-side CHC/PDR invariant replay oracle.
//!
//! This module is the trust-bmc primitive of blueprint slice S3
//! (`docs/design-notes/2026-07-17-sealed-authority-blueprint.md`): a PURE,
//! in-process wrapper around `ay_chc::engines::validate_external_invariant_model`
//! — the same full init + transition + query clause discharge trust-mc-driver's
//! IC3 loop lane runs before emitting accepted `PdrInvariant` evidence
//! (`first-party/trust-mc/trust-mc-driver/src/native.rs`, `try_ic3_loop_lane`).
//!
//! Fail-closed hard rejections, applied BEFORE delegating:
//!
//! - **Vacuous problems (no live query clause)**: `verify_model_impl`'s clause
//!   loop discharges exactly the clauses present — a problem with zero clauses,
//!   or with init/transition clauses but no `ClauseHead::False` safety query,
//!   "accepts" any interpretation without any safety property having been
//!   checked (the D2 vacuous-transition-system laundering shape). The oracle
//!   requires at least one LIVE query clause in `problem.clauses()` and
//!   rejects otherwise (`ChcReplayRejection::NoQueryClause`). This is
//!   deliberately STRICTER than ay-chc's own `ChcProblem::validate`, which
//!   also accepts a problem whose only query was parser-pruned as trivially
//!   false (`pruned_false_queries`) — a pruned query contributes zero clause
//!   discharges, so it earns no invariant-strength acceptance here.
//! - **Ghost-pair certificates** (constitution U4):
//!   `validate_external_invariant_model` short-circuits a model carrying a
//!   sealed FORALL-ARR ghost-pair certificate into
//!   `recheck_ghost_pair_certificate` — a *different evidence class* than
//!   quantifier-free invariant clause discharge. The oracle rejects such
//!   models outright (`ChcReplayRejection::GhostPairCertificate`).
//! - **Empty models** (constitution U4): the validator routes
//!   `model.is_empty()` into `validate_empty_scalar_acyclic_bmc_certificate`
//!   — an acyclic-exhaustive BMC certificate, again not an
//!   inductive-invariant discharge. Rejected outright
//!   (`ChcReplayRejection::EmptyModel`).
//!
//! Each escape would otherwise let a non-invariant (or no) evidence class ride
//! in under CHC/PDR invariant strength.
//!
//! Panic containment: the delegation runs inside `catch_unwind`; any panic is
//! `ChcReplayRejection::ValidatorPanicked`. (`validate_external_invariant_model`
//! additionally converts internal ay panics to `ChcError::Internal`, which the
//! oracle maps to `ValidatorErrored` — still a rejection.)
//!
//! Authority discipline: `ChcReplayVerdict` is deliberately serde-free, has no
//! `Default`, and its construction is private to this module. Holding an
//! accepted verdict therefore implies THIS process ran the full clause check —
//! the verdict cannot be deserialized, defaulted, or assembled by a consumer.
//! The `problem_fingerprint` it echoes is a domain-separated SHA-256 over ay's
//! own deterministic `normalized_chc_input` rendering of the problem the check
//! actually ran against, so a later gate can bind the verdict to its own
//! re-derived problem (reject-only correlation; the fingerprint grants
//! nothing).

use std::panic::{catch_unwind, AssertUnwindSafe};

use ay_chc::{ChcProblem, InvariantModel, PdrConfig};
use sha2::{Digest, Sha256};

/// Domain-separation prefix for [`ChcReplayVerdict::problem_fingerprint`].
///
/// The fingerprint is `sha256(DOMAIN || normalized_chc_input(problem))`,
/// lowercase hex. `normalized_chc_input` is ay-chc's own deterministic
/// normalized CHC/PDR rendering (the same text `normalized_input_sha256`
/// hashes for proof-transcript binding); the domain prefix keeps this hash
/// from colliding with ay's un-prefixed `normalized_chc_input_sha256` or any
/// other sha256-over-the-same-text in the pipeline.
const PROBLEM_FINGERPRINT_DOMAIN: &str = "trust-bmc.replay-oracle.chc-problem.v1\n";

/// Why the oracle rejected a candidate invariant model.
///
/// Every variant is a *rejection*: the caller learns why, but no variant
/// carries or implies any positive evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcReplayRejection {
    /// The problem contains no live query clause (`ClauseHead::False`) —
    /// either it has no clauses at all, or only init/transition clauses.
    /// `verify_model_impl` would "accept" a model over such a system with
    /// ZERO safety discharges (its clause loop checks only the clauses
    /// present), which is the vacuous-transition-system laundering shape the
    /// blueprint's D2 attack confirmed. A problem whose only query was
    /// parser-pruned as trivially false (`pruned_false_queries`) also lands
    /// here: pruned queries contribute no clause discharge.
    NoQueryClause,
    /// The model has no predicate interpretations. ay-chc would route this to
    /// `validate_empty_scalar_acyclic_bmc_certificate` — an acyclic-exhaustive
    /// BMC evidence class, not an inductive invariant (constitution U4).
    EmptyModel,
    /// The model carries a sealed FORALL-ARR ghost-pair certificate. ay-chc
    /// would short-circuit into `recheck_ghost_pair_certificate` — a different
    /// evidence class than quantifier-free invariant clause discharge
    /// (constitution U4).
    GhostPairCertificate,
    /// The full init + transition + query clause discharge ran and REJECTED
    /// the candidate: it is not an inductive invariant for this problem.
    InvariantNotInductive,
    /// The validator returned an error (I/O, parse, or an internal ay panic
    /// already converted to `ChcError::Internal` by `catch_ay_panics`).
    ValidatorErrored(String),
    /// The delegated validation panicked; the panic was contained by the
    /// oracle's `catch_unwind`.
    ValidatorPanicked,
}

impl std::fmt::Display for ChcReplayRejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoQueryClause => write!(
                f,
                "problem has no live query clause (nothing to discharge — a \
                 model over a query-free system earns no invariant-strength \
                 acceptance)"
            ),
            Self::EmptyModel => write!(
                f,
                "empty invariant model (routes to an acyclic-exhaustive BMC \
                 evidence class, not an inductive invariant)"
            ),
            Self::GhostPairCertificate => write!(
                f,
                "model carries a ghost-pair certificate (a different evidence \
                 class than quantifier-free invariant clause discharge)"
            ),
            Self::InvariantNotInductive => write!(
                f,
                "full clause discharge rejected the candidate invariant \
                 (not inductive for this problem)"
            ),
            Self::ValidatorErrored(reason) => write!(f, "validator errored: {reason}"),
            Self::ValidatorPanicked => write!(f, "validator panicked (contained)"),
        }
    }
}

/// The oracle's verdict on one `(problem, candidate model)` replay.
///
/// Serde-free, `Default`-free, and construction-private BY DESIGN: an
/// accepted verdict can only come out of [`replay_chc_invariant`] in this
/// process, after the full clause discharge actually ran here. Consumers
/// observe it through the accessor methods only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcReplayVerdict {
    inner: VerdictInner,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum VerdictInner {
    Accepted {
        /// Domain-separated SHA-256 (lowercase hex) over ay's deterministic
        /// `normalized_chc_input` rendering of the EXACT problem the clause
        /// discharge ran against. See [`PROBLEM_FINGERPRINT_DOMAIN`].
        problem_fingerprint: String,
    },
    Rejected(ChcReplayRejection),
}

impl ChcReplayVerdict {
    // NOTE: no public constructor, no serde, no Default. Construction stays
    // private to this module so holding an accepted verdict implies this
    // process ran the check.
    fn accepted(problem_fingerprint: String) -> Self {
        Self {
            inner: VerdictInner::Accepted {
                problem_fingerprint,
            },
        }
    }

    fn rejected(rejection: ChcReplayRejection) -> Self {
        Self {
            inner: VerdictInner::Rejected(rejection),
        }
    }

    /// True iff the full clause discharge ran in this process and accepted
    /// the candidate invariant for the fingerprinted problem.
    pub fn is_accepted(&self) -> bool {
        matches!(self.inner, VerdictInner::Accepted { .. })
    }

    /// The domain-separated problem fingerprint, present only on acceptance.
    pub fn problem_fingerprint(&self) -> Option<&str> {
        match &self.inner {
            VerdictInner::Accepted {
                problem_fingerprint,
            } => Some(problem_fingerprint),
            VerdictInner::Rejected(_) => None,
        }
    }

    /// The rejection reason, present only on rejection.
    pub fn rejection(&self) -> Option<&ChcReplayRejection> {
        match &self.inner {
            VerdictInner::Accepted { .. } => None,
            VerdictInner::Rejected(rejection) => Some(rejection),
        }
    }
}

/// Compute the domain-separated fingerprint of `problem`.
fn problem_fingerprint(problem: &ChcProblem) -> String {
    let mut hasher = Sha256::new();
    hasher.update(PROBLEM_FINGERPRINT_DOMAIN.as_bytes());
    hasher.update(ay_chc::normalized_chc_input(problem).as_bytes());
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}

/// Replay-check a candidate CHC/PDR invariant model against `problem`,
/// in-process, fail-closed.
///
/// This is a PURE wrapper (no I/O, no globals, no caching) around
/// `ay_chc::engines::validate_external_invariant_model` — the same call
/// trust-mc-driver's IC3 loop lane makes before emitting accepted
/// `PdrInvariant` evidence — with the vacuity and constitution-U4 escape
/// hatches closed BEFORE delegation:
///
/// 1. problems with no live query clause are rejected (nothing to discharge:
///    an acceptance over such a system would be minted with zero safety
///    clauses checked — the confirmed vacuous-problem laundering shape);
/// 2. ghost-pair-certificate models are rejected (different evidence class);
/// 3. empty models are rejected (different evidence class);
/// 4. the delegation runs under `catch_unwind`; any panic is a rejection.
///
/// Only `Ok(true)` from the full init + transition + query clause discharge
/// yields an accepted verdict, and that verdict echoes a domain-separated
/// fingerprint of the problem the discharge actually ran against.
///
/// Timeout discipline is the caller's: `config.solve_timeout` bounds the
/// validation solves exactly as it does for trust-mc-driver's call site
/// (`external_model_validation_config` defaults it to ay-chc's 30s validation
/// timeout when unset). Budget exhaustion surfaces as `Ok(false)` from the
/// validator, i.e. `InvariantNotInductive`-shaped rejection — fail-closed.
pub fn replay_chc_invariant(
    problem: &ChcProblem,
    model: &InvariantModel,
    config: &PdrConfig,
) -> ChcReplayVerdict {
    // Hard rejections FIRST.
    //
    // Problem vacuity precedes model classification: a system with no live
    // query clause supports NO invariant-strength acceptance for any model,
    // so it is rejected before the model is even looked at. NOTE: live
    // clauses only — ay's own `ChcProblem::validate` would also credit
    // `pruned_false_queries`, but a pruned query contributes zero clause
    // discharges and therefore does not count here.
    if !problem.clauses().iter().any(|clause| clause.is_query()) {
        return ChcReplayVerdict::rejected(ChcReplayRejection::NoQueryClause);
    }
    // U4 model-class gates — order matters: a ghost-pair model has
    // intentionally empty quantifier-free interpretations, so the certificate
    // check must precede the emptiness check to report the precise reason.
    if model.has_quantified_array_certificate() {
        return ChcReplayVerdict::rejected(ChcReplayRejection::GhostPairCertificate);
    }
    if model.is_empty() {
        return ChcReplayVerdict::rejected(ChcReplayRejection::EmptyModel);
    }

    // Contain panics from BOTH the fingerprint rendering and the delegated
    // validation. `AssertUnwindSafe` is sound here: on unwind the closure's
    // borrows are discarded along with the whole computation — the oracle
    // returns a rejection and nothing observed the possibly-broken state.
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let fingerprint = problem_fingerprint(problem);
        let validated = ay_chc::engines::validate_external_invariant_model(problem, model, config);
        (fingerprint, validated)
    }));

    match outcome {
        Err(_panic) => ChcReplayVerdict::rejected(ChcReplayRejection::ValidatorPanicked),
        Ok((_, Err(error))) => {
            ChcReplayVerdict::rejected(ChcReplayRejection::ValidatorErrored(error.to_string()))
        }
        Ok((_, Ok(false))) => {
            ChcReplayVerdict::rejected(ChcReplayRejection::InvariantNotInductive)
        }
        Ok((fingerprint, Ok(true))) => ChcReplayVerdict::accepted(fingerprint),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_chc::ChcParser;

    /// A trivially-safe monotone counter: `Inv(0)`, `Inv(x) -> Inv(x+1)`,
    /// `Inv(x) /\ x < 0 -> false`. PDR proves it with e.g. `Inv(x) == x >= 0`.
    /// Mirrors `prove_external_invariant_model_accepts_validated_model` in
    /// ay-chc's own `lib_tests.rs`.
    const SAFE_COUNTER_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    /// Same init/transition, but the query clause flips the bad state to
    /// `x >= 0` — which the safe counter's genuine invariant plainly does NOT
    /// exclude (the initial state x = 0 is already bad). Any model accepted
    /// for the safe counter must be rejected here: its query conjunct is
    /// effectively dropped/false for this system.
    const BAD_QUERY_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (>= x 0)) false)))
(check-sat)
"#;

    /// The safe counter WITHOUT its safety query: init + transition only.
    /// `verify_model_impl` would happily "accept" a model over this system
    /// with zero safety discharges — the confirmed vacuous-problem shape.
    const QUERY_FREE_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(check-sat)
"#;

    /// A declaration-only problem: ZERO clauses of any kind. The most extreme
    /// vacuous shape — the clause loop runs zero iterations.
    const CLAUSE_FREE_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(check-sat)
"#;

    /// The safe counter whose query's constraint conjoins `false`: the parser
    /// prunes the clause as trivially unreachable (`pruned_false_queries`),
    /// so ay's own `ChcProblem::validate` still passes — but zero query
    /// clauses remain to be discharged. The oracle must be stricter.
    const PRUNED_QUERY_SMT2: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0) false) false)))
(check-sat)
"#;

    fn pdr_config() -> PdrConfig {
        PdrConfig::default().with_max_frames(8).with_max_iterations(100)
    }

    /// Solve the safe counter with proof-grade PDR and return its GENUINE
    /// inductive invariant model (standing in for an externally-produced
    /// candidate). Uses the public `engines::solve_pdr_proof_from_str` entry —
    /// `PdrSolver::solve_problem` (the route ay-chc's own lib_tests take) is
    /// `pub(crate)`.
    fn genuine_safe_counter_model() -> (ChcProblem, InvariantModel) {
        let problem = ChcParser::parse(SAFE_COUNTER_SMT2).expect("fixture parses");
        let run = ay_chc::engines::solve_pdr_proof_from_str(SAFE_COUNTER_SMT2, pdr_config())
            .expect("PDR proof run should not error on the safe counter");
        let model = run
            .result
            .safe_invariant()
            .unwrap_or_else(|| panic!("expected PDR to prove the counter safe, got {run:?}"))
            .model()
            .clone();
        assert!(
            !model.is_empty(),
            "the safe counter needs a real (non-empty) invariant model"
        );
        (problem, model)
    }

    /// Vacuity guard, extreme shape: a clause-free problem (declarations
    /// only) must be rejected for ANY model — including a genuine non-empty
    /// one — because zero clauses would be discharged. This is the confirmed
    /// finding's probe (a).
    #[test]
    fn clause_free_problem_is_rejected() {
        let (_safe_problem, model) = genuine_safe_counter_model();
        let vacuous = ChcParser::parse(CLAUSE_FREE_SMT2).expect("fixture parses");
        assert_eq!(vacuous.clauses().len(), 0, "fixture must be clause-free");
        let verdict = replay_chc_invariant(&vacuous, &model, &pdr_config());
        assert!(!verdict.is_accepted());
        assert_eq!(verdict.problem_fingerprint(), None);
        assert_eq!(verdict.rejection(), Some(&ChcReplayRejection::NoQueryClause));
    }

    /// Vacuity guard, init+transition shape: a query-free problem must be
    /// rejected — a model "accepted" over it would have discharged no safety
    /// property. This is the confirmed finding's probe (b).
    #[test]
    fn query_free_problem_is_rejected() {
        let (_safe_problem, model) = genuine_safe_counter_model();
        let query_free = ChcParser::parse(QUERY_FREE_SMT2).expect("fixture parses");
        assert!(
            !query_free.clauses().is_empty(),
            "fixture must keep its init/transition clauses"
        );
        assert_eq!(
            query_free.queries().count(),
            0,
            "fixture must have no query clause"
        );
        let verdict = replay_chc_invariant(&query_free, &model, &pdr_config());
        assert!(!verdict.is_accepted());
        assert_eq!(verdict.problem_fingerprint(), None);
        assert_eq!(verdict.rejection(), Some(&ChcReplayRejection::NoQueryClause));
    }

    /// Vacuity guard, pruned-query shape: ay's parser prunes a query whose
    /// constraint simplifies to false and ay's own `ChcProblem::validate`
    /// still passes (`pruned_false_queries` credit). The oracle counts LIVE
    /// query clauses only — a pruned query contributes zero discharges, so
    /// the problem is rejected.
    #[test]
    fn pruned_query_problem_is_rejected() {
        let (_safe_problem, model) = genuine_safe_counter_model();
        let pruned = ChcParser::parse(PRUNED_QUERY_SMT2).expect("fixture parses");
        assert_eq!(
            pruned.queries().count(),
            0,
            "fixture's query must have been parser-pruned"
        );
        assert!(
            pruned.validate().is_ok(),
            "ay's own validate credits the pruned query — the oracle must be stricter"
        );
        let verdict = replay_chc_invariant(&pruned, &model, &pdr_config());
        assert!(!verdict.is_accepted());
        assert_eq!(verdict.problem_fingerprint(), None);
        assert_eq!(verdict.rejection(), Some(&ChcReplayRejection::NoQueryClause));
    }

    /// U4: an empty model must be rejected BEFORE any delegation — ay-chc
    /// would route it to the acyclic-exhaustive-BMC validator, a different
    /// evidence class.
    #[test]
    fn empty_model_is_rejected() {
        let problem = ChcParser::parse(SAFE_COUNTER_SMT2).expect("fixture parses");
        let verdict = replay_chc_invariant(&problem, &InvariantModel::new(), &pdr_config());
        assert!(!verdict.is_accepted());
        assert_eq!(verdict.problem_fingerprint(), None);
        assert_eq!(verdict.rejection(), Some(&ChcReplayRejection::EmptyModel));
    }

    /// U4: a ghost-pair-certificate model must be rejected. The sealed
    /// certificate is constructible only inside ay-chc
    /// (`GhostPairCertificate::certify_and_seal` and the model setter are
    /// `pub(crate)`), so this test pins the PUBLIC contract the oracle keys
    /// on instead: every externally-obtainable model answers the
    /// `has_quantified_array_certificate()` accessor the oracle consults, and
    /// a certificate-free model does not trip the ghost-pair rejection. The
    /// positive trip is unconstructible from outside ay-chc by design — the
    /// same sealing that makes the escape hatch narrow makes it untestable
    /// here (recorded caveat).
    #[test]
    fn ghost_pair_accessor_is_the_consulted_gate() {
        let (problem, model) = genuine_safe_counter_model();
        assert!(
            !model.has_quantified_array_certificate(),
            "a PDR-solved scalar model must not carry a ghost-pair certificate"
        );
        // And the certificate-free genuine model does NOT get the ghost-pair
        // (or empty-model, or no-query) rejection — it proceeds to the real
        // discharge.
        let verdict = replay_chc_invariant(&problem, &model, &pdr_config());
        assert!(verdict.is_accepted(), "got {verdict:?}");
    }

    /// Positive control: a GENUINE inductive invariant for a tiny problem is
    /// accepted, and the verdict echoes the domain-separated fingerprint of
    /// exactly that problem — deterministically.
    #[test]
    fn genuine_invariant_is_accepted_with_bound_fingerprint() {
        let (problem, model) = genuine_safe_counter_model();
        let verdict = replay_chc_invariant(&problem, &model, &pdr_config());
        assert!(verdict.is_accepted(), "got {verdict:?}");
        assert_eq!(verdict.rejection(), None);

        let fingerprint = verdict
            .problem_fingerprint()
            .expect("accepted verdict carries the fingerprint");
        assert_eq!(fingerprint.len(), 64, "sha256 lowercase hex");
        assert_eq!(fingerprint, problem_fingerprint(&problem));
        // Domain separation: NOT ay's own un-prefixed hash of the same text.
        assert_ne!(fingerprint, ay_chc::normalized_chc_input_sha256(&problem));

        // Determinism pin: replaying the same inputs yields the same verdict
        // and the same fingerprint.
        let again = replay_chc_invariant(&problem, &model, &pdr_config());
        assert!(again.is_accepted());
        assert_eq!(again.problem_fingerprint(), Some(fingerprint));
    }

    /// Negative control (the S3 FALSE-PROOF shape): the SAME genuine model is
    /// NOT inductive for a system whose query clause it does not exclude —
    /// the full clause discharge must reject it as InvariantNotInductive,
    /// never accept it under a different problem.
    #[test]
    fn wrong_invariant_is_rejected_not_inductive() {
        let (_safe_problem, model) = genuine_safe_counter_model();
        let bad_problem = ChcParser::parse(BAD_QUERY_SMT2).expect("fixture parses");
        let verdict = replay_chc_invariant(&bad_problem, &model, &pdr_config());
        assert!(!verdict.is_accepted());
        assert_eq!(verdict.problem_fingerprint(), None);
        assert_eq!(
            verdict.rejection(),
            Some(&ChcReplayRejection::InvariantNotInductive)
        );
    }

    /// The fingerprint binds the verdict to THE problem: two different
    /// problems fingerprint differently (so an accepted verdict for one can
    /// never hash-match a gate's re-derivation of the other).
    #[test]
    fn fingerprint_distinguishes_problems() {
        let safe = ChcParser::parse(SAFE_COUNTER_SMT2).expect("fixture parses");
        let bad = ChcParser::parse(BAD_QUERY_SMT2).expect("fixture parses");
        assert_ne!(problem_fingerprint(&safe), problem_fingerprint(&bad));
    }
}
