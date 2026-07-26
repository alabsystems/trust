// trust-router/carcara_cross_check.rs: N-version Alethe cross-check via Carcara.
//
// Trust: An independent second checker for ay's UNSAT proofs. ay already runs
// its own strict proof checker (see in_process_ay_backend::unsat_to_result); this
// module re-checks the same Alethe proof with Carcara, a SEPARATE, independently
// implemented Alethe checker (reachable as a library through clean-auto's
// `carcara-verify` feature). Combined, a false-PROVE would need the SAME bug to
// exist in BOTH ay's checker AND Carcara — N-version redundancy at the proof
// boundary.
//
// ## Soundness boundary (the one load-bearing rule)
//
// `carcara_cross_check` returns [`CrossCheck::Accept`] ONLY when:
//   1. the proof carries NO unreconstructed theory step (`:rule trust`,
//      `:rule hole`, or a `:rule la_generic` missing its Farkas `:args`), AND
//   2. ay reported ZERO residual trust steps (`trust_count == 0`), AND
//   3. Carcara fully verifies the proof (`Ok(true)` — no holes).
//
// In EVERY other case the result is [`CrossCheck::Reject`] (proof contains a
// trust/hole/holey-la_generic step, ay had residual trust, Carcara rejected, or
// Carcara errored), EXCEPT when the Carcara library is not compiled in, which is
// [`CrossCheck::Unavailable`]. The cross-check NEVER returns `Accept` for a proof
// containing an unreconstructed theory step — those are exactly the steps that
// would let an unsound proof pass a holey checker, so we refuse them up front
// rather than trusting Carcara to.
//
// The helper is wired into `in_process_ay_backend`'s live strict-checked UNSAT
// path when both `ay-backend` and `carcara-crosscheck` are enabled. Its gate is
// monotone: a rejection may downgrade `Proved` to `Unknown`; it never upgrades.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "carcara-crosscheck")]

use clean_auto::bridge::ay_contract::verify_alethe_proof;

/// Outcome of cross-checking an Alethe proof with the independent Carcara checker.
#[derive(Debug, PartialEq, Eq)]
pub enum CrossCheck {
    /// Carcara fully verified a trust-free proof with no residual ay trust steps.
    /// This is the only verdict that may strengthen a PROVE.
    Accept,
    /// The proof must NOT be trusted: it contains an unreconstructed theory step,
    /// ay reported residual trust, Carcara rejected it, or Carcara errored.
    Reject,
    /// The Carcara checker is not available (feature/path absent). The caller
    /// must fall back to ay's own verdict — this is never an `Accept`.
    Unavailable,
}

/// Detect whether an Alethe proof contains an UNRECONSTRUCTED theory step that a
/// holey checker would wave through.
///
/// Returns `true` (reject) for:
/// - `:rule trust` — ay's catch-all for theory lemmas it did not reconstruct
///   (BV bit-blast, arrays, strings).
/// - `:rule hole` — an explicit unchecked gap.
/// - `:rule la_generic` WITHOUT a `:args` clause — linear-arithmetic steps that
///   lack the Farkas coefficients Carcara needs, which clean-auto's bridge would
///   silently degrade to a `hole`. We reject the proof rather than let it degrade.
///
/// A `la_generic` step that DOES carry `:args` is genuine and not flagged here.
fn contains_unreconstructed_step(alethe: &str) -> bool {
    alethe.lines().any(|line| {
        line.contains(":rule trust")
            || line.contains(":rule hole")
            || (line.contains(":rule la_generic") && !line.contains(":args"))
    })
}

/// Independently cross-check an ay UNSAT refutation with Carcara.
///
/// See the module-level docs for the full soundness boundary. In brief: returns
/// [`CrossCheck::Reject`] immediately if `trust_count > 0` or the Alethe text
/// contains an unreconstructed theory step; otherwise defers to Carcara, mapping
/// a fully-verified proof to [`CrossCheck::Accept`], a holey/rejected proof to
/// [`CrossCheck::Reject`], and a missing checker to [`CrossCheck::Unavailable`].
///
/// # Arguments
/// * `problem_smt2` — the SMT-LIB2 problem (declarations + the asserted violation
///   formula + `(check-sat)`), exactly as exported to ay.
/// * `alethe` — the Alethe proof text ay produced for the UNSAT result.
/// * `trust_count` — the number of residual `trust` steps ay itself reported. Any
///   nonzero value means ay did not fully reconstruct the proof, so we refuse it.
#[must_use]
pub fn carcara_cross_check(problem_smt2: &str, alethe: &str, trust_count: u32) -> CrossCheck {
    // CARDINAL SOUNDNESS: fail closed BEFORE touching Carcara. A nonzero residual
    // trust count or any trust/hole/holey-la_generic step means the proof has an
    // unchecked gap that a holey checker (Carcara included, when allowed) would
    // wave through. These never earn an Accept.
    if trust_count > 0 {
        return CrossCheck::Reject;
    }
    if contains_unreconstructed_step(alethe) {
        return CrossCheck::Reject;
    }

    // The proof is structurally trust-free as far as we can tell. Re-check it with
    // the independent Carcara implementation.
    match verify_alethe_proof(problem_smt2, alethe) {
        // Carcara fully verified, no holes.
        Ok(true) => CrossCheck::Accept,
        // Carcara found a hole (e.g. a degraded la_generic) — do not trust.
        Ok(false) => CrossCheck::Reject,
        Err(err) => match err {
            // The carcara-verify feature is not compiled in: checker unavailable.
            // (This arm is reachable only if `clean-auto/carcara-verify` is off,
            // which the `carcara-crosscheck` feature should pull in — keep it as a
            // fail-safe so we degrade to Unavailable, never Accept.)
            clean_auto::bridge::ay_contract::VerifyError::CarcaraNotEnabled => {
                CrossCheck::Unavailable
            }
            // A parse/transport/checker error is NOT a verification success.
            // Fail closed to Reject — a proof Carcara cannot check is not one we
            // can independently vouch for.
            _ => CrossCheck::Reject,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A boolean contradiction `p AND (not p)`, the simplest trust-free UNSAT.
    fn bool_contradiction_problem() -> &'static str {
        "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n"
    }

    /// Genuine trust-free refutation of the boolean contradiction: assume both
    /// literals, resolve to the empty clause. Carcara verifies this with no holes.
    fn bool_contradiction_proof_resolution() -> String {
        "(assume t0 p)\n\
         (assume t1 (not p))\n\
         (step t2 (cl) :rule resolution :premises (t1 t0))\n"
            .to_string()
    }

    /// The same shape but with the contradiction discharged by an unchecked
    /// `trust` step — exactly the unsound pattern the cross-check must reject.
    fn bool_contradiction_proof_trust() -> String {
        "(assume t0 p)\n\
         (assume t1 (not p))\n\
         (step t2 (cl) :rule trust :premises (t1 t0))\n"
            .to_string()
    }

    /// (a) CRITICAL SOUNDNESS: a proof containing `:rule trust` must be Reject,
    /// even with `trust_count == 0` — the textual scan catches it before Carcara,
    /// because Carcara run with trust allowed would otherwise wave it through.
    #[test]
    fn proof_with_trust_rule_is_rejected() {
        let result =
            carcara_cross_check(bool_contradiction_problem(), &bool_contradiction_proof_trust(), 0);
        assert_eq!(
            result,
            CrossCheck::Reject,
            "an Alethe proof containing a `:rule trust` step must NEVER be accepted by the \
             cross-check — it is an unreconstructed theory hole"
        );
    }

    /// (b) A genuinely valid, trust-free Alethe proof of a simple UNSAT is Accept.
    #[test]
    fn valid_trust_free_proof_is_accepted() {
        let result = carcara_cross_check(
            bool_contradiction_problem(),
            &bool_contradiction_proof_resolution(),
            0,
        );
        assert_eq!(
            result,
            CrossCheck::Accept,
            "a complete, trust-free, Carcara-verified UNSAT refutation must be Accept"
        );
    }

    /// (c) A bogus / contradictory proof (claims the empty clause from a single,
    /// non-contradictory assumption) is Reject: Carcara cannot derive `(cl)` from
    /// `p` alone, so the resolution step does not check out.
    #[test]
    fn bogus_proof_is_rejected() {
        let problem = "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n";
        // No `(not p)` premise exists, yet the proof claims the empty clause.
        let bogus = "(assume t0 p)\n\
                     (step t1 (cl) :rule resolution :premises (t0))\n";
        let result = carcara_cross_check(problem, bogus, 0);
        assert_eq!(
            result,
            CrossCheck::Reject,
            "a proof whose resolution step does not actually derive the empty clause must be \
             Reject"
        );
    }

    /// Defense in depth: even a structurally trust-free proof is Reject when ay
    /// itself reported residual trust steps (`trust_count > 0`). We fail closed
    /// before ever invoking Carcara.
    #[test]
    fn nonzero_trust_count_is_rejected_even_for_clean_text() {
        let result = carcara_cross_check(
            bool_contradiction_problem(),
            &bool_contradiction_proof_resolution(),
            1,
        );
        assert_eq!(
            result,
            CrossCheck::Reject,
            "a nonzero ay residual trust_count must force Reject regardless of the proof text"
        );
    }

    /// `hole` and unargumented `la_generic` are also unreconstructed steps.
    #[test]
    fn hole_and_argless_la_generic_are_unreconstructed() {
        assert!(contains_unreconstructed_step("(step t1 (cl) :rule hole :premises (t0))"));
        assert!(contains_unreconstructed_step(
            "(step t1 (cl (not (> x 0))) :rule la_generic :premises (h1))"
        ));
        // la_generic WITH :args is genuine and not flagged.
        assert!(!contains_unreconstructed_step(
            "(step t1 (cl (not (> x 0))) :rule la_generic :args (1))"
        ));
        // A plain resolution step is not an unreconstructed step.
        assert!(!contains_unreconstructed_step(
            "(step t2 (cl) :rule resolution :premises (t1 t0))"
        ));
    }
}
