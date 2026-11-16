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
//   3. ay disclosed `carcara_surface = supported` for the document, AND
//   4. Carcara fully verifies the proof (`Ok(true)` — no holes).
//
// In EVERY other case the result is [`CrossCheck::Reject`] (proof contains a
// trust/hole/holey-la_generic step, ay had residual trust, Carcara rejected, or
// Carcara errored), EXCEPT when ay disclosed that pinned Carcara cannot parse
// the document ([`CrossCheck::SurfaceUnsupported`], carrying ay's reason — a
// `FloatingPoint`/`Seq`/`Char` sort or an escaped symbol spelling), and when the
// Carcara library is not compiled in ([`CrossCheck::Unavailable`]).
//
// `SurfaceUnsupported` (DECISION_QUEUE D7, 2026-09-22) is a REFUSAL, never an
// accept: this is a consumer that CLAIMS an external Carcara check, and no such
// check exists for a document Carcara cannot parse. Before D7 the same proof
// reached Carcara, failed to parse, and was a `Reject`; the verdict class is
// unchanged, only the refusal now names ay's disclosed cause instead of a parse
// error. The trust-count and unreconstructed-step checks stay AHEAD of it, so a
// holey document is refused as holey whatever its surface.
//
// The cross-check NEVER returns `Accept` for a proof
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
    /// ay disclosed `carcara_surface = unsupported(reason)`: pinned Carcara
    /// cannot parse this document (a `FloatingPoint`, `Seq` or `Char` sort, or a
    /// symbol needing the AY/Z3 escape extension), so no external re-check
    /// exists. A consumer claiming the cross-check must refuse it — this is
    /// NEVER an `Accept`, and unlike [`CrossCheck::Unavailable`] it is not a
    /// pass-through either: the checker is present, the document is outside it.
    /// DECISION_QUEUE D7 (2026-09-22).
    SurfaceUnsupported {
        /// ay's disclosed cause, verbatim, for the refusal message.
        reason: String,
    },
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
/// * `unsupported_surface` — `Some(reason)` when ay disclosed
///   `carcara_surface = unsupported(reason)` for this document (D7), `None` when
///   it disclosed `supported`. A caller that cannot tell (a surface variant it
///   does not know) must pass `Some`, never `None`: the enum is
///   `#[non_exhaustive]` and an unknown variant is unsupported, not checked.
#[must_use]
pub fn carcara_cross_check(
    problem_smt2: &str,
    alethe: &str,
    trust_count: u32,
    unsupported_surface: Option<&str>,
) -> CrossCheck {
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
    // D7: ay rendered this document for a surface pinned Carcara cannot parse.
    // No external check exists, so refuse by NAME rather than let Carcara's
    // parser produce the same refusal as an anonymous error.
    if let Some(reason) = unsupported_surface {
        return CrossCheck::SurfaceUnsupported { reason: reason.to_string() };
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
        let result = carcara_cross_check(
            bool_contradiction_problem(),
            &bool_contradiction_proof_trust(),
            0,
            None,
        );
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
            None,
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
        let result = carcara_cross_check(problem, bogus, 0, None);
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
            None,
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

    /// D7 (2026-09-22): ay disclosed `carcara_surface = unsupported(reason)`.
    /// The otherwise-clean document is refused BY NAME, never Accept — and the
    /// refusal happens before Carcara is asked, so it holds with or without a
    /// Carcara that could have parsed it.
    #[test]
    fn unsupported_surface_is_refused_by_name_never_accepted() {
        let reason = "sort `(_ FloatingPoint 8 24)` is outside pinned Carcara's grammar";
        let result = carcara_cross_check(
            bool_contradiction_problem(),
            &bool_contradiction_proof_resolution(),
            0,
            Some(reason),
        );
        assert_eq!(
            result,
            CrossCheck::SurfaceUnsupported { reason: reason.to_string() },
            "a disclosed-unsupported surface must be refused with ay's reason, not accepted \
             (the same clean text with `None` is Accept — see `valid_trust_free_proof_is_accepted`)"
        );
        assert_ne!(result, CrossCheck::Accept);
        assert_ne!(result, CrossCheck::Unavailable, "the checker is present; the surface is not");
    }

    // Clean Carcara fixes 36-40 (Clean b0a2d570a; third-party/carcara/DOWNSTREAM.md).
    // Each problem below is SATISFIABLE (AY 0.27.0 is the oracle Clean measured
    // against), yet the paired proof is one a checker that misreads the script
    // would accept: a Clean whose vendored Carcara predates the fixes certified
    // all four. Copies of Clean's fixtures in
    // crates/clean-auto/src/bridge/ay_backend/carcara_verify/soundness/, kept
    // inline so a later pin cannot weaken the guard by editing them. A pin move
    // that drops the fixes turns these red (docs/first-party-pin-ledger.md).

    /// `pr_u1_define_fun_capture`: `define-fun` expansion must be hygienic. The
    /// parameter `x` of `h` must not capture the global `x` that `k` names, so
    /// `(h 5)` is `x`, not `5`, and the script is satisfiable.
    const PR_U1_DEFINE_FUN_CAPTURE_SMT2: &str = "(set-logic ALL)\n\
        (declare-fun x () Int)\n\
        (define-fun k () Int x)\n\
        (define-fun h ((x Int)) Int k)\n\
        (assert (= (h 5) x))\n\
        (assert (not (= x 5)))\n\
        (check-sat)\n";
    const PR_U1_DEFINE_FUN_CAPTURE_ALETHE: &str = "(assume a0 (= (h 5) x))\n\
        (assume a1 (not (= x 5)))\n\
        (step t1 (cl (= x 5)) :rule symm :premises (a0))\n\
        (step t2 (cl) :rule resolution :premises (a1 t1))\n";

    /// `pr_u14_two_check_sats`: the first `check-sat` sees only `p`. A checker
    /// that pools every assertion of the script refutes a query nobody asked.
    const PR_U14_TWO_CHECK_SATS_SMT2: &str = "(set-logic ALL)\n\
        (declare-fun p () Bool)\n\
        (assert p)\n\
        (check-sat)\n\
        (assert (not p))\n\
        (check-sat)\n";
    const PR_U14_TWO_CHECK_SATS_ALETHE: &str = "(assume a0 p)\n\
        (assume a1 (not p))\n\
        (step t1 (cl) :rule resolution :premises (a0 a1))\n";

    /// `pr_u17_pop`: `(not p)` is popped before the `check-sat`, so only `p` is
    /// asserted. A checker that ignores `push`/`pop` keeps it as a premise.
    const PR_U17_POP_SMT2: &str = "(set-logic ALL)\n\
        (declare-fun p () Bool)\n\
        (push 1)\n\
        (assert (not p))\n\
        (pop 1)\n\
        (assert p)\n\
        (check-sat)\n";
    const PR_U17_POP_ALETHE: &str = "(assume a0 p)\n\
        (assume a1 (not p))\n\
        (step t1 (cl) :rule resolution :premises (a0 a1))\n";

    /// `pr_u31_recursive_definition_inconsistent`: SMT-LIB gives
    /// `define-fun-rec` a least-fixpoint meaning, not the equation as an axiom;
    /// read as an axiom, `f x = f x + 1` is inconsistent and proves anything.
    const PR_U31_RECURSIVE_DEFINITION_SMT2: &str = "(set-logic UFLIA)\n\
        (define-fun-rec f ((x Int)) Int (+ (f x) 1))\n\
        (check-sat)\n";
    const PR_U31_RECURSIVE_DEFINITION_ALETHE: &str = "(assume a0 (forall ((x Int)) (= (f x) (+ (f x) 1))))\n\
        (step t1 (cl (or (not (forall ((x Int)) (= (f x) (+ (f x) 1)))) (= (f 0) (+ (f 0) 1)))) :rule forall_inst :args (0))\n\
        (step t2 (cl (not (forall ((x Int)) (= (f x) (+ (f x) 1)))) (= (f 0) (+ (f 0) 1))) :rule or :premises (t1))\n\
        (step t3 (cl (= (f 0) (+ (f 0) 1))) :rule resolution :premises (t2 a0))\n\
        (step t4 (cl (not (= (f 0) (+ (f 0) 1)))) :rule la_generic :args (1))\n\
        (step t5 (cl) :rule resolution :premises (t3 t4))\n";

    /// `ok_pr_hygienic_define_fun`, the control: the same definitions as
    /// `pr_u1`, read hygienically, make `(h 5)` equal `x`, so this script IS
    /// unsatisfiable and its proof must still be accepted.
    const OK_PR_HYGIENIC_DEFINE_FUN_SMT2: &str = "(set-logic ALL)\n\
        (declare-fun x () Int)\n\
        (define-fun k () Int x)\n\
        (define-fun h ((x Int)) Int k)\n\
        (assert (not (= (h 5) x)))\n\
        (check-sat)\n";
    const OK_PR_HYGIENIC_DEFINE_FUN_ALETHE: &str = "(assume a0 (not (= (h 5) x)))\n\
        (step t1 (cl (= x x)) :rule refl)\n\
        (step t2 (cl) :rule resolution :premises (a0 t1))\n";

    fn assert_satisfiable_script_rejected(name: &str, problem: &str, proof: &str) {
        assert!(
            !contains_unreconstructed_step(proof),
            "{name}: the proof must reach Carcara, not be refused by the textual scan"
        );
        assert_eq!(
            carcara_cross_check(problem, proof, 0, None),
            CrossCheck::Reject,
            "{name}: the problem is SATISFIABLE, so no refutation of it may be accepted; \
             the pinned Clean's Carcara lacks fixes 36-40 (Clean b0a2d570a)"
        );
    }

    #[test]
    fn define_fun_capture_is_rejected() {
        assert_satisfiable_script_rejected(
            "pr_u1_define_fun_capture",
            PR_U1_DEFINE_FUN_CAPTURE_SMT2,
            PR_U1_DEFINE_FUN_CAPTURE_ALETHE,
        );
    }

    #[test]
    fn two_check_sats_are_rejected() {
        assert_satisfiable_script_rejected(
            "pr_u14_two_check_sats",
            PR_U14_TWO_CHECK_SATS_SMT2,
            PR_U14_TWO_CHECK_SATS_ALETHE,
        );
    }

    #[test]
    fn popped_assertion_is_rejected() {
        assert_satisfiable_script_rejected("pr_u17_pop", PR_U17_POP_SMT2, PR_U17_POP_ALETHE);
    }

    #[test]
    fn recursive_definition_read_as_axiom_is_rejected() {
        assert_satisfiable_script_rejected(
            "pr_u31_recursive_definition_inconsistent",
            PR_U31_RECURSIVE_DEFINITION_SMT2,
            PR_U31_RECURSIVE_DEFINITION_ALETHE,
        );
    }

    // AY's r18 cross-review (2026-10-07; Clean 63e5215f3, the
    // `soundness/bs_u_*` fixtures). Each problem gives a user symbol a built-in
    // operator's spelling at the built-in's own arity (a `declare-fun`,
    // `define-fun`, datatype constructor, or the constant `|false|`), and each
    // proof refutes it with `evaluate`, which is sound only if the symbol IS the
    // built-in. Under SMT-LIB every one is ill-formed or satisfiable. Clean
    // 6a916983's Carcara fully verified these fifteen; fix 38 (a60db73bb) refuses
    // the declaration while reading the problem. Inline copies, byte-equal to
    // Clean's fixtures, so a later pin cannot weaken the guard by editing them.
    const R18_BUILTIN_SPELLINGS: [(&str, &str, &str); 15] = [
        (
            "bs_u_c05_dt_ctor_and",
            r#"(set-logic ALL)
(declare-datatypes ((D 0)) (((and (aa Bool) (ab Bool)))))
(assert (not (= (and true false) (and false true))))
(check-sat)
"#,
            r#"(assume a0 (not (= (and true false) (and false true))))
(step t1 (cl (= (not (= (and true false) (and false true))) false)) :rule evaluate)
(step t2 (cl (not (= (not (= (and true false) (and false true))) false)) (not (not (= (and true false) (and false true)))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_c14_dt_ctor_plus",
            r#"(set-logic ALL)
(declare-datatypes ((D 0)) (((+ (pa Int) (pb Int)))))
(assert (not (= (+ 1 0) (+ 0 1))))
(check-sat)
"#,
            r#"(assume a0 (not (= (+ 1 0) (+ 0 1))))
(step t1 (cl (= (not (= (+ 1 0) (+ 0 1))) false)) :rule evaluate)
(step t2 (cl (not (= (not (= (+ 1 0) (+ 0 1))) false)) (not (not (= (+ 1 0) (+ 0 1)))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_c15_definefun_plus",
            r#"(set-logic ALL)
(define-fun + ((x Int) (y Int)) Int 7)
(assert (= (+ 1 1) 7))
(check-sat)
"#,
            r#"(assume a0 (= (+ 1 1) 7))
(step t1 (cl (= (= (+ 1 1) 7) false)) :rule evaluate)
(step t2 (cl (not (= (= (+ 1 1) 7) false)) (not (= (+ 1 1) 7)) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_c16_dt_ctor_bvadd",
            r#"(set-logic ALL)
(declare-datatypes ((D 0)) (((bvadd (pa (_ BitVec 2)) (pb (_ BitVec 2))))))
(assert (not (= (bvadd #b01 #b00) (bvadd #b00 #b01))))
(check-sat)
"#,
            r#"(assume a0 (not (= (bvadd #b01 #b00) (bvadd #b00 #b01))))
(step t1 (cl (= (not (= (bvadd #b01 #b00) (bvadd #b00 #b01))) false)) :rule evaluate)
(step t2 (cl (not (= (not (= (bvadd #b01 #b00) (bvadd #b00 #b01))) false)) (not (not (= (bvadd #b01 #b00) (bvadd #b00 #b01)))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d20_declfun_plus",
            r#"(set-logic ALL)
(declare-fun + (Int Int) Int)
(assert (= (+ 1 1) 7))
(check-sat)
"#,
            r#"(assume a0 (= (+ 1 1) 7))
(step t1 (cl (= (= (+ 1 1) 7) false)) :rule evaluate)
(step t2 (cl (not (= (= (+ 1 1) 7) false)) (not (= (+ 1 1) 7)) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d21_declfun_and2",
            r#"(set-logic ALL)
(declare-fun and (Bool Bool) Bool)
(assert (not (and true true)))
(check-sat)
"#,
            r#"(assume a0 (not (and true true)))
(step t1 (cl (= (not (and true true)) false)) :rule evaluate)
(step t2 (cl (not (= (not (and true true)) false)) (not (not (and true true))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d24_definefun_minus",
            r#"(set-logic ALL)
(define-fun - ((a Int) (b Int)) Int 7)
(assert (= (- 1 1) 7))
(check-sat)
"#,
            r#"(assume a0 (= (- 1 1) 7))
(step t1 (cl (= (= (- 1 1) 7) false)) :rule evaluate)
(step t2 (cl (not (= (= (- 1 1) 7) false)) (not (= (- 1 1) 7)) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d25_declfun_le",
            r#"(set-logic ALL)
(declare-fun <= (Int Int) Bool)
(assert (not (<= 0 1)))
(check-sat)
"#,
            r#"(assume a0 (not (<= 0 1)))
(step t1 (cl (= (not (<= 0 1)) false)) :rule evaluate)
(step t2 (cl (not (= (not (<= 0 1)) false)) (not (not (<= 0 1))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d26_definefun_or",
            r#"(set-logic ALL)
(define-fun or ((a Bool) (b Bool)) Bool false)
(assert (not (or true true)))
(check-sat)
"#,
            r#"(assume a0 (not (or true true)))
(step t1 (cl (= (not (or true true)) false)) :rule evaluate)
(step t2 (cl (not (= (not (or true true)) false)) (not (not (or true true))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d27_dtctor_or",
            r#"(set-logic ALL)
(declare-datatypes ((D 0)) (((or (oa Bool) (ob Bool)))))
(assert (not (= (or true false) (or false true))))
(check-sat)
"#,
            r#"(assume a0 (not (= (or true false) (or false true))))
(step t1 (cl (= (not (= (or true false) (or false true))) false)) :rule evaluate)
(step t2 (cl (not (= (not (= (or true false) (or false true))) false)) (not (not (= (or true false) (or false true)))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d28_definefun_xor",
            r#"(set-logic ALL)
(define-fun xor ((a Bool) (b Bool)) Bool true)
(assert (xor true true))
(check-sat)
"#,
            r#"(assume a0 (xor true true))
(step t1 (cl (= (xor true true) false)) :rule evaluate)
(step t2 (cl (not (= (xor true true) false)) (not (xor true true)) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d29_definefun_ite3",
            r#"(set-logic ALL)
(define-fun ite ((c Bool) (a Int) (b Int)) Int 5)
(assert (= (ite true 0 1) 5))
(check-sat)
"#,
            r#"(assume a0 (= (ite true 0 1) 5))
(step t1 (cl (= (= (ite true 0 1) 5) false)) :rule evaluate)
(step t2 (cl (not (= (= (ite true 0 1) 5) false)) (not (= (ite true 0 1) 5)) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d30_declfun_ite3",
            r#"(set-logic ALL)
(declare-fun ite (Bool Int Int) Int)
(assert (= (ite true 0 1) 5))
(check-sat)
"#,
            r#"(assume a0 (= (ite true 0 1) 5))
(step t1 (cl (= (= (ite true 0 1) 5) false)) :rule evaluate)
(step t2 (cl (not (= (= (ite true 0 1) 5) false)) (not (= (ite true 0 1) 5)) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_d31_definefun_eq2",
            r#"(set-logic ALL)
(define-fun = ((a Int) (b Int)) Bool false)
(assert (not (= 0 0)))
(check-sat)
"#,
            r#"(assume a0 (not (= 0 0)))
(step t1 (cl (= (not (= 0 0)) false)) :rule evaluate)
(step t2 (cl (not (= (not (= 0 0)) false)) (not (not (= 0 0))) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
        (
            "bs_u_e01_declconst_quoted_false",
            r#"(set-logic ALL)
(declare-const |false| Bool)
(assert |false|)
(check-sat)
"#,
            r#"(assume a0 |false|)
(step t1 (cl (= |false| false)) :rule evaluate)
(step t2 (cl (not (= |false| false)) (not |false|) false) :rule equiv_pos2)
(step t3 (cl (not false)) :rule false)
(step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))
"#,
        ),
    ];

    // Script commands a checker must read as SMT-LIB does (Clean fixes 36-38,
    // 4993e9d5c): `push`/`pop`, `reset`, `reset-assertions`, an `assert` after
    // `check-sat`, after `exit` or after `check-sat-assuming`. Each problem's
    // query (or the first one) is satisfiable, yet the proof pools assertions
    // the query never sees. Clean 6a916983 fully verified all six.
    const SCRIPT_COMMANDS_MISREAD: [(&str, &str, &str); 6] = [
        (
            "pr_u9_push_pop",
            r#"(set-logic QF_UF)
(declare-const p Bool)
(push 1)
(assert (and p (not p)))
(pop 1)
(check-sat)
"#,
            r#"(assume h (and p (not p)))
(step t1 (cl p) :rule and :premises (h) :args (0))
(step t2 (cl (not p)) :rule and :premises (h) :args (1))
(step t3 (cl) :rule resolution :premises (t1 t2))
"#,
        ),
        (
            "pr_u18_reset",
            r#"(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(reset)
(set-logic ALL)
(declare-fun p () Bool)
(assert (not p))
(check-sat)
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
        (
            "pr_u7_reset_assertions",
            r#"(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(reset-assertions)
(assert (not p))
(check-sat)
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
        (
            "pr_u15_assert_after_check_sat",
            r#"(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(check-sat)
(assert (not p))
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
        (
            "pr_u16_assert_after_exit",
            r#"(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(exit)
(assert (not p))
(check-sat)
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
        (
            "pr_u8_check_sat_assuming_then_assert",
            r#"(set-logic ALL)
(declare-fun p () Bool)
(check-sat-assuming (p))
(assert (not p))
(check-sat)
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
    ];

    // Controls for the table above: commands after the one `check-sat`, and a
    // `check-sat-assuming` whose assumption is the refuted premise, are UNSAT
    // as written and must still be accepted, so the refusals above cannot pass
    // on a checker that refuses every script with a second command in it.
    const SCRIPT_COMMANDS_CONTROLS: [(&str, &str, &str); 2] = [
        (
            "ok_pr_commands_after_check_sat",
            r#"(set-option :produce-models true)
(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(assert (not p))
(check-sat)
(get-value (p))
(get-model)
(exit)
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
        (
            "ok_pr_check_sat_assuming",
            r#"(set-logic ALL)
(declare-fun p () Bool)
(assert p)
(check-sat-assuming ((not p)))
"#,
            r#"(assume a0 p)
(assume a1 (not p))
(step t1 (cl) :rule resolution :premises (a0 a1))
"#,
        ),
    ];

    #[test]
    fn r18_builtin_spellings_are_rejected() {
        for (name, problem, proof) in R18_BUILTIN_SPELLINGS {
            assert_satisfiable_script_rejected(name, problem, proof);
        }
    }

    #[test]
    fn misread_script_commands_are_rejected() {
        for (name, problem, proof) in SCRIPT_COMMANDS_MISREAD {
            assert_satisfiable_script_rejected(name, problem, proof);
        }
    }

    #[test]
    fn script_command_controls_are_accepted() {
        for (name, problem, proof) in SCRIPT_COMMANDS_CONTROLS {
            assert_eq!(
                carcara_cross_check(problem, proof, 0, None),
                CrossCheck::Accept,
                "{name} is UNSAT as written and must be Accept"
            );
        }
    }

    /// The control keeps the four rejections above from passing vacuously
    /// (a checker that rejects everything would pass them).
    #[test]
    fn hygienic_define_fun_control_is_accepted() {
        assert_eq!(
            carcara_cross_check(
                OK_PR_HYGIENIC_DEFINE_FUN_SMT2,
                OK_PR_HYGIENIC_DEFINE_FUN_ALETHE,
                0,
                None,
            ),
            CrossCheck::Accept,
            "ok_pr_hygienic_define_fun is UNSAT under hygienic expansion and must be Accept"
        );
    }

    /// The trust-count and unreconstructed-step refusals stay AHEAD of the
    /// surface refusal: a holey document is refused as holey whatever its
    /// surface, so the surface disclosure can never mask a `:rule hole`.
    #[test]
    fn holey_document_is_refused_as_holey_before_its_surface_is_read() {
        let reason = "sort `Seq` is outside pinned Carcara's grammar";
        assert_eq!(
            carcara_cross_check(
                bool_contradiction_problem(),
                &bool_contradiction_proof_trust(),
                0,
                Some(reason),
            ),
            CrossCheck::Reject,
        );
        assert_eq!(
            carcara_cross_check(
                bool_contradiction_problem(),
                &bool_contradiction_proof_resolution(),
                1,
                Some(reason),
            ),
            CrossCheck::Reject,
        );
    }
}
