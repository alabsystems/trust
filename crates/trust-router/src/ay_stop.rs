// trust-router/ay_stop.rs: ay's own account of an `unknown`, mapped onto the
// Trust stop-cause vocabulary (`trust_types::determinism::StopCause`).
//
// Plan: docs/design/2026-09-29-incremental-deterministic-trust-results.md §3.2
// and §3.7. ay already knows WHY a check-sat ended undecided: a typed
// `UnknownReason` (in-process, `SolveDetails::unknown_reason` and its stable
// `code()`), and the same reason in the statistics block of the SMT-LIB lane
// (`:unknown.reason` in `(get-info :all-statistics)`). Before this module the
// router threw that away and wrote "solver returned unknown", so a conflict-
// budget stop and a wall-clock stop were the same row.
//
// Why the statistics block and not `(get-info :reason-unknown)`: the subprocess
// lane runs ay with `--z3-mode`, whose reason-unknown answer folds `timeout`,
// `resourceout`, `memout` and `interrupted` into Z3's single "canceled"
// (ay `crates/ay/src/run.rs`, `z3_reason_unknown_output`). The statistics block
// keeps ay's native token, which is the one that separates a count from a clock.
//
// Named stops (`StopItem`, the plan critique's P1 ledger items, 2026-09-30): a
// few of ay's refusals share one code — the certification funnel's
// `self_check_rejected` covers a strict check the caller's stop signal
// cancelled (a clock), an unverified trust rule, a strict-mode `Generic` lemma,
// an exhausted proof-check envelope and a spent certification effort — and a
// SAT answer whose model failed validation reads as a plain `incomplete`. ay's wording (the diagnostic
// detail, `:unknown.detail`) tells them apart; `AyStop` carries the name beside
// the cause so the tally and the ledger count each one.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::VerificationResult;
use trust_types::determinism::{Reproducibility, StopCause, StopItem};

/// The original undecided verdict after a retry lane that did NOT decide it —
/// the disjoint-component refutation, the sound nonlinear relaxation — on
/// either ay lane.
///
/// A retry that stopped for a DETERMINISTIC reason (an effort budget, a
/// component that is UNSAT, an unsupported shape) leaves `original` exactly as
/// it was. A retry that stopped on a clock, a fault or an unexplained stop is
/// folded into `original` ([`StopCause::stamp`], which keeps the less
/// reproducible cause): whether the retry would have decided the VC depended on
/// that stop, so the row is not reproducible whatever the first attempt said.
/// A `Timeout` original is already a clock and stays as it is.
pub(crate) fn after_undecided_retry(
    original: VerificationResult,
    retry_stop: StopCause,
    retry: &str,
) -> VerificationResult {
    match original {
        VerificationResult::Unknown { solver, time_ms, reason }
            if retry_stop.reproducibility() != Reproducibility::Deterministic =>
        {
            VerificationResult::Unknown {
                solver,
                time_ms,
                reason: retry_stop.stamp(&format!("{reason}; the {retry} stopped on {retry_stop}")),
            }
        }
        other => other,
    }
}

/// ay's certification-funnel refusals: a computed verdict withheld because its
/// proof could not be certified (`self_check_rejected`) or still carries trust
/// steps (`proof_trusted`). Both are decided after ay's deferred-clause
/// discharge. Since P4a.1 (ay ffaba97f6, `crates/ay-dpll/src/api/proofs.rs`,
/// Trust's pin) that discharge draws its nested solves from the solved query's
/// own effort count (`CertificationEffort`) and installs no clock, and a stop
/// that ended it — an interrupt, a deadline, a memory ceiling — is published
/// as that stop (`interrupted`, `timeout`, `memory_limit`), never under these
/// codes. So a refusal is the proof's: `solver-incomplete`, refined by the
/// named stop its wording states (a spent certification effort is `effort`; a
/// strict check a stop cancelled mid-walk stays `wall-backstop`).
#[cfg(any(test, feature = "ay-backend"))]
const CERTIFICATION_REFUSAL_CODES: [&str; 2] = ["self_check_rejected", "proof_trusted"];

/// The native tokens of the same two refusals (`UnknownReason` `Display`).
const CERTIFICATION_REFUSAL_TOKENS: [&str; 2] =
    ["(incomplete self-check-rejected)", "(incomplete proof-trusted)"];

/// The phrase ay's executor writes into the `MemoryLimit` diagnostic when the
/// per-executor term-store ceiling (a count of TermStore bytes, not RSS) is what
/// tripped (ay `executor/check_sat.rs`, the theory-loop memory checkpoint).
const TERM_STORE_CEILING_PHRASE: &str = "term-store memory ceiling";

/// Stop cause of ay's stable `UnknownReason::code()` (the in-process lane).
///
/// `detail` is ay's `UnknownDiagnostic::detail`, consulted only to tell the
/// term-store ceiling (a count) from a process-memory ceiling (an RSS reading),
/// which share the `memory_limit` code.
#[cfg(any(test, feature = "ay-backend"))]
#[must_use]
pub(crate) fn stop_cause_of_ay_code(code: &str, detail: Option<&str>) -> StopCause {
    match code {
        "resource_limit" => StopCause::Effort,
        // A wall-clock deadline, or an interrupt someone raised on a clock.
        "timeout" | "interrupted" => StopCause::WallBackstop,
        "memory_limit" => memory_stop(detail),
        _ if CERTIFICATION_REFUSAL_CODES.contains(&code) => StopCause::SolverIncomplete,
        "incomplete"
        | "quantifier_round_limit"
        | "quantifier_deferred"
        | "quantifier_unhandled"
        | "quantifier_cegqi_incomplete"
        | "quantifier_ematching_exists_incomplete"
        | "split_limit"
        | "expression_split" => StopCause::SolverIncomplete,
        "unsupported" | "unsupported_arithmetic" | "unsupported_mixed_collection" => {
            StopCause::Unsupported
        }
        "internal_error" => StopCause::SolverFault,
        // `unknown` is ay's own "no specific reason"; anything newer than this
        // table is not guessed at.
        _ => StopCause::Unclassified,
    }
}

/// Stop cause of ay's native reason TOKEN — its `UnknownReason` `Display`, the
/// value of `:unknown.reason` in the statistics block (`resourceout`,
/// `timeout`, `memout`, `(incomplete quantifier-cegqi)`, …).
#[must_use]
pub(crate) fn stop_cause_of_ay_token(token: &str, detail: Option<&str>) -> StopCause {
    let token = token.trim().trim_matches('"').trim();
    // The certification refusals (`CERTIFICATION_REFUSAL_TOKENS`) are
    // `(incomplete …)` tokens, and `solver-incomplete` like every other.
    match token {
        "resourceout" => StopCause::Effort,
        "timeout" | "interrupted" => StopCause::WallBackstop,
        "memout" => memory_stop(detail),
        "incomplete" => StopCause::SolverIncomplete,
        "unsupported" => StopCause::Unsupported,
        "internal-error" => StopCause::SolverFault,
        _ if token.starts_with("(incomplete") => StopCause::SolverIncomplete,
        _ if token.starts_with("(unsupported") => StopCause::Unsupported,
        // `unknown`, Z3-mode's `canceled` (which folds a count and a clock
        // together) and anything newer: not guessed at.
        _ => StopCause::Unclassified,
    }
}

/// A stop as ay stated it: the cause, and the named stop ([`StopItem`]) its
/// wording identifies, if any.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct AyStop {
    /// What ended the search.
    pub(crate) cause: StopCause,
    /// The named stop, when ay's wording is one Trust counts by name.
    pub(crate) item: Option<StopItem>,
}

impl AyStop {
    /// `cause`, refined by the first named stop any of `texts` identifies
    /// ([`stop_item_of_ay_text`]).
    ///
    /// Only a cause that leaves the stop unexplained or generic —
    /// `unclassified` (ay's `unknown`), `solver-incomplete` (ay's
    /// `self_check_rejected` and `proof_trusted` among them), `solver-fault` —
    /// is refined, and it is refined by [`StopCause::combine`], so naming an
    /// item never makes a stop more reproducible. A direct statement (effort, a clock, memory, unsupported)
    /// stands, unnamed: its wording is ay's account of THAT bound.
    pub(crate) fn from_texts(cause: StopCause, texts: &[Option<&str>]) -> Self {
        let refinable = matches!(
            cause,
            StopCause::Unclassified | StopCause::SolverIncomplete | StopCause::SolverFault
        );
        let item = texts.iter().flatten().find_map(|text| stop_item_of_ay_text(text));
        match item {
            Some(item) if refinable => {
                Self { cause: StopCause::combine(cause, item.cause()), item: Some(item) }
            }
            _ => Self { cause, item: None },
        }
    }

    /// `detail`, stamped with this stop (and its item).
    pub(crate) fn stamp(self, detail: &str) -> String {
        match self.item {
            Some(item) => self.cause.stamp_item(item, detail),
            None => self.cause.stamp(detail),
        }
    }

    /// An `Unknown` result that ended for this stop.
    pub(crate) fn unknown_result(
        self,
        solver: &str,
        time_ms: u64,
        detail: &str,
    ) -> VerificationResult {
        VerificationResult::Unknown { solver: solver.into(), time_ms, reason: self.stamp(detail) }
    }
}

/// [`stop_cause_of_ay_code`], refined by the named stop ay's wording states.
#[cfg(any(test, feature = "ay-backend"))]
pub(crate) fn ay_stop_of_code(code: &str, texts: &[Option<&str>]) -> AyStop {
    let detail = texts.iter().flatten().next().copied();
    AyStop::from_texts(stop_cause_of_ay_code(code, detail), texts)
}

/// [`stop_cause_of_ay_token`], refined by the named stop ay's wording states.
pub(crate) fn ay_stop_of_token(token: &str, detail: Option<&str>) -> AyStop {
    AyStop::from_texts(stop_cause_of_ay_token(token, detail), &[detail, Some(token)])
}

/// ay's wording of a strict proof check the caller's stop signal cancelled
/// (ay `ProofCheckError::Cancelled`, `crates/ay-proof/src/checker/error.rs`).
const STRICT_CHECK_CANCELLED_PHRASE: &str = "proof validation cancelled by the caller";

/// ay's wording of the count envelope a strict proof check exhausted (ay
/// `ProofCheckError::ResourceLimit`).
const PROOF_CHECK_ENVELOPE_PHRASE: &str = "proof validation resource envelope exhausted";

/// ay's wording of a strict-mode proof step that is an unverified trust rule
/// (ay `ProofCheckError`, "step {step} uses unverified trust rule").
const UNVERIFIED_TRUST_RULE_PHRASE: &str = "uses unverified trust rule";

/// ay's wording of a strict-mode `Generic` theory lemma ("step {step} uses
/// unsupported theory lemma kind Generic in strict mode").
const GENERIC_THEORY_LEMMA_PHRASE: &str = "unsupported theory lemma kind Generic";

/// ay's wording of a deferred-trust discharge that spent the effort it draws
/// from the solved query's count ("certification effort exhausted (spent S of
/// A)", ay `api/proofs/certification_effort.rs`, P4a.1).
const CERTIFICATION_EFFORT_PHRASE: &str = "certification effort exhausted";

/// ay's wording of a SAT model that failed validation (ay-dpll
/// `model/validation/pipeline.rs`, "model validation violated: …").
const MODEL_VALIDATION_PHRASE: &str = "model validation violated";

/// ay's native-replay refusal of an UNSAT without strict proof authority (ay
/// `api/solving/native_replay.rs`, `require_native_replay_proof_authority`).
const NATIVE_REPLAY_REFUSAL_PHRASE: &str = "UNSAT replay lacks strict proof authority";

/// The named stop ay's wording identifies, if it is one Trust counts by name
/// (plan-critique P1 ledger items, 2026-09-30). The phrases are ay's own error
/// texts at Trust's ay pin (da447f9a6, unchanged since ffaba97f6); a phrase ay
/// rewords stops matching and the stop falls back to its unnamed cause, never
/// to a wrong name.
///
/// A spent certification effort is read before the trust rule it leaves: ay
/// appends it to the refusal of the clause the discharge could not finish, and
/// the count, not the proof, is why that clause stayed a trust step.
pub(crate) fn stop_item_of_ay_text(text: &str) -> Option<StopItem> {
    if text.contains(STRICT_CHECK_CANCELLED_PHRASE) || native_replay_checked_every_step(text) {
        Some(StopItem::StrictCheckCancelled)
    } else if text.contains(CERTIFICATION_EFFORT_PHRASE) {
        Some(StopItem::CertificationEffort)
    } else if text.contains(PROOF_CHECK_ENVELOPE_PHRASE) {
        Some(StopItem::ProofCheckEnvelope)
    } else if text.contains(UNVERIFIED_TRUST_RULE_PHRASE) {
        Some(StopItem::UnverifiedTrustRule)
    } else if text.contains(GENERIC_THEORY_LEMMA_PHRASE) {
        Some(StopItem::GenericTheoryLemma)
    } else if text.contains(MODEL_VALIDATION_PHRASE) {
        Some(StopItem::ModelValidationViolated)
    } else if text.contains("FINALIZE_SAT_FAIL")
        || text.contains("Invalid SAT model")
        || (text.contains("BUG: original clause") && text.contains("unsatisfied"))
    {
        Some(StopItem::InvalidSatModel)
    } else {
        None
    }
}

/// Whether `result` is ay's own UNSAT that a certification gate WITHHELD: ay's
/// search decided the query UNSAT, and ay says only that its proof could not
/// be certified, never that the query is satisfiable. Read off the row either
/// ay lane writes: ay's refusal token rides in its reason (the in-process
/// `UnknownReason` text, the subprocess `:unknown.reason`), and so does the
/// named stop ay's wording states ([`StopItem::from_reason`]).
///
/// `proof_trusted` is such an UNSAT whatever its wording: ay files nothing else
/// under it. `self_check_rejected` is one only when its named stop refuses an
/// UNSAT proof: a cancelled strict check, an unverified trust rule, a
/// strict-mode `Generic` lemma, an exhausted proof-check envelope, a spent
/// certification effort. ay files other verdicts under that code (Trust's pin
/// da447f9a6): a computed SAT that
/// reached its API boundary without its model-validation capability
/// (`api/solving/check.rs`), and a working-set UNSAT its exact BV/LIA checker
/// found satisfiable (`bounded_bv_lia/mod.rs`). Either query can be
/// satisfiable, so neither counts.
#[must_use]
pub(crate) fn withheld_computed_unsat(result: &VerificationResult) -> bool {
    let VerificationResult::Unknown { reason, .. } = result else {
        return false;
    };
    let [self_check_rejected, proof_trusted] = CERTIFICATION_REFUSAL_TOKENS;
    reason.contains(proof_trusted)
        || (reason.contains(self_check_rejected)
            && StopItem::from_reason(reason).is_some_and(|item| {
                matches!(
                    item,
                    StopItem::StrictCheckCancelled
                        | StopItem::UnverifiedTrustRule
                        | StopItem::GenericTheoryLemma
                        | StopItem::ProofCheckEnvelope
                        | StopItem::CertificationEffort
                )
            }))
}

/// ay's native-replay authority refusal of a proof its strict checker walked to
/// the LAST step, with no checker failure and no trust step: nothing but the
/// post-validator stop signal withheld the authority (critique 2026-09-30).
fn native_replay_checked_every_step(text: &str) -> bool {
    if !text.contains(NATIVE_REPLAY_REFUSAL_PHRASE) {
        return false;
    }
    let some = |key: &str| -> Option<u64> {
        let at = text.find(key)?;
        let rest = text[at + key.len()..].strip_prefix("Some(")?;
        rest[..rest.find(')')?].parse().ok()
    };
    matches!(
        (some("checked_steps="), some("total_steps=")),
        (Some(checked), Some(total)) if total > 0 && checked == total
    ) && some("raw_checker_failures=") == Some(0)
        && some("proof_trust=") == Some(0)
        && text.contains("strictly_verified=false")
}

fn memory_stop(detail: Option<&str>) -> StopCause {
    if detail.is_some_and(|detail| detail.contains(TERM_STORE_CEILING_PHRASE)) {
        StopCause::TermMemory
    } else {
        StopCause::RssBackstop
    }
}

/// ay's account of the last `unknown`, read from an `(get-info
/// :all-statistics)` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AyUnknownAccount {
    /// The native reason token (`:unknown.reason`).
    pub(crate) reason: String,
    /// The human detail (`:unknown.detail`), when present.
    pub(crate) detail: Option<String>,
    /// SAT conflicts the solve spent (`:conflicts`), when present.
    pub(crate) conflicts: Option<u64>,
}

impl AyUnknownAccount {
    /// Parse the account out of a statistics block. `None` when the block names
    /// no `:unknown.reason` (an older ay, or a block from a decided solve).
    #[must_use]
    pub(crate) fn parse(statistics: &str) -> Option<Self> {
        let reason = statistics_value(statistics, ":unknown.reason")?;
        Some(Self {
            reason,
            detail: statistics_value(statistics, ":unknown.detail"),
            conflicts: statistics_value(statistics, ":conflicts")
                .and_then(|value| value.parse::<u64>().ok()),
        })
    }

    /// The stop cause this account states.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn stop_cause(&self) -> StopCause {
        self.stop().cause
    }

    /// The stop this account states, named when its detail is one Trust counts
    /// by name.
    #[must_use]
    pub(crate) fn stop(&self) -> AyStop {
        ay_stop_of_token(&self.reason, self.detail.as_deref())
    }

    /// A reason line for the row: ay's token, and the conflicts it spent.
    #[must_use]
    pub(crate) fn describe(&self) -> String {
        match self.conflicts {
            Some(conflicts) => format!("ay unknown ({}; {conflicts} conflicts)", self.reason),
            None => format!("ay unknown ({})", self.reason),
        }
    }
}

/// The value of one `:key value` entry of an SMT-LIB statistics block. A string
/// value is returned without its quotes, with SMT-LIB's doubled `""` escape
/// undone. Keys are matched whole (`:conflicts` never matches
/// `:theory-conflicts`).
fn statistics_value(statistics: &str, key: &str) -> Option<String> {
    let mut rest = statistics;
    loop {
        let at = rest.find(key)?;
        let before_ok = at == 0 || rest[..at].ends_with(|c: char| c.is_whitespace() || c == '(');
        let after = &rest[at + key.len()..];
        let after_ok = after.starts_with(|c: char| c.is_whitespace());
        if before_ok && after_ok {
            let value = after.trim_start();
            return Some(if let Some(quoted) = value.strip_prefix('"') {
                read_smtlib_string(quoted)
            } else {
                value
                    .split(|c: char| c.is_whitespace() || c == ')')
                    .next()
                    .unwrap_or_default()
                    .to_string()
            });
        }
        rest = &rest[at + key.len()..];
    }
}

/// Read an SMT-LIB string literal body (after the opening quote) up to its
/// closing quote, undoing the `""` escape.
fn read_smtlib_string(body: &str) -> String {
    let mut out = String::new();
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' {
            if chars.peek() == Some(&'"') {
                chars.next();
                out.push('"');
            } else {
                break;
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The statistics block the pinned ay prints after a conflict-budget stop,
    /// trimmed to the keys this module reads plus neighbours that must not be
    /// confused with them (captured 2026-09-29 from ay 0.26.0 build 9624,
    /// `--z3-mode -smt2`, PHP(10,9) under `(set-option :rlimit 10000)`).
    const RESOURCEOUT_BLOCK: &str = r#"(:conflicts                                   10000
 :decisions                                   33238
 :rlimit-count                                428759
 :theory-conflicts                            0
 :unknown.cost-center                         "deterministic-budget"
 :unknown.detail                              "deterministic resource budget exhausted before a definitive result (conflicts=10000, decisions=33238; `:rlimit` or the default ground budget, #ground-determinism)"
 :unknown.phase                               "resource-control"
 :unknown.reason                              "resourceout")"#;

    #[test]
    fn a_conflict_budget_stop_reads_as_effort_with_its_conflicts() {
        let account = AyUnknownAccount::parse(RESOURCEOUT_BLOCK).unwrap();
        assert_eq!(account.reason, "resourceout");
        assert_eq!(account.conflicts, Some(10_000));
        assert!(account.detail.as_deref().unwrap().starts_with("deterministic resource budget"));
        assert_eq!(account.stop_cause(), StopCause::Effort);
        assert_eq!(account.describe(), "ay unknown (resourceout; 10000 conflicts)");
    }

    #[test]
    fn keys_match_whole_and_strings_unescape() {
        let block = r#"(:theory-conflicts 7
 :conflicts 3
 :unknown.detail "a ""quoted"" (unbalanced detail"
 :unknown.reason timeout)"#;
        let account = AyUnknownAccount::parse(block).unwrap();
        assert_eq!(account.conflicts, Some(3), ":theory-conflicts must not be read as :conflicts");
        assert_eq!(account.detail.as_deref(), Some("a \"quoted\" (unbalanced detail"));
        assert_eq!(account.reason, "timeout");
        assert_eq!(account.stop_cause(), StopCause::WallBackstop);
        assert_eq!(AyUnknownAccount::parse("(:conflicts 3)"), None);
    }

    #[test]
    fn every_native_token_has_its_cause() {
        let cases = [
            ("resourceout", None, StopCause::Effort),
            ("timeout", None, StopCause::WallBackstop),
            ("interrupted", None, StopCause::WallBackstop),
            ("memout", None, StopCause::RssBackstop),
            (
                "memout",
                Some(
                    "executor term-store memory ceiling exceeded while the active solve phase was running",
                ),
                StopCause::TermMemory,
            ),
            ("incomplete", None, StopCause::SolverIncomplete),
            ("(incomplete quantifier-cegqi)", None, StopCause::SolverIncomplete),
            ("(incomplete self-check-rejected)", None, StopCause::SolverIncomplete),
            ("(incomplete proof-trusted)", None, StopCause::SolverIncomplete),
            ("unsupported", None, StopCause::Unsupported),
            ("(unsupported arithmetic)", None, StopCause::Unsupported),
            ("internal-error", None, StopCause::SolverFault),
            ("unknown", None, StopCause::Unclassified),
            ("canceled", None, StopCause::Unclassified),
            ("\"resourceout\"", None, StopCause::Effort),
        ];
        for (token, detail, expected) in cases {
            assert_eq!(stop_cause_of_ay_token(token, detail), expected, "{token}");
        }
    }

    /// Since ay da447f9a6 (P4a, the BV/FP bit-blast slice) a stop that cut a
    /// bit-blast solve's encoding is published as that stop, where ffaba97f6
    /// published `incomplete` (a congruence pass a poll stopped, ay
    /// `executor/theories/congruence_bail.rs`) or an untagged unknown (a
    /// `bitblast_all` the process memory ceiling cut). On both lanes a clock or
    /// an interrupt is `wall-backstop`; the process ceiling is `rss-backstop`
    /// (a reading, never the term-store count); the pass's own count cap stays
    /// `solver-incomplete`; a spent `:rlimit` (its conflicts, or the decision
    /// allowance beside them) is `effort`. Each is a direct statement of its
    /// bound, so no item is named.
    #[test]
    fn a_bit_blast_stop_is_read_as_that_stop() {
        let stopped = |token: &str| {
            format!(
                "a BV congruence pass was stopped ({token}); a SAT under the partial \
                 axiomatization is withheld (UNSAT stays valid)"
            )
        };
        let cases = [
            ("timeout", "timeout", stopped("timeout"), StopCause::WallBackstop),
            ("interrupted", "interrupted", stopped("interrupted"), StopCause::WallBackstop),
            ("memory_limit", "memout", stopped("memout"), StopCause::RssBackstop),
            (
                "memory_limit",
                "memout",
                "process memory ceiling exceeded while the active solve phase was running"
                    .to_string(),
                StopCause::RssBackstop,
            ),
            (
                "incomplete",
                "incomplete",
                "a BV congruence pass reached its count cap; a SAT under the partial \
                 axiomatization is withheld (UNSAT stays valid)"
                    .to_string(),
                StopCause::SolverIncomplete,
            ),
            (
                "resource_limit",
                "resourceout",
                "deterministic resource budget exhausted before a definitive result".to_string(),
                StopCause::Effort,
            ),
        ];
        for (code, token, detail, cause) in cases {
            let expected = AyStop { cause, item: None };
            assert_eq!(ay_stop_of_code(code, &[Some(&detail)]), expected, "{code}: {detail}");
            assert_eq!(ay_stop_of_token(token, Some(&detail)), expected, "{token}: {detail}");
        }
    }

    /// Critique of the lane-efficiency plan (2026-09-30), P1 ledger items: the
    /// stops ay words but Trust used to read as a bare `unclassified` (or an
    /// unnamed `solver-incomplete`) are named, each with its one cause.
    #[test]
    fn ay_wording_names_the_stop() {
        let certification = "computed UNSAT rejected by mandatory strict certification: ";
        let cases = [
            (
                format!(
                    "{certification}proof validation cancelled by the caller (interrupt, \
                     deadline, or memory limit)"
                ),
                Some(StopItem::StrictCheckCancelled),
            ),
            (
                format!("{certification}step t5 uses unverified trust rule"),
                Some(StopItem::UnverifiedTrustRule),
            ),
            (
                format!(
                    "{certification}step t2 uses unsupported theory lemma kind Generic in \
                     strict mode"
                ),
                Some(StopItem::GenericTheoryLemma),
            ),
            (
                format!("{certification}proof validation resource envelope exhausted"),
                Some(StopItem::ProofCheckEnvelope),
            ),
            (
                // ay names the count beside the trust rule it left; the count
                // is the stop.
                "deferred-trust discharge failed: a collected trust clause is not a standalone \
                 theory tautology AND the problem assertions could not be independently \
                 re-solved as UNSAT; certification effort exhausted (spent 13 of 10); step t5 \
                 uses unverified trust rule"
                    .to_string(),
                Some(StopItem::CertificationEffort),
            ),
            (
                "model validation violated: Assertion: x = 3 is false".to_string(),
                Some(StopItem::ModelValidationViolated),
            ),
            (
                "BUG: original clause 497327/1553935 unsatisfied, reconstruction_len=3".to_string(),
                Some(StopItem::InvalidSatModel),
            ),
            (
                "BUG [#8819]: Invalid SAT model — finalized model does not satisfy original \
                 clauses on release-mode re-verification"
                    .to_string(),
                Some(StopItem::InvalidSatModel),
            ),
            ("deterministic resource budget exhausted".to_string(), None),
            ("step t1 references missing premise t0".to_string(), None),
        ];
        for (text, expected) in cases {
            assert_eq!(stop_item_of_ay_text(&text), expected, "{text}");
        }
    }

    #[test]
    fn a_named_stop_refines_only_an_unexplained_or_generic_cause() {
        let cancelled =
            Some("proof validation cancelled by the caller (interrupt, deadline, or memory limit)");
        // ay's certification funnel: `self_check_rejected` reads
        // `solver-incomplete` (P4a.1 counts the discharge), and a strict check
        // a stop cancelled mid-walk is still a CLOCK stop.
        let stop = ay_stop_of_code("self_check_rejected", &[cancelled]);
        assert_eq!(
            stop,
            AyStop { cause: StopCause::WallBackstop, item: Some(StopItem::StrictCheckCancelled) }
        );
        let token = ay_stop_of_token("(incomplete self-check-rejected)", cancelled);
        assert_eq!(token, stop, "both lanes read the same stop");
        // The trust-rule and Generic-lemma refusals are the proof's, and the
        // envelope and the certification effort are counts: each reproducible,
        // by name, on both lanes.
        for (detail, item, cause) in [
            (
                "step t5 uses unverified trust rule",
                StopItem::UnverifiedTrustRule,
                StopCause::SolverIncomplete,
            ),
            (
                "step t2 uses unsupported theory lemma kind Generic in strict mode",
                StopItem::GenericTheoryLemma,
                StopCause::SolverIncomplete,
            ),
            (
                "proof validation resource envelope exhausted",
                StopItem::ProofCheckEnvelope,
                StopCause::Effort,
            ),
            (
                "certification effort exhausted (spent 13 of 10)",
                StopItem::CertificationEffort,
                StopCause::Effort,
            ),
        ] {
            let stop = ay_stop_of_code("self_check_rejected", &[Some(detail)]);
            assert_eq!(stop, AyStop { cause, item: Some(item) }, "{detail}");
            let token = ay_stop_of_token("(incomplete self-check-rejected)", Some(detail));
            assert_eq!(token, stop, "both lanes read the same stop: {detail}");
        }
        // A degraded SAT stays a deterministic `solver-incomplete`, named.
        let invalid_model = Some("model validation violated: Assertion: y");
        assert_eq!(
            ay_stop_of_code("incomplete", &[invalid_model]),
            AyStop {
                cause: StopCause::SolverIncomplete,
                item: Some(StopItem::ModelValidationViolated)
            }
        );
        // An ay defect behind an untagged `unknown` is a solver fault.
        assert_eq!(
            ay_stop_of_code("unknown", &[Some("BUG: original clause 3/10 unsatisfied")]),
            AyStop { cause: StopCause::SolverFault, item: Some(StopItem::InvalidSatModel) }
        );
        // A direct resource statement stands, unnamed.
        assert_eq!(
            ay_stop_of_code("resource_limit", &[invalid_model]),
            AyStop { cause: StopCause::Effort, item: None }
        );
        assert_eq!(
            ay_stop_of_code("incomplete", &[None]),
            AyStop { cause: StopCause::SolverIncomplete, item: None }
        );
        // The stamp carries both tokens, the stop token last.
        let stamped = stop.stamp("in-process ay returned unknown");
        assert_eq!(StopItem::from_reason(&stamped), Some(StopItem::StrictCheckCancelled));
        assert_eq!(StopCause::from_reason(&stamped), Some(StopCause::WallBackstop));
    }

    #[test]
    fn a_native_replay_refusal_with_every_step_checked_is_the_post_validator_stop() {
        let refusal = |checked: &str, total: &str, trust: &str| {
            format!(
                "UNSAT replay lacks strict proof authority (checker_active=true, \
                 artifact_available=true, summary_checker_failures=0, strictly_verified=false, \
                 raw_checker_failures=Some(0), proof_complete=true, proof_trust={trust}, \
                 checked_steps={checked}, total_steps={total}, skipped_holes=Some(0), \
                 proof_decline=None)"
            )
        };
        assert_eq!(
            stop_item_of_ay_text(&refusal("Some(6)", "Some(6)", "Some(0)")),
            Some(StopItem::StrictCheckCancelled)
        );
        assert_eq!(stop_item_of_ay_text(&refusal("Some(5)", "Some(6)", "Some(0)")), None);
        assert_eq!(stop_item_of_ay_text(&refusal("Some(6)", "Some(6)", "Some(2)")), None);
        assert_eq!(stop_item_of_ay_text(&refusal("None", "None", "Some(0)")), None);
    }

    #[test]
    fn a_statistics_block_names_the_stop_from_its_detail() {
        let block = r#"(:conflicts 12
 :unknown.detail "computed UNSAT rejected by mandatory strict certification: proof validation cancelled by the caller (interrupt, deadline, or memory limit)"
 :unknown.reason "(incomplete self-check-rejected)")"#;
        let account = AyUnknownAccount::parse(block).unwrap();
        assert_eq!(
            account.stop(),
            AyStop { cause: StopCause::WallBackstop, item: Some(StopItem::StrictCheckCancelled) }
        );
        assert_eq!(account.stop_cause(), StopCause::WallBackstop);
    }

    /// Review of the 2026-10-01 retry gate: ay files more than a withheld UNSAT
    /// under `self_check_rejected`, so only `proof_trusted`, or a named refusal
    /// of an UNSAT proof, says ay's search decided the query. Read off both
    /// lanes' rows.
    #[test]
    fn only_unsat_evidence_reads_as_a_withheld_computed_unsat() {
        let certification = "computed UNSAT rejected by mandatory strict certification: ";
        let rows = |code: &str, token: &str, detail: Option<&str>| {
            [
                ay_stop_of_code(code, &[detail, Some(token)]).unknown_result(
                    "in-process ay",
                    1,
                    &format!("in-process ay returned unknown: {token} (1 conflicts)"),
                ),
                ay_stop_of_token(token, detail).unknown_result(
                    "ay-incremental",
                    1,
                    &format!("ay unknown ({token}; 1 conflicts)"),
                ),
            ]
        };
        let rejected = |detail: Option<&str>| {
            rows("self_check_rejected", "(incomplete self-check-rejected)", detail)
        };
        let withheld = [
            format!("{certification}step t0 uses unverified trust rule"),
            format!(
                "{certification}step t2 uses unsupported theory lemma kind Generic in strict mode"
            ),
            format!("{certification}proof validation resource envelope exhausted"),
            format!(
                "{certification}proof validation cancelled by the caller (interrupt, deadline, \
                 or memory limit)"
            ),
            format!("{certification}certification effort exhausted (spent 13 of 10)"),
        ];
        for detail in &withheld {
            for row in rejected(Some(detail)) {
                assert!(withheld_computed_unsat(&row), "{row:?}");
            }
        }
        for detail in [None, Some("the terminal derivation chain is not trust-free")] {
            for row in rows("proof_trusted", "(incomplete proof-trusted)", detail) {
                assert!(withheld_computed_unsat(&row), "{row:?}");
            }
        }
        // ay's SAT refusals and its exact checker's SAT contradiction share the
        // code (ay-dpll `api/solving/check.rs`, `bounded_bv_lia/mod.rs`).
        for detail in [
            None,
            Some(
                "computed SAT reached the native API boundary without its model-validation \
                 capability",
            ),
            Some(
                "strict UNSAT proof validation failed: exact public BV/LIA source rejected a \
                 working-set refutation: the independently interpreted BV/LIA query is \
                 satisfiable",
            ),
            Some("model validation violated: Assertion: x = 3 is false"),
        ] {
            for row in rejected(detail) {
                assert!(!withheld_computed_unsat(&row), "{row:?}");
            }
        }
        // A proof-refusal wording under any other reason is not certification's.
        for (code, token) in [("timeout", "timeout"), ("incomplete", "incomplete")] {
            for row in rows(code, token, Some(&withheld[0])) {
                assert!(!withheld_computed_unsat(&row), "{row:?}");
            }
        }
        assert!(!withheld_computed_unsat(&VerificationResult::Timeout {
            solver: "ay".into(),
            timeout_ms: 5,
        }));
    }

    /// Review finding (2026-09-29): a retry that stopped on the clock must not
    /// leave the original row claiming its deterministic first-attempt cause.
    #[test]
    fn an_undecided_retry_folds_only_a_non_reproducible_stop_into_the_row() {
        let original = StopCause::Effort.unknown_result("ay", 7, "ay unknown (resourceout)");
        for deterministic in [StopCause::Effort, StopCause::Solved, StopCause::Unsupported] {
            assert_eq!(
                format!(
                    "{:?}",
                    after_undecided_retry(original.clone(), deterministic, "component retry")
                ),
                format!("{original:?}"),
                "a {deterministic} retry stop leaves the row as it was"
            );
        }
        for clock_like in [
            StopCause::WallBackstop,
            StopCause::Unclassified,
            StopCause::SolverFault,
            StopCause::RssBackstop,
        ] {
            let folded = after_undecided_retry(original.clone(), clock_like, "component retry");
            assert_eq!(StopCause::of_result(&folded), clock_like, "{folded:?}");
            let VerificationResult::Unknown { reason, time_ms, .. } = &folded else {
                panic!("still undecided: {folded:?}");
            };
            assert_eq!(*time_ms, 7);
            assert!(reason.starts_with("ay unknown (resourceout)"), "{reason}");
            assert!(reason.contains("component retry stopped on"), "{reason}");
        }
        let timeout = VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5 };
        assert!(matches!(
            after_undecided_retry(timeout, StopCause::Unclassified, "relaxation"),
            VerificationResult::Timeout { timeout_ms: 5, .. }
        ));
    }

    #[test]
    fn every_stable_code_has_its_cause() {
        // ay `UnknownReason::code()` at Trust's ay pin (da447f9a6),
        // `crates/ay-dpll/src/executor_types/mod.rs`.
        let cases = [
            ("timeout", StopCause::WallBackstop),
            ("resource_limit", StopCause::Effort),
            ("memory_limit", StopCause::RssBackstop),
            ("interrupted", StopCause::WallBackstop),
            ("incomplete", StopCause::SolverIncomplete),
            // Certification refusals: the discharge behind them is counted
            // (P4a.1), and a stop that ended it is published as that stop.
            ("self_check_rejected", StopCause::SolverIncomplete),
            ("proof_trusted", StopCause::SolverIncomplete),
            ("quantifier_round_limit", StopCause::SolverIncomplete),
            ("quantifier_deferred", StopCause::SolverIncomplete),
            ("quantifier_unhandled", StopCause::SolverIncomplete),
            ("quantifier_cegqi_incomplete", StopCause::SolverIncomplete),
            ("quantifier_ematching_exists_incomplete", StopCause::SolverIncomplete),
            ("split_limit", StopCause::SolverIncomplete),
            ("expression_split", StopCause::SolverIncomplete),
            ("unsupported", StopCause::Unsupported),
            ("unsupported_arithmetic", StopCause::Unsupported),
            ("unsupported_mixed_collection", StopCause::Unsupported),
            ("internal_error", StopCause::SolverFault),
            ("unknown", StopCause::Unclassified),
            ("a_code_from_a_newer_ay", StopCause::Unclassified),
        ];
        for (code, expected) in cases {
            assert_eq!(stop_cause_of_ay_code(code, None), expected, "{code}");
        }
        assert_eq!(
            stop_cause_of_ay_code(
                "memory_limit",
                Some("executor term-store memory ceiling exceeded")
            ),
            StopCause::TermMemory
        );
    }
}
