//! Determinism accounting for verification results: WHY each obligation's
//! search ended, whether that reason is reproducible, and the per-unit verdict
//! vector whose digest says whether two runs agreed.
//!
//! Plan of record: `docs/design/2026-09-29-incremental-deterministic-trust-results.md`
//! (§2 terms, §3.1 the rule, §3.6 the budget profile, §3.7 report changes).
//!
//! # The rule this module makes checkable
//!
//! Every bound that can change a verdict must be a COUNT. A clock or an RSS
//! reading may stop a run, but it never produces a verdict. Before this module
//! a clock-ended obligation and a count-ended one were the same `Unknown` row,
//! so a consumer that saw a proved count move could only guess, from log text,
//! whether the machine was loaded or the code changed. Here every obligation
//! carries a [`StopCause`], every stop cause has one [`Reproducibility`], and a
//! unit's [`UnitOutcome`] is the worst of them:
//!
//! * `measured` — every stop cause is deterministic: the same inputs, seal and
//!   budget profile give the same verdict vector at any load;
//! * `not-reproducible` — at least one obligation was ended by a clock or an RSS
//!   reading (or by a producer that never said why); the Summary is printed and
//!   flagged, and its counts are not a floor measurement;
//! * `could-not-run` — the verifier was refused the resources to run at all
//!   (admission refused); no Summary is printed.
//!
//! # How a stop cause travels
//!
//! The router, the compiler and targo exchange obligation results as
//! [`VerificationResult`] and [`TransportObligationResult`](crate::TransportObligationResult)
//! values whose undecided rows carry a free-text `reason`. A producer that knows
//! why a search ended states it with a typed constructor
//! ([`StopCause::unknown_result`], [`StopCause::stamp`]); the cause rides at the
//! END of the reason as one machine-written token, `[stop:<cause>]`, and is read
//! back by exactly one parser ([`StopCause::from_reason`]). The end, because
//! existing consumers match reasons by prefix (the admission prefixes, the
//! memory-guard wording). A row whose producer did not state a cause reads back
//! as [`StopCause::Unclassified`], which is NOT reproducible: an unexplained stop
//! is never counted as deterministic, so a lane that has not been threaded yet
//! shows up in the stop-cause tally instead of silently passing as `measured`.
//!
//! # When causes combine, the less reproducible one wins
//!
//! A row's reason often carries more than one statement: a wrapper quotes an
//! inner reason and states its own cause, a retry restamps the first attempt, a
//! fallback lane decides after an earlier lane stopped. Whenever two causes bear
//! on one row, the LESS reproducible one wins — `could-not-run` beats
//! `not-reproducible`, which beats every deterministic cause
//! ([`StopCause::combine`]). A wrapper that states a deterministic cause can
//! therefore never launder a clock (or an unexplained stop) underneath it: had
//! the clock not fired, the row could have ended differently, so the row is not
//! reproducible whatever the wrapper then concluded. Between two causes of the
//! same class the outer (later) statement wins, except that `unclassified`
//! never replaces a stated cause of its own class. [`StopCause::stamp`] applies
//! this rule to the cause already in the detail, and [`StopCause::from_reason`]
//! returns the worst cause the reason carries.
//!
//! # Backstops that fire outside a row
//!
//! Not every stop ends a published row. The compiler consumes solver results
//! internally — the whole-crate R1 harvest, refutation attempts, strict
//! revalidation, proof-authority lanes — and a clock that ends one of those
//! changes which rows are decided without appearing in any row's reason. Plan
//! §2 defines `not-reproducible` as "at least one backstop fired", so every
//! solver lane and budget scope reports such a stop to the process-wide
//! backstop ledger ([`note_stop`]); the compiler publishes the ledger once per
//! crate ([`take_noted_stops`], carried by the crate's coverage transport), and
//! a consumer folds it into the unit outcome.

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::digest::lowercase_hex;
use crate::{Formula, Outcome, VerificationResult};

/// What ended the search for one obligation.
///
/// The canonical spelling ([`StopCause::as_str`]) is the only one written on
/// any wire, in any report and inside a `[stop:…]` reason token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum StopCause {
    /// A decision procedure reached a verdict (proved or refuted), including a
    /// verdict a later policy gate then withheld — but only a gate that is a
    /// pure function of the verdict and the obligation. A gate that runs work of
    /// its own on a wall clock (S1 revalidation; a proof-authority lane) cannot
    /// state `solved` for a withheld verdict: it states the clock's stop, or
    /// `unclassified`, until that work is counted (plan P4a). ay's strict-proof
    /// discharge is counted since ay ffaba97f6 (P4a.1): its refusals are
    /// [`StopCause::SolverIncomplete`] or [`StopCause::Effort`], and a stop that
    /// ended it is that stop.
    Solved,
    /// The per-function preprocessing STEP budget
    /// (`-Ztrust-verify-function-budget-steps`) ran out.
    Steps,
    /// A solver EFFORT count ran out: the query's size-scaled `:rlimit`
    /// conflict count ([`EffortScale`], plan §3.2a) or ay's own decision
    /// allowance, which ay enforces on every SAT solve and reports as
    /// `resourceout`. Also the clean kernel's own heartbeat count when it ends
    /// the re-check of a certificate (trust-certify's `kernel_stop`, P4a
    /// slice 2): a fixed count per type checker, not sized from the query.
    Effort,
    /// The solver's per-executor term-memory allowance (a count of TermStore
    /// bytes, independent of process RSS) ran out.
    TermMemory,
    /// A model-checking frame / unrolling-depth cap ran out.
    Frames,
    /// The solver ended without a verdict for a reason of its own that does not
    /// depend on the clock: an incomplete theory lane, a quantifier
    /// instantiation cap, a split cap, a model that did not validate, a
    /// certification refusal (a strict proof with a trust step or a `Generic`
    /// lemma left in it). ay's certification funnel discharges deferred proof
    /// steps with nested solves drawn from the solved query's own effort count
    /// (P4a.1, ay ffaba97f6), and publishes a stop that ended the discharge as
    /// that stop, never as a refusal.
    SolverIncomplete,
    /// No lane can encode or decide this obligation (unsupported MIR, a
    /// declined formula shape, no backend for the kind).
    Unsupported,
    /// The obligation was deliberately not handed to a decision procedure: a
    /// recorded assumption, a design mandate, a policy row.
    NotDispatched,
    /// A wall clock ended the search: a per-VC timeout or per-function
    /// deadline, the step budget's clock poll, a watchdog, an external
    /// interrupt. NOT reproducible. The ay lanes' clocks sit behind the one
    /// effort count ([`EffortScale`]) and preprocessing's behind the step
    /// budget; the native CHC/PDR engine,
    /// kernel certification and the structural promotions have no count yet
    /// (plan P4a), so for them the same clocks are still the bound. Either way
    /// this stop is how a unit shows that a clock decided something.
    WallBackstop,
    /// A process-RSS reading ended the search: the router memory guard, a
    /// solver `--memory`/`:max-memory` ceiling. NOT reproducible.
    RssBackstop,
    /// The solver process crashed, could not be spawned, or broke protocol.
    /// NOT reproducible.
    SolverFault,
    /// The producer did not say why the search ended, or cannot know: a gate
    /// that withheld a verdict after work of its own that may have run out on a
    /// clock it cannot see (a proof-authority lane). NOT reproducible: an
    /// unexplained stop is never counted as deterministic.
    Unclassified,
    /// Resource admission (trustd / the memory jobserver) refused to let the
    /// solver run. The UNIT could not run; this is never an obligation verdict.
    AdmissionRefused,
}

/// How a stop cause bears on reproducibility.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Reproducibility {
    /// The same inputs, seal and budget profile end the search the same way.
    Deterministic,
    /// A clock, an RSS reading, a crash, or an unexplained stop ended it.
    NotReproducible,
    /// The verifier was refused the resources to run.
    CouldNotRun,
}

impl Reproducibility {
    /// How far this class is from a measurement: `0` deterministic, `1` not
    /// reproducible, `2` could not run. The combination rule
    /// ([`StopCause::combine`]) keeps the higher rank.
    #[must_use]
    pub const fn rank(self) -> u8 {
        match self {
            Self::Deterministic => 0,
            Self::NotReproducible => 1,
            Self::CouldNotRun => 2,
        }
    }
}

impl StopCause {
    /// Every stop cause, in canonical-name order.
    pub const ALL: [Self; 13] = [
        Self::AdmissionRefused,
        Self::Effort,
        Self::Frames,
        Self::NotDispatched,
        Self::RssBackstop,
        Self::Solved,
        Self::SolverFault,
        Self::SolverIncomplete,
        Self::Steps,
        Self::TermMemory,
        Self::Unclassified,
        Self::Unsupported,
        Self::WallBackstop,
    ];

    /// The canonical serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Solved => "solved",
            Self::Steps => "steps",
            Self::Effort => "effort",
            Self::TermMemory => "term-memory",
            Self::Frames => "frames",
            Self::SolverIncomplete => "solver-incomplete",
            Self::Unsupported => "unsupported",
            Self::NotDispatched => "not-dispatched",
            Self::WallBackstop => "wall-backstop",
            Self::RssBackstop => "rss-backstop",
            Self::SolverFault => "solver-fault",
            Self::Unclassified => "unclassified",
            Self::AdmissionRefused => "admission-refused",
        }
    }

    /// Parse the canonical spelling. Anything else is refused, never bucketed.
    #[must_use]
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "solved" => Some(Self::Solved),
            "steps" => Some(Self::Steps),
            "effort" => Some(Self::Effort),
            "term-memory" => Some(Self::TermMemory),
            "frames" => Some(Self::Frames),
            "solver-incomplete" => Some(Self::SolverIncomplete),
            "unsupported" => Some(Self::Unsupported),
            "not-dispatched" => Some(Self::NotDispatched),
            "wall-backstop" => Some(Self::WallBackstop),
            "rss-backstop" => Some(Self::RssBackstop),
            "solver-fault" => Some(Self::SolverFault),
            "unclassified" => Some(Self::Unclassified),
            "admission-refused" => Some(Self::AdmissionRefused),
            _ => None,
        }
    }

    /// Whether this cause is the solver COUNT (plan §3.2a): the one
    /// size-scaled effort count (`effort`). Deterministic, and counted in the
    /// backstop ledger wherever the stopped work went ([`note_stop`]), so how
    /// often it binds is visible.
    #[must_use]
    pub const fn is_solver_count(self) -> bool {
        matches!(self, Self::Effort)
    }

    /// Whether this cause is a RESOURCE backstop that ended a solve before it
    /// decided anything: a process-memory reading (`rss-backstop` — the router
    /// memory guard, or the in-process solver's own process ceiling) or a
    /// solver fault. Neither is reproducible, and neither says anything about
    /// the obligation, so a lane that stopped on one must leave that trace on
    /// the row another lane produced ([`fold_lane_stop`]) instead of letting
    /// that row's own text stand as the reason the obligation is unproved.
    #[must_use]
    pub const fn is_resource_backstop(self) -> bool {
        matches!(self, Self::RssBackstop | Self::SolverFault)
    }

    /// Whether this cause lets the same inputs reproduce the same verdict.
    #[must_use]
    pub const fn reproducibility(self) -> Reproducibility {
        match self {
            Self::Solved
            | Self::Steps
            | Self::Effort
            | Self::TermMemory
            | Self::Frames
            | Self::SolverIncomplete
            | Self::Unsupported
            | Self::NotDispatched => Reproducibility::Deterministic,
            Self::WallBackstop | Self::RssBackstop | Self::SolverFault | Self::Unclassified => {
                Reproducibility::NotReproducible
            }
            Self::AdmissionRefused => Reproducibility::CouldNotRun,
        }
    }

    /// The machine token this cause is carried as inside a free-text reason.
    #[must_use]
    pub const fn token_str(self) -> &'static str {
        match self {
            Self::Solved => "[stop:solved]",
            Self::Steps => "[stop:steps]",
            Self::Effort => "[stop:effort]",
            Self::TermMemory => "[stop:term-memory]",
            Self::Frames => "[stop:frames]",
            Self::SolverIncomplete => "[stop:solver-incomplete]",
            Self::Unsupported => "[stop:unsupported]",
            Self::NotDispatched => "[stop:not-dispatched]",
            Self::WallBackstop => "[stop:wall-backstop]",
            Self::RssBackstop => "[stop:rss-backstop]",
            Self::SolverFault => "[stop:solver-fault]",
            Self::Unclassified => "[stop:unclassified]",
            Self::AdmissionRefused => "[stop:admission-refused]",
        }
    }

    /// The machine token this cause is carried as inside a free-text reason.
    #[must_use]
    pub fn token(self) -> String {
        self.token_str().to_string()
    }

    /// The cause of a row on which both `inner` (stated first: a quoted inner
    /// reason, an earlier attempt, a lane whose stop let a later lane run) and
    /// `outer` (stated last) bear.
    ///
    /// The LESS reproducible cause wins: `could-not-run` over
    /// `not-reproducible` over every deterministic cause. A deterministic
    /// statement made after a clock fired cannot make the row reproducible,
    /// because without the clock the row could have ended differently. Within
    /// one class the outer statement wins — it is the one that decided what the
    /// row finally says — except that `unclassified` ("nobody said why") never
    /// replaces a cause of its own class that somebody did state.
    #[must_use]
    pub const fn combine(inner: Self, outer: Self) -> Self {
        let inner_rank = inner.reproducibility().rank();
        let outer_rank = outer.reproducibility().rank();
        if inner_rank > outer_rank {
            inner
        } else if outer_rank > inner_rank {
            outer
        } else if matches!(outer, Self::Unclassified) {
            inner
        } else {
            outer
        }
    }

    /// `detail`, followed by one token: this cause combined
    /// ([`Self::combine`]) with the cause `detail` already carries. A token
    /// already ending `detail` is replaced, so re-stating never yields two
    /// trailing tokens that disagree — and a restamp never makes the row MORE
    /// reproducible than the detail it wraps.
    #[must_use]
    pub fn stamp(self, detail: &str) -> String {
        let cause = match Self::from_reason(detail) {
            Some(inner) => Self::combine(inner, self),
            None => self,
        };
        let detail = strip_trailing_token(detail);
        if detail.is_empty() {
            cause.token()
        } else {
            format!("{detail} {}", cause.token_str())
        }
    }

    /// An `Unknown` result whose search ended for this cause.
    #[must_use]
    pub fn unknown_result(self, solver: &str, time_ms: u64, detail: &str) -> VerificationResult {
        VerificationResult::Unknown { solver: solver.into(), time_ms, reason: self.stamp(detail) }
    }

    /// The cause `reason` states, if it carries any stop token.
    ///
    /// Every token is read and they are folded in order with
    /// [`Self::combine`]: the least reproducible cause present wins, and among
    /// causes of one class the last (outermost) statement wins. A quoted inner
    /// reason that says a clock fired therefore keeps the row not reproducible
    /// whatever a wrapper stated after it. A token naming no known cause is
    /// ignored (it cannot have been written by [`Self::stamp`]).
    #[must_use]
    pub fn from_reason(reason: &str) -> Option<Self> {
        let mut found: Option<Self> = None;
        let mut rest = reason;
        while let Some(open) = rest.find(STOP_TOKEN_OPEN) {
            let after = &rest[open + STOP_TOKEN_OPEN.len()..];
            let Some(close) = after.find(STOP_TOKEN_CLOSE) else { break };
            if let Some(cause) = Self::parse(&after[..close]) {
                found = Some(match found {
                    Some(earlier) => Self::combine(earlier, cause),
                    None => cause,
                });
            }
            rest = &after[close..];
        }
        found
    }

    /// The stop cause of a router/backend result.
    ///
    /// A verdict is `solved`; a `Timeout` is a clock by construction; an
    /// `Unknown` is whatever its producer stated, and `unclassified` when it
    /// stated nothing.
    #[must_use]
    pub fn of_result(result: &VerificationResult) -> Self {
        match result {
            VerificationResult::Proved { .. } | VerificationResult::Failed { .. } => Self::Solved,
            VerificationResult::Timeout { .. } => Self::WallBackstop,
            VerificationResult::Unknown { reason, .. } => {
                Self::from_reason(reason).unwrap_or(Self::Unclassified)
            }
        }
    }

    /// The stop cause of one transported/reported obligation row.
    ///
    /// A stated cause wins, except over an outcome that is itself a clock: a
    /// `timeout`/`canceled` row is at least `wall-backstop` whatever its reason
    /// states ([`Self::combine`]). Without a stated cause the outcome decides
    /// where the outcome itself says why the search ended (a verdict, a
    /// timeout, an admitted assumption, an unencodable obligation); an
    /// undecided row that says nothing is `unclassified`.
    #[must_use]
    pub fn of_outcome(outcome: Outcome, reason: Option<&str>) -> Self {
        let stated = reason.and_then(Self::from_reason);
        match (outcome, stated) {
            (Outcome::Timeout | Outcome::Canceled, Some(cause)) => {
                Self::combine(cause, Self::WallBackstop)
            }
            (_, Some(cause)) => cause,
            (Outcome::Proved | Outcome::Failed | Outcome::Rejected, None) => Self::Solved,
            (Outcome::Timeout | Outcome::Canceled, None) => Self::WallBackstop,
            (Outcome::Skipped, None) => Self::NotDispatched,
            (Outcome::Unsupported, None) => Self::Unsupported,
            (Outcome::Unknown | Outcome::RuntimeChecked, None) => Self::Unclassified,
        }
    }
}

impl PartialOrd for StopCause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by canonical NAME, never by severity: the order exists so tallies
/// and vectors serialize in one byte sequence, and a comparison that silently
/// meant "worse" is how a gate ends up ranking one stop above another.
impl Ord for StopCause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl fmt::Display for StopCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

const STOP_TOKEN_OPEN: &str = "[stop:";
const STOP_TOKEN_CLOSE: &str = "]";

fn strip_trailing_token(detail: &str) -> &str {
    let trimmed = detail.trim_end();
    if let Some(body) = trimmed.strip_suffix(STOP_TOKEN_CLOSE)
        && let Some(open) = body.rfind(STOP_TOKEN_OPEN)
        && StopCause::parse(&body[open + STOP_TOKEN_OPEN.len()..]).is_some()
    {
        return body[..open].trim_end();
    }
    trimmed
}

impl StopCause {
    /// [`Self::stamp`], naming the stop as `item` as well: `detail`, then the
    /// item's `[stop-item:<name>]` token, then the trailing stop token. The
    /// cause is combined with any the detail already states, exactly as
    /// [`Self::stamp`] combines it, so naming an item never makes a row more
    /// reproducible.
    #[must_use]
    pub fn stamp_item(self, item: StopItem, detail: &str) -> String {
        let cause = match Self::from_reason(detail) {
            Some(inner) => Self::combine(inner, self),
            None => self,
        };
        let body = strip_trailing_token(detail);
        if body.is_empty() {
            format!("{} {}", item.token_str(), cause.token_str())
        } else {
            format!("{body} {} {}", item.token_str(), cause.token_str())
        }
    }

    /// An `Unknown` result whose search ended for this cause, named as `item`.
    #[must_use]
    pub fn unknown_result_item(
        self,
        item: StopItem,
        solver: &str,
        time_ms: u64,
        detail: &str,
    ) -> VerificationResult {
        VerificationResult::Unknown {
            solver: solver.into(),
            time_ms,
            reason: self.stamp_item(item, detail),
        }
    }
}

/// A NAMED stop: one known way a search ends — or a computed verdict is thrown
/// away — that its [`StopCause`] alone does not tell apart from others of its
/// class. Each item is counted by name, in the unit's tally
/// ([`StopItemTally`]) and in the backstop ledger ([`note_item`]), so the work
/// it discards is sized and owed by name (the seal backlog), and each has
/// exactly one stop cause ([`StopItem::cause`]).
///
/// The wording that identifies an item is ay's, so recognising it is the
/// router's job; the item then rides in the row's reason as one
/// `[stop-item:<name>]` token ([`StopCause::stamp_item`]), just before the
/// row's `[stop:<cause>]` token, and is read back by [`StopItem::from_reason`].
/// Recorded 2026-09-30 from the release lane's logs (the 0.99 lane, 81 logs,
/// and run D): the counts in each variant's doc are those logs'.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum StopItem {
    /// ay's strict proof check was CANCELLED ("proof validation cancelled by
    /// the caller (interrupt, deadline, or memory limit)", ay
    /// `ProofCheckError::Cancelled`), which mandatory certification turns into
    /// a rejected UNSAT. Most of these are the post-validator stop: after a
    /// validation that reached its LAST step, ay polls the executor's stop
    /// signal once more (ay `strict_check_progress.rs`,
    /// `check_with_executor_progress_reporting_work` and
    /// `check_proof_gate_under_controls`, at main's pin cb87694a9) and, if the
    /// deadline or an interrupt is already set, throws the checked proof away
    /// (0.99 lane: 3,439 of 4,042 cancelled checks had checked every step). The
    /// native-replay authority refusal with every step checked is the same
    /// stop. Trust's ay pin (ffaba97f6) carries ay's
    /// `fix/strict-check-accept-completed`: a validation that reached its last
    /// step is accepted and the stop signal is honoured only between steps, so
    /// the cancellations left are genuine mid-check stops — a clock, an
    /// interrupt or a memory reading, none of them reproducible:
    /// `wall-backstop`.
    StrictCheckCancelled,
    /// Mandatory strict certification rejected a computed UNSAT whose proof
    /// "uses unverified trust rule" (0.99 lane: 545). The trust steps are what
    /// ay's deferred discharge left undischarged. Since P4a.1 (ay ffaba97f6)
    /// that discharge draws its nested solves from the solved query's own
    /// effort count, never a clock, and a stop that ended it is published as
    /// that stop: a refusal is the proof's, `solver-incomplete`, owed by name
    /// until ay removes the trust rules. A discharge whose count ran out says
    /// so and is [`StopItem::CertificationEffort`] instead.
    UnverifiedTrustRule,
    /// Mandatory strict certification rejected a computed UNSAT whose proof
    /// "uses unsupported theory lemma kind Generic in strict mode" (0.99 lane:
    /// 493). Decided after the same counted discharge: `solver-incomplete`,
    /// owed until ay reconstructs Generic lemmas.
    GenericTheoryLemma,
    /// Mandatory strict certification rejected a computed UNSAT because "proof
    /// validation resource envelope exhausted" (ay `ProofCheckError::
    /// ResourceLimit`, the `BudgetRefused` limb: a COUNT envelope of check work
    /// and bytes, `MAX_CHECK_WORK` / `MAX_CHECK_BYTES`; 0.99 lane: 211). A
    /// budget stop, not a proof defect. The proof it measured came through the
    /// discharge, which is counted since P4a.1, so the row is the count it is:
    /// `effort`.
    ProofCheckEnvelope,
    /// ay's certification funnel refused a computed UNSAT because the
    /// deferred-trust discharge spent the effort it draws from the solved
    /// query's own count ("certification effort exhausted (spent S of A)", ay
    /// `api/proofs/certification_effort.rs`, P4a.1). A count, so `effort`: the
    /// same query on any host spends the same draws and refuses the same way.
    CertificationEffort,
    /// ay degraded a SAT answer to `unknown` because its model failed
    /// validation ("model validation violated: <boundary>: <detail>"; in
    /// process, `ExecuteDegradationKind::UnvalidatedSatBoundary`; 0.99 lane:
    /// 3,673). A deterministic gate over the model the search produced:
    /// `solver-incomplete`, named so the theory lanes it points at are owed.
    ModelValidationViolated,
    /// ay's SAT finalization found a model that violates an original clause
    /// (`FINALIZE_SAT_FAIL: BUG: original clause ... unsatisfied`, or the
    /// release-mode re-verification's "Invalid SAT model"; ay-sat
    /// `finalize_sat.rs`): an ay defect, degraded to `unknown`, and it poisons
    /// any later UNSAT of the same solve. A `solver-fault`.
    InvalidSatModel,
}

impl StopItem {
    /// Every item, in canonical-name order.
    pub const ALL: [Self; 7] = [
        Self::CertificationEffort,
        Self::GenericTheoryLemma,
        Self::InvalidSatModel,
        Self::ModelValidationViolated,
        Self::ProofCheckEnvelope,
        Self::StrictCheckCancelled,
        Self::UnverifiedTrustRule,
    ];

    /// The canonical serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StrictCheckCancelled => "strict-check-cancelled",
            Self::UnverifiedTrustRule => "unverified-trust-rule",
            Self::GenericTheoryLemma => "generic-theory-lemma",
            Self::ProofCheckEnvelope => "proof-check-envelope",
            Self::CertificationEffort => "certification-effort",
            Self::ModelValidationViolated => "model-validation-violated",
            Self::InvalidSatModel => "invalid-sat-model",
        }
    }

    /// Parse the canonical spelling. Anything else is refused.
    #[must_use]
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "strict-check-cancelled" => Some(Self::StrictCheckCancelled),
            "unverified-trust-rule" => Some(Self::UnverifiedTrustRule),
            "generic-theory-lemma" => Some(Self::GenericTheoryLemma),
            "proof-check-envelope" => Some(Self::ProofCheckEnvelope),
            "certification-effort" => Some(Self::CertificationEffort),
            "model-validation-violated" => Some(Self::ModelValidationViolated),
            "invalid-sat-model" => Some(Self::InvalidSatModel),
            _ => None,
        }
    }

    /// The stop cause a row this item names carries.
    #[must_use]
    pub const fn cause(self) -> StopCause {
        match self {
            Self::StrictCheckCancelled => StopCause::WallBackstop,
            Self::ProofCheckEnvelope | Self::CertificationEffort => StopCause::Effort,
            Self::UnverifiedTrustRule
            | Self::GenericTheoryLemma
            | Self::ModelValidationViolated => StopCause::SolverIncomplete,
            Self::InvalidSatModel => StopCause::SolverFault,
        }
    }

    /// The machine token this item is carried as inside a free-text reason.
    #[must_use]
    pub const fn token_str(self) -> &'static str {
        match self {
            Self::StrictCheckCancelled => "[stop-item:strict-check-cancelled]",
            Self::UnverifiedTrustRule => "[stop-item:unverified-trust-rule]",
            Self::GenericTheoryLemma => "[stop-item:generic-theory-lemma]",
            Self::ProofCheckEnvelope => "[stop-item:proof-check-envelope]",
            Self::CertificationEffort => "[stop-item:certification-effort]",
            Self::ModelValidationViolated => "[stop-item:model-validation-violated]",
            Self::InvalidSatModel => "[stop-item:invalid-sat-model]",
        }
    }

    /// The machine token this item is carried as inside a free-text reason.
    #[must_use]
    pub fn token(self) -> String {
        self.token_str().to_string()
    }

    /// The item `reason` names, if any: the LAST well-formed item token (the
    /// outermost statement; a quoted inner reason's item is superseded).
    #[must_use]
    pub fn from_reason(reason: &str) -> Option<Self> {
        let mut found = None;
        let mut rest = reason;
        while let Some(open) = rest.find(ITEM_TOKEN_OPEN) {
            let after = &rest[open + ITEM_TOKEN_OPEN.len()..];
            let Some(close) = after.find(STOP_TOKEN_CLOSE) else { break };
            if let Some(item) = Self::parse(&after[..close]) {
                found = Some(item);
            }
            rest = &after[close..];
        }
        found
    }
}

impl PartialOrd for StopItem {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by canonical NAME, as [`StopCause`] is.
impl Ord for StopItem {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl fmt::Display for StopItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

const ITEM_TOKEN_OPEN: &str = "[stop-item:";

/// Per-unit count of obligations by named stop ([`StopItem`]).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct StopItemTally(BTreeMap<StopItem, u64>);

impl StopItemTally {
    /// Count one obligation.
    pub fn record(&mut self, item: StopItem) {
        *self.0.entry(item).or_insert(0) += 1;
    }

    /// Obligations named `item`.
    #[must_use]
    pub fn count(&self, item: StopItem) -> u64 {
        self.0.get(&item).copied().unwrap_or(0)
    }

    /// Whether no obligation was named.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// `item=count` pairs in canonical order.
    #[must_use]
    pub fn render(&self) -> String {
        if self.0.is_empty() {
            return "none".to_string();
        }
        use std::fmt::Write as _;
        let mut out = String::with_capacity(self.0.len() * 24);
        for (i, (item, count)) in self.0.iter().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            out.push_str(item.as_str());
            out.push('=');
            let _ = write!(out, "{count}");
        }
        out
    }
}

impl FromIterator<StopItem> for StopItemTally {
    fn from_iter<I: IntoIterator<Item = StopItem>>(iter: I) -> Self {
        let mut tally = Self::default();
        for item in iter {
            tally.record(item);
        }
        tally
    }
}

/// Backstops, and stops nobody explained, that fired somewhere in one compile,
/// by the lane that saw them (plan §2: a unit is `not-reproducible` when at
/// least one backstop fired, whether or not the result it ended became a row),
/// and every NAMED stop ([`StopItem`]) the lanes saw.
///
/// The compiler consumes many solver results internally — the whole-crate R1
/// harvest, refutation attempts, S1 strict revalidation, proof-authority
/// lanes. A clock that ends one of those can change which published rows are
/// decided without appearing in any row's reason. Every solver lane and budget
/// scope therefore reports a non-deterministic stop here ([`note_stop`]), and
/// the compiler publishes the ledger once per crate ([`take_noted_stops`]).
/// A named stop is recorded whatever its class ([`note_item`]): the work it
/// discards is counted by name wherever it happened. A deterministic named
/// entry never affects the unit outcome; the outcome takes each entry's cause.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NotedStop {
    /// The lane that saw the stop (a fixed, human-readable name).
    pub lane: String,
    /// What ended the work. Deterministic only on a named entry or a solver
    /// count stop (`effort`).
    pub cause: StopCause,
    /// The named stop, when the lane recognised one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub item: Option<StopItem>,
    /// How many times this lane saw this cause (and item).
    pub count: u64,
}

impl fmt::Display for NotedStop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            Some(item) => write!(f, "{} {}[{item}]={}", self.lane, self.cause, self.count),
            None => write!(f, "{} {}={}", self.lane, self.cause, self.count),
        }
    }
}

type LedgerSubKey = (StopCause, Option<StopItem>);
type LedgerMap = BTreeMap<String, BTreeMap<LedgerSubKey, u64>>;

/// The process-wide backstop ledger: `lane -> (cause, item) -> count`.
/// Process-wide, not thread-local, on purpose: solver work runs on rayon pool
/// threads as well as on the thread that verifies the function, and the unit it
/// bears on is the whole crate the process compiles.
static NOTED_STOPS: std::sync::Mutex<LedgerMap> = std::sync::Mutex::new(BTreeMap::new());

fn noted_stop_ledger() -> std::sync::MutexGuard<'static, LedgerMap> {
    // A poisoned ledger still holds every stop noted before the panic; losing
    // them would let a clock-ended compile read as measured.
    NOTED_STOPS.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn record_in_ledger(lane: &str, cause: StopCause, item: Option<StopItem>) {
    let mut ledger = noted_stop_ledger();
    if let Some(sub) = ledger.get_mut(lane) {
        *sub.entry((cause, item)).or_insert(0) += 1;
    } else {
        ledger.insert(lane.to_string(), BTreeMap::from([((cause, item), 1)]));
    }
}

/// Record that `cause` ended some work in `lane`.
///
/// Recorded: every cause that is not deterministic, and `effort` — the one
/// solver COUNT — so how often that count binds is visible wherever the
/// stopped work went, in a row or not (a refutation attempt, a bridged solve
/// whose row another lane produced). A deterministic entry never changes the
/// unit outcome. Other deterministic causes are not recorded: they end the
/// same work the same way on every run.
pub fn note_stop(lane: &str, cause: StopCause) {
    if cause.reproducibility() == Reproducibility::Deterministic && cause != StopCause::Effort {
        return;
    }
    record_in_ledger(lane, cause, None);
    // T3 L4 (C06a): the same stop, attributed to its body, for the elision audit.
    crate::audit_ledger::stop(lane, cause, None);
}

/// Plan §3.7 (review 2026-09-30): fold the COUNT stop of a lane that
/// tried an obligation and did not decide it into the row ANOTHER lane
/// produced for the same obligation, which is the row that survives.
///
/// `None` unless `lane_result` is an `Unknown` whose stated cause is a solver
/// count ([`StopCause::is_solver_count`]). Otherwise the row's reason, with a
/// clause naming the lane and its stop, under one trailing token: the row's
/// own cause combined with the lane's ([`StopCause::combine`]), where a row
/// that states no cause counts as `unclassified`. So a deterministic row
/// (`unsupported`) now states the count that also ended it, while a row a
/// clock ended stays `wall-backstop` and a row that states nothing stays
/// `unclassified` — an unexplained stop may be a clock the row cannot see, and
/// naming a count must never make it read as reproducible.
#[must_use]
pub fn fold_lane_count_stop(
    row_reason: &str,
    lane: &str,
    lane_result: &VerificationResult,
) -> Option<String> {
    let VerificationResult::Unknown { reason: lane_reason, .. } = lane_result else {
        return None;
    };
    let lane_cause = StopCause::from_reason(lane_reason)?;
    if !lane_cause.is_solver_count() {
        return None;
    }
    let row_cause = StopCause::from_reason(row_reason).unwrap_or(StopCause::Unclassified);
    let cause = StopCause::combine(row_cause, lane_cause);
    let detail = format!(
        "{}; {lane} stopped on its {lane_cause} count: {}",
        strip_trailing_token(row_reason),
        strip_trailing_token(lane_reason),
    );
    Some(cause.stamp(&detail))
}

/// [`fold_lane_count_stop`], and also the RESOURCE backstop of a lane that
/// tried an obligation and did not decide it ([`StopCause::is_resource_backstop`]):
/// ay's process-memory ceiling, the router memory guard, a solver fault.
///
/// Measured 2026-10-02 (trust main `d36c551fac`, aterm-grid, advisory lane):
/// the trustc process footprint peaked at 5.4 GiB against the in-process ay
/// ceiling of RAM/8 (3 GiB on a 24 GiB host; the seal run peaked at 2.8 GiB),
/// the unit's backstop ledger counted 532 in-process ay `rss-backstop` stops,
/// and no function verified after about 60% of the crate carries any ay or
/// kernel time. The ay bridge kept the native row wherever ay stopped, so 21
/// rows the seal toolchain proves read `unknown`/`runtime_checked` with the
/// native bundle's refusal text ("constructor member has no complete exact root
/// invocation path") and `[stop:unclassified]` — a typed-input refusal that is
/// not why they are unproved: the same refusal leaves ay's kernel-certified
/// proof in place when the ceiling has not fired. With this fold the row states
/// the backstop.
///
/// `None` unless `lane_result` is an `Unknown` whose stated cause is a solver
/// count or a resource backstop. The row's cause is combined with the lane's
/// ([`StopCause::combine`]): every resource backstop is not reproducible, so a
/// deterministic row (`unsupported`) and a row that stated nothing
/// (`unclassified`) both become the backstop, while a row the verifier could not
/// run at all stays `admission-refused`. Text and stop cause only: the row stays
/// as undecided as it was.
#[must_use]
pub fn fold_lane_stop(
    row_reason: &str,
    lane: &str,
    lane_result: &VerificationResult,
) -> Option<String> {
    if let Some(folded) = fold_lane_count_stop(row_reason, lane, lane_result) {
        return Some(folded);
    }
    let VerificationResult::Unknown { reason: lane_reason, .. } = lane_result else {
        return None;
    };
    let lane_cause = StopCause::from_reason(lane_reason)?;
    if !lane_cause.is_resource_backstop() {
        return None;
    }
    let row_cause = StopCause::from_reason(row_reason).unwrap_or(StopCause::Unclassified);
    let cause = StopCause::combine(row_cause, lane_cause);
    let detail = format!(
        "{}; {lane} stopped on {lane_cause} before it decided: {}",
        strip_trailing_token(row_reason),
        strip_trailing_token(lane_reason),
    );
    Some(cause.stamp(&detail))
}

/// Record that the named stop `item` ended some work in `lane`, with the cause
/// the work carried (`cause`, at least as unreproducible as the item's own). A
/// named stop is recorded whatever its class: it is counted by name wherever it
/// happened, in a row or not.
pub fn note_item(lane: &str, cause: StopCause, item: StopItem) {
    record_in_ledger(lane, cause, Some(item));
    // T3 L4 (C06a): the same stop, attributed to its body, for the elision audit.
    crate::audit_ledger::stop(lane, cause, Some(item));
}

/// [`note_stop`] with the stop cause of a solver result ([`StopCause::of_result`]),
/// or [`note_item`] when its reason names a stop ([`StopItem::from_reason`]).
/// Call it on the result a lane RETURNS, after any retry it runs, so a stop the
/// lane itself recovered from is not reported twice.
pub fn note_result(lane: &str, result: &VerificationResult) {
    let cause = StopCause::of_result(result);
    let item = match result {
        VerificationResult::Unknown { reason, .. } => StopItem::from_reason(reason),
        _ => None,
    };
    match item {
        Some(item) => note_item(lane, cause, item),
        None => note_stop(lane, cause),
    }
}

/// Every stop noted so far, in canonical `(lane, cause, item)` order, without
/// clearing the ledger.
#[must_use]
pub fn noted_stops() -> Vec<NotedStop> {
    ledger_rows(&noted_stop_ledger())
}

/// Every stop noted so far, clearing the ledger: the compiler calls this once,
/// when it publishes the crate's accounting, so a later compile in the same
/// process starts empty.
#[must_use]
pub fn take_noted_stops() -> Vec<NotedStop> {
    ledger_rows(&std::mem::take(&mut *noted_stop_ledger()))
}

fn ledger_rows(ledger: &LedgerMap) -> Vec<NotedStop> {
    ledger
        .iter()
        .flat_map(|(lane, sub)| {
            sub.iter().map(move |((cause, item), count)| NotedStop {
                lane: lane.clone(),
                cause: *cause,
                item: *item,
                count: *count,
            })
        })
        .collect()
}

/// One unit's outcome (plan §2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum UnitOutcome {
    /// Every stop cause is deterministic.
    Measured,
    /// At least one stop cause is not reproducible.
    NotReproducible,
    /// The verifier could not run; there is no count.
    CouldNotRun,
}

impl UnitOutcome {
    /// The canonical serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Measured => "measured",
            Self::NotReproducible => "not-reproducible",
            Self::CouldNotRun => "could-not-run",
        }
    }

    /// The outcome of a unit whose obligations ended for `causes`.
    ///
    /// One refused admission makes the unit `could-not-run`; otherwise one
    /// non-reproducible cause makes it `not-reproducible`. An empty unit is
    /// `measured`: it has no stop that could differ between runs.
    #[must_use]
    pub fn from_causes(causes: impl IntoIterator<Item = StopCause>) -> Self {
        let mut outcome = Self::Measured;
        for cause in causes {
            match cause.reproducibility() {
                Reproducibility::CouldNotRun => return Self::CouldNotRun,
                Reproducibility::NotReproducible => outcome = Self::NotReproducible,
                Reproducibility::Deterministic => {}
            }
        }
        outcome
    }
}

impl fmt::Display for UnitOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Per-unit count of obligations by stop cause (plan §3.7).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct StopCauseTally(BTreeMap<StopCause, u64>);

impl StopCauseTally {
    /// Count one obligation.
    pub fn record(&mut self, cause: StopCause) {
        *self.0.entry(cause).or_insert(0) += 1;
    }

    /// Obligations that stopped for `cause`.
    #[must_use]
    pub fn count(&self, cause: StopCause) -> u64 {
        self.0.get(&cause).copied().unwrap_or(0)
    }

    /// Every recorded `(cause, count)`, in canonical-name order.
    pub fn iter(&self) -> impl Iterator<Item = (StopCause, u64)> + '_ {
        self.0.iter().map(|(cause, count)| (*cause, *count))
    }

    /// The unit outcome these stops imply.
    #[must_use]
    pub fn outcome(&self) -> UnitOutcome {
        UnitOutcome::from_causes(self.0.keys().copied())
    }

    /// `cause=count` pairs in canonical order, e.g. `effort=3 solved=40`.
    #[must_use]
    pub fn render(&self) -> String {
        if self.0.is_empty() {
            return "none".to_string();
        }
        use std::fmt::Write as _;
        let mut out = String::with_capacity(self.0.len() * 20);
        for (i, (cause, count)) in self.0.iter().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            out.push_str(cause.as_str());
            out.push('=');
            let _ = write!(out, "{count}");
        }
        out
    }
}

impl FromIterator<StopCause> for StopCauseTally {
    fn from_iter<I: IntoIterator<Item = StopCause>>(iter: I) -> Self {
        let mut tally = Self::default();
        for cause in iter {
            tally.record(cause);
        }
        tally
    }
}

/// One row of a verdict vector: `(stable obligation key, status, stop cause)`.
///
/// The key must be free of volatile identity — no package ID (it embeds the
/// absolute checkout path), no bundle or crate hash (it moves with the package
/// version), no session nonce — or two runs over the same inputs disagree on
/// the key rather than on the verdict. [`VerdictEntry::new`] refuses a key that
/// visibly carries one.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VerdictEntry {
    /// The stable obligation key, `<def_path>#<local id>`
    /// ([`crate::obligation_identity::obligation_key`]): content-addressed, so
    /// renumbering a sibling or editing unrelated code leaves it alone. Never
    /// the compiler's ordinal `obligation_id`, which is a binding token only.
    pub obligation: String,
    /// The published status.
    pub status: String,
    /// What ended the search.
    pub stop: StopCause,
}

/// A key rejected as a verdict-vector key, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VolatileObligationKey {
    /// The rejected key.
    pub key: String,
    /// Which volatile component it carries.
    pub reason: &'static str,
}

impl fmt::Display for VolatileObligationKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "obligation key `{}` is not a verdict-vector key: {}", self.key, self.reason)
    }
}

impl VerdictEntry {
    /// A vector row, refusing a key that carries volatile identity.
    ///
    /// # Errors
    ///
    /// The key names a crate hash (`rustc-crate:`), a package ID or absolute
    /// path, or is empty.
    pub fn new(
        obligation: impl Into<String>,
        status: Outcome,
        stop: StopCause,
    ) -> Result<Self, VolatileObligationKey> {
        let obligation = obligation.into();
        if let Some(reason) = volatile_key_component(&obligation) {
            return Err(VolatileObligationKey { key: obligation, reason });
        }
        Ok(Self { obligation, status: status.as_str().to_string(), stop })
    }
}

fn volatile_key_component(key: &str) -> Option<&'static str> {
    if key.trim().is_empty() {
        return Some("it is empty");
    }
    if key.contains("rustc-crate:") {
        return Some("it names a crate hash, which moves with the package version");
    }
    if key.contains("path+file://")
        || key.contains("registry+")
        || key.contains("git+")
        || key.starts_with('/')
        || key.contains(":/")
    {
        return Some("it names a package ID or an absolute path, which moves with the checkout");
    }
    None
}

/// The canonical per-unit verdict vector and its digest (plan §2).
///
/// Canonical order is total — `(obligation, status, stop)` — so the digest does
/// not depend on the order rows were produced in. Duplicate keys are kept: a
/// key that occurs twice is part of what the unit produced, and dropping one
/// would let two different productions share a digest.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerdictVector {
    entries: Vec<VerdictEntry>,
}

/// Domain separator of the vector digest. Bump the version when the encoding
/// or the meaning of a field changes, so old and new digests never compare
/// equal by accident. v2: the key is the stable `<def_path>#<local id>` (T9);
/// v1 keyed on the ordinal obligation id.
pub const VERDICT_VECTOR_DOMAIN: &[u8] = b"trust-verdict-vector/v2\0";

impl VerdictVector {
    /// Build the canonical vector.
    #[must_use]
    pub fn new(mut entries: Vec<VerdictEntry>) -> Self {
        entries.sort_by(|a, b| {
            (a.obligation.as_str(), a.status.as_str(), a.stop.as_str()).cmp(&(
                b.obligation.as_str(),
                b.status.as_str(),
                b.stop.as_str(),
            ))
        });
        Self { entries }
    }

    /// The canonical rows.
    #[must_use]
    pub fn entries(&self) -> &[VerdictEntry] {
        &self.entries
    }

    /// Stop-cause tally over the rows.
    #[must_use]
    pub fn tally(&self) -> StopCauseTally {
        self.entries.iter().map(|entry| entry.stop).collect()
    }

    /// Lowercase SHA-256 hex of the canonical encoding: the domain, then every
    /// row as three length-prefixed fields. Two runs agree exactly when their
    /// digests are equal.
    #[must_use]
    pub fn digest(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(VERDICT_VECTOR_DOMAIN);
        hasher.update((self.entries.len() as u64).to_le_bytes());
        for entry in &self.entries {
            for field in [entry.obligation.as_str(), entry.status.as_str(), entry.stop.as_str()] {
                hasher.update((field.len() as u64).to_le_bytes());
                hasher.update(field.as_bytes());
            }
        }
        lowercase_hex(&hasher.finalize())
    }

    /// The first rows at which `self` and `other` differ, for a report that
    /// has to say WHERE two runs disagreed. `None` for identical vectors.
    #[must_use]
    pub fn first_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Option<(Option<&'a VerdictEntry>, Option<&'a VerdictEntry>)> {
        let len = self.entries.len().max(other.entries.len());
        (0..len).find_map(|index| {
            let left = self.entries.get(index);
            let right = other.entries.get(index);
            (left != right).then_some((left, right))
        })
    }
}

/// The number of distinct terms in the DAG of `assertions`, taken together:
/// the query size the one effort count scales with (plan §3.2a; DECISION_QUEUE
/// BUDGET-1).
///
/// Every structurally identical subterm counts once, across all the
/// assertions, and variables and constants count. A consistent renaming leaves
/// it unchanged, and tree duplication is not counted. It is
/// [`trust_ir_contract::formula_dag::FormulaDag`]'s node count — the
/// hash-consed store keyed on (payload, child ids) by exact equality, built by
/// an iterative walk over the exhaustive `Formula::children` — so no variant is
/// skipped or counted as an opaque leaf, and the definition is the one the
/// toolchain already has (trust-mc's 8e ruling names the same measure: "k × the
/// query's distinct nodes").
#[must_use]
pub fn query_size(assertions: &[&Formula]) -> u64 {
    let mut dag = trust_ir_contract::formula_dag::FormulaDag::new();
    for assertion in assertions {
        dag.intern(assertion);
    }
    u64::try_from(dag.len()).unwrap_or(u64::MAX)
}

/// The one solver-effort count (plan §3.2a; DECISION_QUEUE BUDGET-1): every ay
/// query `q` is bounded by
///
/// ```text
/// effort(q) = min(C, max(1, k · size(q)))   SAT conflicts, saturating
/// ```
///
/// where `size` is [`query_size`] over every assertion in scope at that
/// check-sat, `k` is this scale (the profile's single `effort` field) and `C`
/// is [`Self::CEILING`]. It reaches ay as `(set-option :rlimit effort(q))`
/// before every check-sat on the three trust-router ingress points (the
/// in-process program, the subprocess session, the one-shot script). Those
/// lanes have no other Trust count: no per-function cap, no flat per-VC budget.
///
/// Not covered yet (T2 dependencies, recorded, not papered over):
///
/// * trust-certify's direct ay solves (the clean-auto `AyProofBackend` and the
///   datatype no-confusion check) send no `:rlimit`. They run under ay's flat
///   ground allowance and a 90 s clock read from `AY_DIRECT_SOLVE_TIMEOUT_MS`
///   (`first-party/clean`, `execution.rs`), and their answers grade
///   `Certified` rows. Plan §3.6 gives clean-auto and kernel certification
///   the same count in T2.
/// * ay's residual clocks run on wall time inside a query until P4a counts
///   them. At Trust's ay pin (da447f9a6) the strict-proof discharge (P4a.1),
///   the eager-persistent split-loop arm and every BV/FP bit-blast solve (P4a)
///   run on counts under `:rlimit`, the bit-blast solves on ay-sat's counted
///   inprocessing schedules too, and the clock reads left on those paths only
///   stop, each published as the stop it is. What remains is ay-sat's
///   wall-capped restart inprocessing and lookahead in every other SAT solve
///   (the eager-persistent arm's among them): ay's process-wide
///   `--sat-deterministic-inproc` is off by default and only the bit-blast
///   arms switch it on per solver. Such a cap never ends a search, but it moves
///   where the count stops one. A query that is slow per conflict can still
///   reach the per-query clock before its count: it stops `wall-backstop` and
///   its unit is not reproducible. The count does not stand in front of every
///   query's clock; [`Self::CEILING`] says where it does.
///
/// What the pinned ay does with it (ay `01b58012`, MEASURED in its source):
///
/// * `:rlimit` REPLACES ay's default per-SAT-solve conflict allowance
///   (`pipeline_fns::effective_conflict_allowance`: `resource_limit.or_else(..)`),
///   so that allowance is not a second count under this one.
/// * It bounds EACH SAT solve inside a check-sat, not the whole check: a check
///   that runs several SAT solves can spend more than `effort(q)`. The
///   check-wide count needs ay's deterministic effort API (trust-mc ay-ask
///   2026-10-01 item 2): a T2 dependency.
/// * ay's default per-SAT-solve DECISION allowance (24,000,000) stays in force
///   under `:rlimit` (`effective_decision_allowance`: `:rlimit` does not replace
///   it) and the pinned ay has no SMT-LIB option to set it. It is therefore a
///   second, ay-internal count that a decision-heavy, conflict-light search can
///   stop on (reported `effort`). Deleting it — one count under a deterministic
///   node, ay's allowances applying only where no `:rlimit` is set — is T2's
///   change in ay: a T2 dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct EffortScale {
    /// `k`: SAT conflicts per distinct query term, `1..=C`.
    pub conflicts_per_node: u64,
}

impl EffortScale {
    /// `C`: the most conflicts one query is given. It is P2's flat per-query
    /// count, the reference the calibration rule measures against (BUDGET-1),
    /// so no query is given more search than P2 gave every query. Two reasons
    /// it is not ay's 400,000-conflict ground allowance:
    ///
    /// * The clock. 100,000 conflicts cost 1.57-1.71 s of CPU on the idle m3
    ///   host (MEASURED 2026-09-29, `scripts/measure_ay_conflict_rate.py`,
    ///   pigeonhole PHP(10,9) on the `ay` beside seal 321aaeda7's `trustc`), so
    ///   a SAT solve its count stops has used about a third of the
    ///   unchanged 5,000 ms per-query clock ([`Backstop::vc_clock_ms`]).
    ///   400,000 would be 6.3-6.8 s, behind that clock, so on a large query
    ///   the clock rather than the count would end an undecided search. That
    ///   holds per SAT solve on an idle host, and only for queries whose time
    ///   goes into conflicts (see the type docs for the queries it does not
    ///   cover).
    /// * ay's bound. It is below ay's per-SAT-solve ground allowance (400,000
    ///   at ay `01b58012`, `Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE`,
    ///   `pub(crate)`), which an explicit `:rlimit` replaces, so the count only
    ///   ever tightens ay's own bound. The ay pin train re-checks that ay's
    ///   allowance stays at or above it.
    ///
    /// T2 deletes the clamp when ay's check-wide tick budget replaces
    /// `:rlimit`. Any change here is a profile schema change.
    pub const CEILING: u64 = 100_000;

    /// The built-in `k`: PROVISIONAL, fitted by the committed harness
    /// `crates/trust-vcgen/tests/effort_calibration.rs` until `targo trust
    /// calibrate` and the per-query ledger it reads exist (DECISION_QUEUE
    /// BUDGET-1a records how this fit differs from BUDGET-1's).
    ///
    /// The rule is BUDGET-1's: the k that keeps the most decided queries at
    /// no more total projected conflicts than P2's flat 100,000 per query,
    /// ties going to the smaller k. With [`Self::CEILING`] equal to that
    /// reference no k projects more, so the rule picks the least grid k that
    /// keeps every query the reference decides. That k is then taken with a
    /// margin of 2. On the pinned ay the conflicts a query needs move with
    /// timing (ay's residual clocks), and at the rule's exact k a query at the
    /// edge is decided idle and lost under load: `cex_grounding_castu_unminable`
    /// VC 2, refuted at 192 alone, came back incomplete in 2 of 4 runs of its
    /// test file at eight threads, and in 0 of 5 at 384, 768 or 1536. The
    /// harness adds one condition: no query the reference decides or stops on
    /// its count may stop on the clock at the fitted k.
    ///
    /// Measured 2026-10-08 on m3 (load 3.6 at the start, 17.5 at the end; ay
    /// at opt-level 3, as trustc links it; 1,432 s), over every in-process ay
    /// query of the real-MIR fixtures under `crates/trust-vcgen/tests/fixtures`
    /// (4,452 queries from 1,788 functions in 1,796 files), behind the shipped
    /// 5,000 ms clock:
    ///
    /// * the reference decides 3,994, each within 1.3 s;
    /// * 3,987 of them are decided at k = 1; 2 need 32, 3 need 64 and 2 need
    ///   192, all of them refutations of a multiplication overflow (the
    ///   largest, `unfolded_const_bound_shift_unsafe_default_mir.json` VC 10,
    ///   132 terms);
    /// * so the rule's k is 192, and with the margin 384, whose projected
    ///   worst case is 0.195 of the reference (`Σ min(C, k · size)` against
    ///   `n · C`);
    /// * solved again at 384, the corpus decides the same 3,994 queries with
    ///   the same outcome each, and no query the reference decides or stops on
    ///   its count moves to the clock. 157 stop on a clock in both runs (ay's
    ///   residual clocks among them, from 364 ms), 13 the reference left to a
    ///   clock end `solver-incomplete` at 384, and 2 the reference left
    ///   `unclassified` near 4.2 s (`mul64_guard_loop_fresh`, both builds)
    ///   end on a clock at 3.9 s; neither stop is reproducible;
    /// * no query of the corpus stopped on `effort` in either run. Its
    ///   undecided queries end on ay's own stops or on a clock, so the count
    ///   bounds them without deciding where they stop. That is the T2
    ///   dependency in the type docs, measured.
    pub const BUILTIN: Self = Self { conflicts_per_node: 384 };

    /// Parse the profile value (`k`).
    ///
    /// # Errors
    ///
    /// Anything but one decimal integer from 1 through [`Self::CEILING`]: `0`
    /// would give every query the one-conflict floor, and a larger `k` changes
    /// nothing a query of size 1 does not already get.
    pub fn parse(raw: &str) -> Result<Self, String> {
        let raw = raw.trim();
        match raw.parse::<u64>() {
            Ok(k) if (1..=Self::CEILING).contains(&k) => Ok(Self { conflicts_per_node: k }),
            Ok(k) => Err(format!(
                "effort {k} is outside 1..={}: it is SAT conflicts per distinct query term, and \
                 one query is never given more than that",
                Self::CEILING
            )),
            Err(_) => Err(format!("`{raw}` is not a positive integer effort scale")),
        }
    }

    /// The effort of a query of `size` distinct terms:
    /// `min(C, max(1, k · size))`, saturating.
    #[must_use]
    pub fn for_size(self, size: u64) -> QueryEffort {
        let conflicts = self.conflicts_per_node.saturating_mul(size).clamp(1, Self::CEILING);
        QueryEffort { size, conflicts }
    }

    /// The effort of the query whose assertions in scope are `assertions`.
    #[must_use]
    pub fn for_query(self, assertions: &[&Formula]) -> QueryEffort {
        self.for_size(query_size(assertions))
    }
}

impl Default for EffortScale {
    fn default() -> Self {
        Self::BUILTIN
    }
}

/// One query's size and the conflicts it is given ([`EffortScale::for_size`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct QueryEffort {
    /// [`query_size`] of the query.
    pub size: u64,
    /// SAT conflicts, always at least 1: ay reads `:rlimit 0` as unbounded.
    pub conflicts: u64,
}

impl QueryEffort {
    /// The SMT-LIB option that installs this effort, as `(name, value)`.
    #[must_use]
    pub fn smt2_option(self) -> (&'static str, String) {
        (":rlimit", self.conflicts.to_string())
    }

    /// The same option as one `(set-option …)` command line.
    #[must_use]
    pub fn smt2_command(self) -> String {
        format!("(set-option :rlimit {})", self.conflicts)
    }

    /// This query's effort split across the variable-disjoint components
    /// (`component_sizes`, each a [`query_size`]) that together stand for it,
    /// in proportion to each component's size: part `i` gets
    /// `conflicts · size_i / Σ size`, rounded down, and never less than one
    /// conflict. The parts sum to at most the whole whenever the whole has at
    /// least one conflict per part; below that each part keeps its floor of
    /// one, because `:rlimit 0` would be unbounded.
    #[must_use]
    pub fn split_by_size(self, component_sizes: &[u64]) -> Vec<QueryEffort> {
        let total: u128 = component_sizes.iter().map(|&size| u128::from(size)).sum();
        component_sizes
            .iter()
            .map(|&size| {
                let share =
                    (u128::from(self.conflicts) * u128::from(size)).checked_div(total).unwrap_or(0);
                QueryEffort { size, conflicts: u64::try_from(share).unwrap_or(u64::MAX).max(1) }
            })
            .collect()
    }
}

/// The one wall-clock backstop knob (plan §3.6; the `[trust] backstop` key): a
/// per-mille multiplier on the reference clocks. The built-in 1000 reproduces
/// today's clocks exactly — 5,000 ms per query and 120,000 ms per function, the
/// values targo has always passed — and no clock value moves before T2 demotes
/// the clocks (the 2026-09-30 review rule: no clock becomes a backstop until a
/// count stands in front of all the work it bounds). A clock that fires is
/// `wall-backstop`; it never produces a verdict count.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Backstop {
    /// Per-mille of the reference clocks, at least 1.
    pub per_mille: u32,
}

impl Backstop {
    /// The built-in multiplier: the reference clocks unchanged.
    pub const BUILTIN: Self = Self { per_mille: 1000 };
    /// The per-query reference clock, in ms, at 1000 per mille.
    pub const REFERENCE_VC_CLOCK_MS: u64 = 5_000;
    /// The per-function reference clock, in ms, at 1000 per mille.
    pub const REFERENCE_FUNCTION_CLOCK_MS: u64 = 120_000;

    /// Parse the profile value (per mille).
    ///
    /// # Errors
    ///
    /// Anything but one decimal integer of at least 1: `0` would be no clock
    /// at all, and the backstop is the bound of the work no count reaches yet.
    pub fn parse(raw: &str) -> Result<Self, String> {
        let raw = raw.trim();
        match raw.parse::<u32>() {
            Ok(0) => Err("backstop must be at least 1 per mille: 0 would stop no work at all, \
                 and the backstop still bounds the work no count reaches yet"
                .to_string()),
            Ok(per_mille) => Ok(Self { per_mille }),
            Err(_) => Err(format!("`{raw}` is not a positive per-mille backstop")),
        }
    }

    /// The per-query clock passed as `-Ztrust-verify-timeout-ms`:
    /// `max(1, 5000 · b / 1000)`.
    #[must_use]
    pub fn vc_clock_ms(self) -> u64 {
        (Self::REFERENCE_VC_CLOCK_MS * u64::from(self.per_mille) / 1000).max(1)
    }

    /// The per-function clock passed as `-Ztrust-verify-function-budget-ms`:
    /// `max(1, 120000 · b / 1000)`.
    #[must_use]
    pub fn function_clock_ms(self) -> u64 {
        (Self::REFERENCE_FUNCTION_CLOCK_MS * u64::from(self.per_mille) / 1000).max(1)
    }
}

impl Default for Backstop {
    fn default() -> Self {
        Self::BUILTIN
    }
}

/// Every value that bounds search in one verified run (plan §3.6), with a
/// schema version. Its canonical hash is the budget profile id: SHA-256 over
/// the schema, the effort scale and the backstop, and nothing else.
///
/// Schema 4 is the only schema this toolchain reads: a record of any other
/// schema is refused by name, with no decode path (intermediate schemas never
/// ship). The decoder reads `schema` before it judges any other field, so a
/// record of an older schema, whose fields differ, is refused for its schema
/// and not for the first field this one lacks.
/// The verification level and policy are lane, not budget — a report records
/// and `targo trust diff` compares them on their own — and the worker-thread
/// count is a scheduling choice: both are outside the id. The derived clocks
/// are recorded in the header beside the id, never hashed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BudgetProfile {
    /// Schema version of this record: [`BUDGET_PROFILE_SCHEMA`].
    pub schema: u32,
    /// Human name. Informational: not part of the id.
    pub name: String,
    /// The one solver-effort count's scale `k` ([`EffortScale`]).
    pub effort: EffortScale,
    /// The wall-clock backstop multiplier ([`Backstop`]).
    pub backstop: Backstop,
    /// Verifier worker threads (`-Ztrust-verify-worker-threads`), 0 = uncapped.
    ///
    /// Recorded, not in the id: no verdict of a measured run can depend on it.
    /// Its one reader is the full verifier's `execute_engine_batches`, whose
    /// batches each read the shared bundle and write only their own result,
    /// joined in batch order; no batch reaches the effort count except through
    /// its own queries, each of which carries its own count; and the router
    /// dispatches serially in input order (plan P4), with no cross-function
    /// solver cache whose fill order could follow the schedule.
    pub worker_threads: u64,
}

/// The fields of a [`BudgetProfile`] record, in their serialized order.
const BUDGET_PROFILE_FIELDS: &[&str] = &["schema", "name", "effort", "backstop", "worker_threads"];

/// Refuse a record of any schema but [`BUDGET_PROFILE_SCHEMA`], by name.
fn readable_budget_profile_schema(schema: u32) -> Result<u32, String> {
    if schema == BUDGET_PROFILE_SCHEMA {
        Ok(schema)
    } else {
        Err(format!(
            "budget profile schema {schema} is not readable by this toolchain, which reads schema \
             {BUDGET_PROFILE_SCHEMA} only; regenerate the report"
        ))
    }
}

impl BudgetProfile {
    /// A decoded schema-4 record, its values validated.
    fn from_record(
        schema: u32,
        name: String,
        effort: EffortScale,
        backstop: Backstop,
        worker_threads: u64,
    ) -> Result<Self, String> {
        let schema = readable_budget_profile_schema(schema)?;
        if !(1..=EffortScale::CEILING).contains(&effort.conflicts_per_node) {
            return Err(format!(
                "effort {} is outside 1..={}: it is SAT conflicts per distinct query term, and \
                 one query is never given more than that",
                effort.conflicts_per_node,
                EffortScale::CEILING
            ));
        }
        if backstop.per_mille == 0 {
            return Err("backstop must be at least 1 per mille: 0 would stop no work at all, \
                 and the backstop still bounds the work no count reaches yet"
                .to_string());
        }
        Ok(Self { schema, name, effort, backstop, worker_threads })
    }
}

impl<'de> Deserialize<'de> for BudgetProfile {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_struct(
            "BudgetProfile",
            BUDGET_PROFILE_FIELDS,
            BudgetProfileVisitor,
        )
    }
}

/// Read one field's value into its slot, remembering the first field seen twice.
fn take_field<'de, A: serde::de::MapAccess<'de>, T: Deserialize<'de>>(
    map: &mut A,
    slot: &mut Option<T>,
    field: &'static str,
    repeated: &mut Option<&'static str>,
) -> Result<(), A::Error> {
    let value = map.next_value()?;
    if slot.replace(value).is_some() && repeated.is_none() {
        *repeated = Some(field);
    }
    Ok(())
}

/// Decodes a [`BudgetProfile`] schema first. A record of another schema is
/// refused by its schema whatever its other fields are; a schema-4 record is
/// then held to exactly the schema-4 fields (an unknown or repeated field is
/// refused, as `deny_unknown_fields` would).
struct BudgetProfileVisitor;

impl<'de> serde::de::Visitor<'de> for BudgetProfileVisitor {
    type Value = BudgetProfile;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a budget profile record")
    }

    fn visit_seq<A: serde::de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        use serde::de::Error;
        let schema: u32 = seq.next_element()?.ok_or_else(|| A::Error::invalid_length(0, &self))?;
        readable_budget_profile_schema(schema).map_err(A::Error::custom)?;
        let name = seq.next_element()?.ok_or_else(|| A::Error::invalid_length(1, &self))?;
        let effort = seq.next_element()?.ok_or_else(|| A::Error::invalid_length(2, &self))?;
        let backstop = seq.next_element()?.ok_or_else(|| A::Error::invalid_length(3, &self))?;
        let worker_threads =
            seq.next_element()?.ok_or_else(|| A::Error::invalid_length(4, &self))?;
        BudgetProfile::from_record(schema, name, effort, backstop, worker_threads)
            .map_err(A::Error::custom)
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        use serde::de::Error;
        let mut schema: Option<u32> = None;
        let mut name: Option<String> = None;
        let mut effort: Option<EffortScale> = None;
        let mut backstop: Option<Backstop> = None;
        let mut worker_threads: Option<u64> = None;
        let mut unknown: Option<String> = None;
        let mut repeated: Option<&'static str> = None;
        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "schema" => take_field(&mut map, &mut schema, "schema", &mut repeated)?,
                "name" => take_field(&mut map, &mut name, "name", &mut repeated)?,
                "effort" => take_field(&mut map, &mut effort, "effort", &mut repeated)?,
                "backstop" => take_field(&mut map, &mut backstop, "backstop", &mut repeated)?,
                "worker_threads" => {
                    take_field(&mut map, &mut worker_threads, "worker_threads", &mut repeated)?;
                }
                _ => {
                    map.next_value::<serde::de::IgnoredAny>()?;
                    unknown.get_or_insert(key);
                }
            }
        }
        let schema = schema.ok_or_else(|| A::Error::missing_field("schema"))?;
        readable_budget_profile_schema(schema).map_err(A::Error::custom)?;
        if let Some(field) = unknown {
            return Err(A::Error::unknown_field(&field, BUDGET_PROFILE_FIELDS));
        }
        if let Some(field) = repeated {
            return Err(A::Error::duplicate_field(field));
        }
        BudgetProfile::from_record(
            schema,
            name.ok_or_else(|| A::Error::missing_field("name"))?,
            effort.ok_or_else(|| A::Error::missing_field("effort"))?,
            backstop.ok_or_else(|| A::Error::missing_field("backstop"))?,
            worker_threads.ok_or_else(|| A::Error::missing_field("worker_threads"))?,
        )
        .map_err(A::Error::custom)
    }
}

/// Current [`BudgetProfile::schema`].
pub const BUDGET_PROFILE_SCHEMA: u32 = 4;

/// Domain separator of the budget profile id.
pub const BUDGET_PROFILE_DOMAIN: &[u8] = b"trust-budget-profile\0";

impl BudgetProfile {
    /// The profile with these bounds, named `builtin` when they are the
    /// built-in ones and `configured` otherwise.
    #[must_use]
    pub fn new(effort: EffortScale, backstop: Backstop, worker_threads: u64) -> Self {
        let name = if effort == EffortScale::BUILTIN && backstop == Backstop::BUILTIN {
            "builtin"
        } else {
            "configured"
        };
        Self {
            schema: BUDGET_PROFILE_SCHEMA,
            name: name.to_string(),
            effort,
            backstop,
            worker_threads,
        }
    }

    /// The built-in profile targo uses when a workspace declares no budgets.
    #[must_use]
    pub fn builtin() -> Self {
        Self::new(EffortScale::BUILTIN, Backstop::BUILTIN, 0)
    }

    /// `key=value` pairs in canonical (sorted-key) order: exactly the values
    /// the id hashes.
    #[must_use]
    pub fn canonical_fields(&self) -> Vec<(&'static str, String)> {
        vec![
            ("backstop", self.backstop.per_mille.to_string()),
            ("effort", self.effort.conflicts_per_node.to_string()),
            ("schema", self.schema.to_string()),
        ]
    }

    /// The budget profile id: lowercase SHA-256 hex over the domain and the
    /// canonical fields, each length-prefixed.
    #[must_use]
    pub fn id(&self) -> String {
        use std::fmt::Write as _;
        let mut hasher = Sha256::new();
        hasher.update(BUDGET_PROFILE_DOMAIN);
        let mut buf = String::with_capacity(20);
        for (key, num) in [
            ("backstop", u64::from(self.backstop.per_mille)),
            ("effort", self.effort.conflicts_per_node),
            ("schema", u64::from(self.schema)),
        ] {
            buf.clear();
            let _ = write!(buf, "{num}");
            for part in [key, buf.as_str()] {
                hasher.update((part.len() as u64).to_le_bytes());
                hasher.update(part.as_bytes());
            }
        }
        lowercase_hex(&hasher.finalize())
    }

    /// The report header line: the id and the values it hashes, then the
    /// recorded values it does not, then the pin no profile can move: a
    /// verifying session runs one front-end thread whatever `-Zthreads` says
    /// (plan §3.5, T4.3; `rustc_session::trust_frontend_threads_by_flags`).
    /// The pin is outside the id and outside the record: it is not a bound.
    /// It states what the compiler does, not what this build observed, so it
    /// holds for a matched targo-trust and trustc (both T4.3 or later); report
    /// text only (DECISION_QUEUE FRONTEND-THREADS-1).
    #[must_use]
    pub fn header_line(&self) -> String {
        format!(
            "Budget profile: {} ({}) backstop={} effort={} schema={}; not in the id: \
             vc_clock_ms={} function_clock_ms={} worker_threads={} frontend_threads=1 (pinned)",
            short_id(&self.id()),
            self.name,
            self.backstop.per_mille,
            self.effort.conflicts_per_node,
            self.schema,
            self.backstop.vc_clock_ms(),
            self.backstop.function_clock_ms(),
            self.worker_threads,
        )
    }
}

/// A run's determinism accounting, recorded on its verification gate (plan
/// §3.7): whether the gate's counts are a MEASUREMENT, the budget profile they
/// were measured under, and the verdict vector that identifies them.
///
/// Data, never authority: a saved report's block is a claim like any other
/// saved field, and a consumer that compares two runs compares their
/// `vector_digest`s, which it can recompute from `vector`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GateDeterminism {
    /// `measured`, `not-reproducible` or `could-not-run`.
    pub outcome: UnitOutcome,
    /// [`BudgetProfile::id`] of `budget_profile`.
    pub budget_profile_id: String,
    /// Every bound the run was held to.
    pub budget_profile: BudgetProfile,
    /// [`VerdictVector::digest`] of `vector`.
    pub vector_digest: String,
    /// Obligations by stop cause.
    pub stop_causes: StopCauseTally,
    /// Obligations by named stop ([`StopItem`]); empty when no row named one.
    #[serde(default, skip_serializing_if = "StopItemTally::is_empty")]
    pub stop_items: StopItemTally,
    /// The canonical verdict vector.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub vector: Vec<VerdictEntry>,
    /// Obligation keys refused as vector keys because they carry volatile
    /// identity; any entry here keeps the run from being `measured`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub volatile_keys: Vec<String>,
    /// Functions with a row that carried no stable obligation key (T9); any
    /// entry here makes the run `could-not-run`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unkeyed_functions: Vec<String>,
    /// Backstops (and unexplained stops) the compiler's backstop ledger saw
    /// fire, in the published rows or outside them, the named stops it saw and
    /// the solver count stops it counted (`effort`)
    /// ([`NotedStop`]); any entry whose cause is not deterministic keeps the
    /// run from being `measured`. Not part of the vector: two runs whose
    /// vectors agree still differ in whether a clock decided anything.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub noted_stops: Vec<NotedStop>,
}

/// The first 12 hex digits of an id or digest, as reports print it.
#[must_use]
pub fn short_id(id: &str) -> &str {
    id.get(..12).unwrap_or(id)
}

#[cfg(test)]
#[path = "determinism_tests.rs"]
mod tests;
