// targo-trust/determinism_report.rs: the budget profile a run used, and whether
// its counts are a MEASUREMENT.
//
// Plan: docs/design/2026-09-29-incremental-deterministic-trust-results.md
// §3.6 (the budget profile), §3.7 (report changes) and §2 (verdict vector,
// stop cause, unit outcome). The shared vocabulary lives in
// `trust_types::determinism`; this module applies it to targo's published rows.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::determinism::{
    BudgetProfile, NotedStop, Reproducibility, StopCause, StopCauseTally, StopItem, StopItemTally,
    UnitOutcome, VerdictEntry, VerdictVector, short_id,
};

use crate::config::TrustConfig;
use crate::types::{VerificationOutcome, VerificationResult, structured_transport_evidence};

/// The exit status of a run that produced no measurement (plan §2, §3.1,
/// §4.8): its outcome is `could-not-run` or `not-reproducible` (a refused
/// admission, a row with no stable key, a backstop or another clock, an RSS
/// reading, a solver fault, an unexplained stop), the run's own wall-clock
/// backstop ended its compiler, or the trustd memory authority could not admit
/// it. Distinct from 1, a verdict (a refuted or unproved obligation), and 2, a
/// usage or setup error, so a consumer reads COULD NOT RUN from the status
/// rather than from log text. `diff --baseline` and `check --save-baseline`
/// exit with it on the same condition (`baseline::EXIT_NOT_MEASURED`).
pub(crate) const EXIT_COULD_NOT_RUN: u8 = 3;

/// The budget profile a run uses (plan §3.6): the workspace root's `[trust]`
/// `effort` and `backstop` — the only budget spelling — and the worker-thread
/// count `--worker-threads` passes, which is recorded but is not a bound and is
/// not in the id. Nothing else reaches it: an inherited RUSTFLAGS budget option
/// is ignored with a notice, TRUSTFLAGS is not read (DECISION_QUEUE T7a), and
/// the level and policy are lane, recorded and compared on their own.
pub(crate) fn budget_profile(config: &TrustConfig) -> BudgetProfile {
    BudgetProfile::new(config.effort, config.backstop, config.worker_threads)
}

/// What ended the search for one published row.
///
/// A verdict is `solved`. Otherwise the cause the producer stamped into the
/// reason decides — combined, as every cause is, so that the less reproducible
/// statement wins (`StopCause::combine`): a timeout row is at least
/// `wall-backstop` whatever its reason states. A row that carries no stamp is
/// classified only where the row itself says why (a timeout, a recorded
/// assumption or design mandate, a memory-admission refusal, an unsupported-MIR
/// obligation — whose own detail may carry the stamp of the budget trip that
/// produced it), and is `unclassified` — never counted as deterministic —
/// everywhere else.
pub(crate) fn row_stop_cause(row: &VerificationResult) -> StopCause {
    if matches!(row.outcome, VerificationOutcome::Proved | VerificationOutcome::Failed) {
        return StopCause::Solved;
    }
    // An unsupported-MIR marker's own detail may carry the stamp of the budget
    // trip that produced it (`steps`, or `wall-backstop` when the clock
    // tripped); fold it with whatever the reason states, the detail last.
    let unsupported_detail = structured_transport_evidence(row)
        .and_then(|evidence| evidence.typed_kind)
        .and_then(|kind| match *kind {
            trust_types::VcKind::UnsupportedMir { detail, .. } => Some(detail),
            _ => None,
        });
    let stated = [
        row.reason.as_deref().and_then(StopCause::from_reason),
        unsupported_detail.as_deref().and_then(StopCause::from_reason),
    ]
    .into_iter()
    .flatten()
    .reduce(StopCause::combine);
    if row.outcome == VerificationOutcome::Timeout {
        return stated.map_or(StopCause::WallBackstop, |cause| {
            StopCause::combine(cause, StopCause::WallBackstop)
        });
    }
    if let Some(cause) = stated {
        return cause;
    }
    if row.message.starts_with(trust_types::VcKind::memory_admission_message_prefix().as_str()) {
        return StopCause::AdmissionRefused;
    }
    if crate::pipeline::hardened::counts_as_design_mandate(row)
        || crate::pipeline::hardened::counts_as_conditional_evidence(row)
    {
        return StopCause::NotDispatched;
    }
    if unsupported_detail.is_some() {
        return StopCause::Unsupported;
    }
    StopCause::Unclassified
}

/// The named stop a published row's reason states ([`StopItem`]), if any.
pub(crate) fn row_stop_item(row: &VerificationResult) -> Option<StopItem> {
    if matches!(row.outcome, VerificationOutcome::Proved | VerificationOutcome::Failed) {
        return None;
    }
    row.reason.as_deref().and_then(StopItem::from_reason)
}

pub(crate) fn row_status(row: &VerificationResult) -> trust_types::Outcome {
    match row.outcome {
        VerificationOutcome::Proved => trust_types::Outcome::Proved,
        VerificationOutcome::Failed => trust_types::Outcome::Failed,
        VerificationOutcome::RuntimeChecked => trust_types::Outcome::RuntimeChecked,
        VerificationOutcome::Timeout => trust_types::Outcome::Timeout,
        VerificationOutcome::Unknown => trust_types::Outcome::Unknown,
    }
}

/// One run's determinism accounting over its published rows (plan §3.7).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnitDeterminism {
    /// `measured`, `not-reproducible` or `could-not-run`.
    pub(crate) outcome: UnitOutcome,
    /// Obligations by stop cause.
    pub(crate) tally: StopCauseTally,
    /// Obligations by named stop (the plan critique's P1 ledger items).
    pub(crate) items: StopItemTally,
    /// The canonical verdict vector.
    pub(crate) vector: VerdictVector,
    /// Rows whose stable key carried volatile identity (a package ID, an
    /// absolute path, a crate hash). Such a row keeps the unit from being
    /// `measured`: two checkouts would disagree on its key, not its verdict.
    pub(crate) volatile_keys: Vec<String>,
    /// Functions with a row that carried no stable key (T9), sorted and
    /// distinct. A keyless row is a producer defect — an older compiler, a
    /// refused mint, a row targo synthesized for a transport defect — and it
    /// makes the unit `could-not-run`: its verdicts cannot be compared, so
    /// there is no measurement to publish.
    pub(crate) unkeyed_functions: Vec<String>,
    /// The functions of [`Self::unkeyed_functions`] with a keyless row the
    /// COMPILER published (an older compiler, a refused mint, a lossily parsed
    /// row), sorted and distinct: the ones that "published obligations with no
    /// stable key".
    pub(crate) unkeyed_published_functions: Vec<String>,
    /// The keyless rows that are targo's own, in report order: one entry per
    /// row it synthesized for a transport defect
    /// ([`is_synthesized_transport_defect_row`]), rendered as "`<kind>`:
    /// <reason> (filed under <function>)". Each is also in
    /// [`Self::unkeyed_functions`] and makes the unit could-not-run exactly as
    /// any keyless row does; they are kept apart only so the refusal can state
    /// the defect and its reason. No function published them.
    pub(crate) transport_defects: Vec<String>,
    /// Backstops (and unexplained stops) the compiler's backstop ledger saw
    /// fire anywhere in the run, in a row or not (plan §2), and the named stops
    /// it saw. Any entry whose cause is not deterministic keeps the unit from
    /// being `measured`.
    pub(crate) noted_stops: Vec<NotedStop>,
}

/// Whether `row` is one targo synthesized for a transport defect: the
/// `transport:*` rows `crate::pipeline::transport` builds
/// (`transport_summary_result` to `missing_structured_transport_result`), each
/// with backend `targo-trust`, a `transport:<defect>` kind and no structured
/// evidence. Every row built from a compiler envelope carries structured
/// evidence, so no compiler row passes for one. Such a row states what was
/// wrong with the transport; it is not an obligation of the function, crate or
/// `<transport>` placeholder it is filed under. This decides only how a
/// could-not-run refusal is WORDED: the row is keyless and refuses the unit
/// either way.
fn is_synthesized_transport_defect_row(row: &VerificationResult) -> bool {
    row.backend == "targo-trust"
        && row.kind.starts_with("transport:")
        && structured_transport_evidence(row).is_none()
}

impl UnitDeterminism {
    /// Account for `rows` (the published rows, in report order).
    ///
    /// A row's key is its stable obligation key, `<def_path>#<local id>` (T9,
    /// `trust_types::obligation_identity`), which the compiler minted from the
    /// row's kind and source text and targo bound to the row from the
    /// function's envelope. There is no fallback: the ordinal `obligation_id`
    /// is a binding token and never a comparison key, and a row without a
    /// stable key makes the unit `could-not-run`, naming its function
    /// ([`Self::unkeyed_functions`]).
    ///
    /// `noted_stops` is the compilers' backstop ledger (the coverage transport
    /// of every compiled unit, merged): a clock that ended work the compiler
    /// consumed without publishing a row — the R1 harvest, a refutation
    /// attempt, S1 revalidation — appears there and nowhere else, and it makes
    /// the unit `not-reproducible` (or `could-not-run`) exactly as a row would.
    /// It is not part of the vector.
    ///
    /// `rows` is any selection of a run's rows: the whole run for its
    /// `Summary:` line and gate, one package's share for that package's
    /// records (`crate::package_record::PackageFacts`).
    pub(crate) fn of_rows<'a>(
        rows: impl IntoIterator<Item = &'a VerificationResult>,
        noted_stops: &[NotedStop],
    ) -> Self {
        let mut entries = Vec::new();
        let mut volatile_keys = Vec::new();
        let mut unkeyed_functions = std::collections::BTreeSet::new();
        let mut unkeyed_published_functions = std::collections::BTreeSet::new();
        let mut transport_defects = Vec::new();
        let mut causes = Vec::new();
        let mut items = StopItemTally::default();
        for row in rows {
            let stop = row_stop_cause(row);
            causes.push(stop);
            if let Some(item) = row_stop_item(row) {
                items.record(item);
            }
            let Some(identity) = structured_transport_evidence(row).and_then(|e| e.identity) else {
                unkeyed_functions.insert(row.function.clone());
                if is_synthesized_transport_defect_row(row) {
                    transport_defects.push(format!(
                        "`{}`: {} (filed under {})",
                        row.kind,
                        row.reason.as_deref().unwrap_or(&row.message),
                        row.function
                    ));
                } else {
                    unkeyed_published_functions.insert(row.function.clone());
                }
                continue;
            };
            match VerdictEntry::new(identity.key, row_status(row), stop) {
                Ok(entry) => entries.push(entry),
                Err(volatile) => volatile_keys.push(volatile.to_string()),
            }
        }
        let vector = VerdictVector::new(entries);
        let mut outcome = UnitOutcome::from_causes(
            causes.iter().copied().chain(noted_stops.iter().map(|stop| stop.cause)),
        );
        if outcome == UnitOutcome::Measured && !volatile_keys.is_empty() {
            outcome = UnitOutcome::NotReproducible;
        }
        if !unkeyed_functions.is_empty() {
            outcome = UnitOutcome::CouldNotRun;
        }
        let tally = causes.into_iter().collect();
        Self {
            outcome,
            tally,
            items,
            vector,
            volatile_keys,
            unkeyed_functions: unkeyed_functions.into_iter().collect(),
            unkeyed_published_functions: unkeyed_published_functions.into_iter().collect(),
            transport_defects,
            noted_stops: noted_stops.to_vec(),
        }
    }

    /// The `COULD NOT RUN:` line printed instead of a `Summary:` line: what
    /// kept this run from being a measurement. `None` unless the outcome is
    /// could-not-run.
    pub(crate) fn could_not_run_line(&self) -> Option<String> {
        if self.outcome != UnitOutcome::CouldNotRun {
            return None;
        }
        let mut causes = Vec::new();
        let refused = self.admission_refusals();
        let noted = self.noted_admission_refusals();
        if refused > 0 || noted > 0 {
            causes.push(format!(
                "{refused} obligation(s) were refused solver admission (trustd / the memory \
                 jobserver; {noted} refused solver attempt(s) in all, counting work that \
                 published no row)"
            ));
        }
        const SHOWN: usize = 5;
        if !self.transport_defects.is_empty() {
            // Targo's own rows: say what was wrong with the transport. Saying
            // that a function "published obligations with no stable key" sent
            // the reader after an obligation that does not exist (2026-10-12:
            // an accounting mismatch read as two unkeyed functions, its row
            // counts hundreds of lines further down the log).
            let mut named: Vec<&str> =
                self.transport_defects.iter().take(SHOWN).map(String::as_str).collect();
            if self.transport_defects.len() > SHOWN {
                named.push("…");
            }
            causes.push(format!(
                "targo-trust found {} transport defect(s) and reports each as a row of its own, \
                 which has no stable key, so the unit's verdicts cannot be compared: {}",
                self.transport_defects.len(),
                named.join("; ")
            ));
        }
        if !self.unkeyed_published_functions.is_empty() {
            let mut named: Vec<&str> =
                self.unkeyed_published_functions.iter().take(SHOWN).map(String::as_str).collect();
            if self.unkeyed_published_functions.len() > SHOWN {
                named.push("…");
            }
            causes.push(format!(
                "{} function(s) published obligations with no stable key, so no verdict of \
                 theirs can be compared: {}",
                self.unkeyed_published_functions.len(),
                named.join(", ")
            ));
        }
        Some(format!(
            "COULD NOT RUN: verification did not run to a measurement: {}, so this run has no \
             counts",
            causes.join("; ")
        ))
    }

    /// Obligations whose solver was refused admission.
    pub(crate) fn admission_refusals(&self) -> u64 {
        self.tally.count(StopCause::AdmissionRefused)
    }

    /// Solver attempts the backstop ledger saw refused admission. A lane notes
    /// every refusal it returns, so this counts refused ATTEMPTS — including
    /// the ones already behind an `admission-refused` row, and ones in work
    /// that published no row — never obligations.
    pub(crate) fn noted_admission_refusals(&self) -> u64 {
        self.noted_stops
            .iter()
            .filter(|stop| stop.cause == StopCause::AdmissionRefused)
            .map(|stop| stop.count)
            .sum()
    }

    /// The text appended to the `Summary:` line.
    pub(crate) fn summary_suffix(&self, profile: &BudgetProfile) -> String {
        format!(
            "; {}; profile {}; vector {}",
            self.outcome,
            short_id(&profile.id()),
            short_id(&self.vector.digest())
        )
    }

    /// The line stating the stop-cause tally, and why a non-measured unit is not
    /// a floor measurement.
    pub(crate) fn stop_cause_line(&self) -> String {
        let mut line = format!("Stop causes: {}", self.tally.render());
        if !self.items.is_empty() {
            line.push_str(&format!("; named: {}", self.items.render()));
        }
        if !self.volatile_keys.is_empty() {
            line.push_str(&format!(
                "; {} obligation key(s) carry volatile identity",
                self.volatile_keys.len()
            ));
        }
        // The ledger's deterministic entries are the named stops and the one
        // solver count (`effort`), counted wherever the
        // stopped work went (plan P2): never a backstop, never a reason the
        // unit is not measured.
        let (fired, named): (Vec<&NotedStop>, Vec<&NotedStop>) = self
            .noted_stops
            .iter()
            .partition(|stop| stop.cause.reproducibility() != Reproducibility::Deterministic);
        if !fired.is_empty() {
            let fired: Vec<String> = fired.iter().map(ToString::to_string).collect();
            line.push_str(&format!("; backstops fired: {}", fired.join(", ")));
        }
        if !named.is_empty() {
            let named: Vec<String> = named.iter().map(ToString::to_string).collect();
            line.push_str(&format!(
                "; counted and named stops the lanes saw: {}",
                named.join(", ")
            ));
        }
        match self.outcome {
            UnitOutcome::Measured => {}
            UnitOutcome::NotReproducible => line.push_str(
                " — NOT REPRODUCIBLE: a clock, an RSS reading, a solver fault or an unexplained \
                 stop ended at least one obligation, or work the verdicts depend on, so these \
                 counts are not a floor measurement",
            ),
            UnitOutcome::CouldNotRun => line.push_str(
                " — COULD NOT RUN: resource admission refused the solver, or a row carried no \
                 stable key, so this run is not a measurement",
            ),
        }
        line
    }

    /// The JSON block recorded on the verification gate.
    pub(crate) fn gate_block(
        &self,
        profile: &BudgetProfile,
    ) -> trust_types::determinism::GateDeterminism {
        trust_types::determinism::GateDeterminism {
            outcome: self.outcome,
            budget_profile_id: profile.id(),
            budget_profile: profile.clone(),
            vector_digest: self.vector.digest(),
            stop_causes: self.tally.clone(),
            stop_items: self.items.clone(),
            vector: self.vector.entries().to_vec(),
            volatile_keys: self.volatile_keys.clone(),
            unkeyed_functions: self.unkeyed_functions.clone(),
            noted_stops: self.noted_stops.clone(),
        }
    }
}

/// The backstop ledgers of every compiled unit's coverage transport, merged
/// into one canonical list (a `(lane, cause, item)` entry seen by several units
/// sums).
pub(crate) fn merged_noted_stops<'a>(
    coverage_rows: impl IntoIterator<Item = &'a trust_types::CoverageTransportSummary>,
) -> Vec<NotedStop> {
    merged_stops(coverage_rows.into_iter().flat_map(|row| row.noted_stops.iter()))
}

/// Merge compiler notes and typed publication-elision notes once at the
/// producer boundary. Elided rows stay outside the verdict vector/counts.
pub(crate) fn noted_stops_with_publication(
    compiler: &[NotedStop],
    publication: &[crate::types::PublicationStop],
    package: Option<&str>,
) -> Vec<NotedStop> {
    merged_stops(
        compiler.iter().chain(
            publication
                .iter()
                .filter(|note| {
                    package.is_none()
                        || note.package.is_none()
                        || note.package.as_deref() == package
                })
                .map(|note| &note.stop),
        ),
    )
}

fn merged_stops<'a>(stops: impl IntoIterator<Item = &'a NotedStop>) -> Vec<NotedStop> {
    let mut merged: BTreeMap<(String, StopCause, Option<StopItem>), u64> = BTreeMap::new();
    for stop in stops {
        *merged.entry((stop.lane.clone(), stop.cause, stop.item)).or_insert(0) += stop.count;
    }
    merged
        .into_iter()
        .map(|((lane, cause, item), count)| NotedStop { lane, cause, item, count })
        .collect()
}

/// A report fixture's profile: the built-in one.
#[cfg(test)]
pub(crate) fn test_budget_profile() -> BudgetProfile {
    BudgetProfile::builtin()
}

#[cfg(test)]
#[path = "determinism_report_tests.rs"]
mod tests;
