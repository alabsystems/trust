// targo-trust/package_record.rs: one JSON record per package,
// `trust.package.v1` (work item T7c; plan
// docs/design/2026-09-29-incremental-deterministic-trust-results.md §3.7,
// "Machine-readable records").
//
// Every crate-mode `targo trust check` writes
// `<target-dir>/trust/packages/<package>.json` beside the obligation record
// `<target-dir>/trust/obligations/<package>.ndjson` (`crate::obligations`),
// one of each for every package the run selected or verified or that reported
// a compile error. An unselected dependency's record is not removed when its
// errors are gone: it stays until a run selects, verifies or breaks it again.
// A consumer reads
// a package's outcome, stop causes, coverage and counts here instead of from
// the human `Summary:` line.
//
// ONE SOURCE. A package's facts are computed once ([`PackageFacts`]), by the
// functions the run's own `Summary:` line, `Stop causes:` line and gate use —
// `UnitDeterminism::of_rows` (outcome, stop-cause tally, backstop ledger,
// verdict vector), `aggregate_coverage` and `partition_outcome_counts` — over
// the package's share of the run's rows and coverage rows. The obligation
// record's header and this record are both rendered from that one value, so
// they cannot disagree, and in a one-package run that value is the run's.
//
// ATTRIBUTION. A row belongs to the package its stable key names; a coverage
// row (one per compiled unit) to the package it names. A row with no stable
// key names no package, so it is in no package's counts, stop causes or cost:
// its function is named in every package's `unkeyed_functions` count, and it
// makes each of them `could-not-run`, as the run is — so a keyless refutation
// is never a package's `failed`, and the packages' counts never sum to more
// than the run's. A package with a unit that concluded without a coverage row
// has incomplete coverage, and a package none of whose units published one
// (it never compiled, or no unit of it concluded) was not measured: it is
// `could-not-run`, its coverage `null`.
//
// FORMAT. One JSON object, keys sorted at every level, no insignificant
// whitespace, one LF at the end:
//
//   {"conflicting_def_paths":0,"cost":{"wall_clock_ms":…},"counts":{…},
//    "coverage":{"complete":true,"eligible":…,"processed":…},
//    "degraded_anchors":0,"lane":"strict","memory_need":{"absent":"T3",…},
//    "noted_stops":[…],"outcome":"measured","package":"demo","policy":"strict",
//    "profile":"<64 hex>","provenance":{"absent":"T10",…},
//    "result_key":{"absent":"T10",…},"schema":"trust.package.v1",
//    "seal":{"absent":"A8",…},"selection":"--lib",
//    "stop_causes":{"solved":…},"targo_trust_commit":"<40 hex>|unbound",
//    "unkeyed_functions":0,"vector":"<64 hex>","volatile_keys":0,
//    "worker_threads":0}
//
// `worker_threads` is the verifier worker-thread cap the run passed
// (`--worker-threads`; 0 is no cap). The budget profile records it outside
// its id, so it is stated beside `profile`: `targo trust stability`'s
// parallelism axis reads it to know its serial leg ran with one thread.
//
// DETERMINISM. Every field but `cost` is a function of the run's inputs: no
// timestamp, no Cargo package ID (which embeds the checkout's path), no
// function label (which embeds the package ID) — keys, counts and digests
// only. The one field that holds text the caller wrote is `selection`: a
// `--target` spec file or a `--config` value is kept as written, so an
// absolute path written there is in the record (and in the baseline header);
// nothing else names a path. `cost` is wall-clock time: it varies from run to
// run, and it is in no digest and no comparison.
//
// ABSENT. A field the toolchain cannot fill yet is present as
// `{"absent":"<item>","until":"<what fills it>"}`, never invented and never a
// stand-in: the seal's identity (T13a's `artifact_content_sha256`, which an
// installed pack cannot read until the consumer's adoption, A8), the memory
// need trustd admitted the package with (T3's admission, §3.4), and the result
// key and provenance (T10's store, §4). The commit targo-trust was built from
// is stated under its own name, `targo_trust_commit`, not as the seal.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};

use trust_types::determinism::UnitOutcome;
use trust_types::{CoverageTransportSummary, VerificationCoverage};

use crate::determinism_report::{UnitDeterminism, merged_noted_stops};
use crate::obligations::RunFacts;
use crate::pipeline::hardened::{OutcomeCounts, aggregate_coverage, partition_outcome_counts};
use crate::types::VerificationResult;

/// The schema name every package record carries.
pub(crate) const PACKAGE_RECORD_SCHEMA: &str = "trust.package.v1";

/// The seal's identity: T13a defines it as `artifact_content_sha256` in the
/// seal's PROVENANCE, and an installed atpkg pack carries no PROVENANCE, so it
/// can neither read nor recompute it; the consumer's adoption (A8) ships the
/// PROVENANCE in the pack or names a second scope over what a pack carries.
/// The targo-trust commit is no stand-in: two seals cut from one commit share
/// it.
pub(crate) const SEAL_ABSENT: (&str, &str) = (
    "A8",
    "the seal's identity is `artifact_content_sha256` in its PROVENANCE (T13a), which an \
     installed pack does not carry; the consumer's adoption (A8) ships it in the pack or names \
     a scope over what a pack carries",
);

/// A field the toolchain cannot fill yet: `{"absent": <item>, "until": <what
/// fills it>}`.
pub(crate) fn absent((item, until): (&str, &str)) -> serde_json::Value {
    serde_json::json!({ "absent": item, "until": until })
}

/// The memory need trustd admitted the package with, and its source: T3's
/// admission before start (plan §3.4, T3 landing L8) reports it.
const MEMORY_NEED_ABSENT: (&str, &str) = (
    "T3",
    "trustd's admission before start (plan §3.4) reports the memory need it admitted a unit \
     with and its source (recorded or model); trustd admits no unit yet",
);

/// The result key: T10's result store (plan §4.2) keys each unit's result.
const RESULT_KEY_ABSENT: (&str, &str) =
    ("T10", "the result store (plan §4.2) keys each unit's result; there is no store yet");

/// Whether the result was fresh or reused: T10's result store (plan §4.5).
const PROVENANCE_ABSENT: (&str, &str) = (
    "T10",
    "the result store (plan §4.5) says whether a result is fresh or reused; there is no store \
     yet, and nothing is reused",
);

/// The coverage evidence of a run beyond its rows.
#[derive(Debug, Clone, Default)]
pub(crate) struct RunCoverage<'a> {
    /// The coverage transport of every compiled unit (one row per unit).
    pub(crate) rows: &'a [CoverageTransportSummary],
    /// Producer-retained stops of elided rows, attributed by transported identity.
    pub(crate) publication_stops: &'a [crate::types::PublicationStop],
    /// Packages with a unit that concluded without publishing a coverage row:
    /// their coverage is not complete, whatever their other units say.
    pub(crate) missing: BTreeSet<String>,
    /// The error-level compiler diagnostics Cargo reported (compile errors,
    /// and the verifier's own refusals), each in the package its envelope
    /// names. A package with one is recorded, with its error lines
    /// (`crate::obligations`), whether or not the run selected it; whether
    /// it concluded is read from its coverage rows alone.
    pub(crate) compile_errors: &'a [crate::obligations::CompileError],
}

/// The package a coverage row names: its Cargo package, or, outside Cargo, its
/// crate — the same fallback a row's stable identity takes
/// (`crate::types::envelope_identities`).
pub(crate) fn coverage_package(row: &CoverageTransportSummary) -> &str {
    if row.package_name.trim().is_empty() { &row.crate_name } else { &row.package_name }
}

/// What one package of a run established. Computed once per package by
/// [`PackageFacts::of_package`]; both its obligation record header and its
/// package record are rendered from it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PackageFacts {
    /// Outcome, stop-cause tally, backstop ledger and verdict vector of the
    /// package's own rows; its `unkeyed_functions`,
    /// `unkeyed_published_functions` and `transport_defects` are the run's (a
    /// keyless row names no package), and they make the outcome
    /// `could-not-run`.
    pub(crate) determinism: UnitDeterminism,
    /// The package's coverage, summed over its units' coverage rows; `None`
    /// when no unit of it published one.
    pub(crate) coverage: Option<VerificationCoverage>,
    /// Obligation keys its units minted on a degraded anchor.
    pub(crate) degraded_anchors: usize,
    /// The outcome partition of its rows, as the `Summary:` line counts them.
    pub(crate) counts: OutcomeCounts,
    /// Def paths of the package published with two different source digests
    /// (`ObligationRecords::conflicting_functions`).
    pub(crate) conflicting_def_paths: usize,
    /// Wall-clock milliseconds the compiler reported for the package's rows.
    /// Not a function of the inputs: in no digest and no comparison.
    pub(crate) wall_clock_ms: u64,
}

impl PackageFacts {
    /// The facts of one package from its own `rows` (those whose stable key
    /// names it), the run's rows that carry no stable key, accounted for on
    /// their own (`keyless`: `UnitDeterminism::of_rows` over those rows alone;
    /// no package can be attributed one), and its units' `coverage` rows.
    pub(crate) fn of_package<'a>(
        rows: impl IntoIterator<Item = &'a VerificationResult> + Clone,
        keyless: &UnitDeterminism,
        coverage: &[&CoverageTransportSummary],
        coverage_missing: bool,
        publication_stops: &[crate::types::PublicationStop],
        package: &str,
        conflicting_def_paths: usize,
    ) -> Self {
        let noted_stops = crate::determinism_report::noted_stops_with_publication(
            &merged_noted_stops(coverage.iter().copied()),
            publication_stops,
            Some(package),
        );
        let mut determinism = UnitDeterminism::of_rows(rows.clone(), &noted_stops);
        let (counts, _defects) = partition_outcome_counts(rows.clone());
        let wall_clock_ms = rows
            .into_iter()
            .filter_map(|row| row.time_ms)
            .fold(0u64, |total, ms| total.saturating_add(ms));
        let mut coverage_summary = aggregate_coverage(coverage.iter().copied());
        if coverage_missing {
            if let Some(summary) = coverage_summary.as_mut() {
                summary.coverage_complete = false;
            }
        }
        let degraded_anchors =
            coverage.iter().map(|row| row.degraded_anchors).fold(0usize, usize::saturating_add);
        // A keyless row names no package and so is in none of the counts
        // above; it leaves every package of the run unmeasured, as it leaves
        // the run (`UnitDeterminism::of_rows`), and the package states it as
        // the run does: which functions, which the compiler published, which
        // transport defects.
        if !keyless.unkeyed_functions.is_empty() {
            determinism.unkeyed_functions.clone_from(&keyless.unkeyed_functions);
            determinism
                .unkeyed_published_functions
                .clone_from(&keyless.unkeyed_published_functions);
            determinism.transport_defects.clone_from(&keyless.transport_defects);
            determinism.outcome = UnitOutcome::CouldNotRun;
        }
        // Every verified unit publishes its coverage row; a package with none
        // was never measured (its unit did not compile, or did not conclude),
        // whatever its empty rows would otherwise say.
        if coverage_summary.is_none() {
            determinism.outcome = UnitOutcome::CouldNotRun;
        }
        Self {
            determinism,
            coverage: coverage_summary,
            degraded_anchors,
            counts,
            conflicting_def_paths,
            wall_clock_ms,
        }
    }

    /// Whether every eligible function of the package was verified.
    pub(crate) fn coverage_complete(&self) -> bool {
        self.coverage.as_ref().is_some_and(|coverage| coverage.coverage_complete)
    }

    /// The package's verdict-vector digest.
    pub(crate) fn vector_digest(&self) -> String {
        self.determinism.vector.digest()
    }

    /// The `trust.package.v1` record of `package` in a run described by `run`:
    /// canonical JSON (keys sorted), one LF at the end.
    pub(crate) fn record_json(&self, package: &str, run: &RunFacts) -> String {
        let counts = &self.counts;
        let value = serde_json::json!({
            "schema": PACKAGE_RECORD_SCHEMA,
            "package": package,
            "lane": run.lane,
            "policy": run.policy,
            "selection": run.selection,
            "seal": absent(SEAL_ABSENT),
            "targo_trust_commit": run.targo_trust_commit,
            "profile": run.profile,
            "worker_threads": run.worker_threads,
            "outcome": self.determinism.outcome.as_str(),
            "vector": self.vector_digest(),
            "stop_causes": self.determinism.tally,
            "noted_stops": self.determinism.noted_stops,
            "coverage": self.coverage.as_ref().map(|coverage| serde_json::json!({
                "eligible": coverage.eligible,
                "processed": coverage.processed,
                "complete": coverage.coverage_complete,
            })),
            "counts": {
                "total": counts.total,
                "proved": counts.proved,
                "failed": counts.failed,
                "unknown": counts.unknown,
                "runtime_checked": counts.runtime_checked,
                "assumed": counts.assumed,
                "mandated": counts.mandated,
                "contract_panics": counts.contract_panics,
            },
            "degraded_anchors": self.degraded_anchors,
            "unkeyed_functions": self.determinism.unkeyed_functions.len(),
            "volatile_keys": self.determinism.volatile_keys.len(),
            "conflicting_def_paths": self.conflicting_def_paths,
            "memory_need": absent(MEMORY_NEED_ABSENT),
            "result_key": absent(RESULT_KEY_ABSENT),
            "provenance": absent(PROVENANCE_ABSENT),
            "cost": { "wall_clock_ms": self.wall_clock_ms },
        });
        let mut bytes =
            trust_types::digest::canonical_json_bytes(&value).expect("a JSON value serializes");
        bytes.push(b'\n');
        String::from_utf8(bytes).expect("serde_json writes UTF-8")
    }
}

/// The package records directory of a Cargo target directory.
pub(crate) fn package_records_dir(target_dir: &Path) -> PathBuf {
    target_dir.join("trust").join("packages")
}

/// The record file of `package` under `dir`.
pub(crate) fn package_record_path(dir: &Path, package: &str) -> PathBuf {
    dir.join(format!("{}.json", crate::obligations::record_file_stem(package)))
}

/// Remove the records a run of `packages` is about to replace — the package
/// record and the obligation record of each — so that a run that stops after
/// its package selection is known and before it writes them (a trustd that
/// could not be established, a compile that never published) never leaves an
/// earlier run's records looking like its own. An exit before the selection
/// is known is exit 2 and removes nothing; a consumer gates on the exit status.
/// Records of packages the run did not select are left as they are.
pub(crate) fn remove_records(
    target_dir: &Path,
    packages: &BTreeSet<String>,
) -> io::Result<Vec<PathBuf>> {
    let obligations = crate::obligations::records_dir(target_dir);
    let package_records = package_records_dir(target_dir);
    let mut removed = Vec::new();
    for package in packages {
        for path in [
            crate::obligations::obligation_record_path(&obligations, package),
            package_record_path(&package_records, package),
        ] {
            match std::fs::remove_file(&path) {
                Ok(()) => removed.push(path),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
    }
    Ok(removed)
}

/// The facts of every package of a run, by name.
pub(crate) type PackageFactsByName = BTreeMap<String, PackageFacts>;

#[cfg(test)]
#[path = "package_record_tests.rs"]
mod tests;
