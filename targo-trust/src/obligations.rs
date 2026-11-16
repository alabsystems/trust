// targo-trust/obligations.rs: the compact per-obligation record,
// `trust.obligations.v1` (work item T9).
//
// One line per obligation: its stable key (`trust_types::obligation_identity`),
// kind, published status, stop cause and location — about two hundred bytes,
// where report.ndjson spends tens of kilobytes on the same obligation. Every
// crate-mode `targo trust check` writes one file per package to
// `<target-dir>/trust/obligations/<package>.ndjson`, and the committed baseline
// (`crate::baseline`) is a projection of the same records, so the record, the
// baseline and `targo trust diff` read one representation.
//
// FORMAT. NDJSON, LF line endings, bytewise-sorted:
//
//   {"schema":"trust.obligations.v1","package":…,"lane":…,"policy":…,
//    "selection":…,"seal":{"absent":"A8",…},"targo_trust_commit":…,
//    "profile":…,"outcome":…,"vector":…,"concluded":true|false,…}
//   {"fn":"<def path>","source":"<function source digest>"|null}
//   {"key":"<def path>#<id>","kind":…,"status":…,"stop":…,"file":…,"line":…,"col":…,
//    "encoding":…,"discharge":…,"premises":[…]}
//   {"key":…,…,"status":"failed",…,"premises":[…],"basis":"refuted"|"unproved_fail_closed"}
//   …
//
// CONCLUDED. The header's `concluded` states whether the record's rows are a
// measurement of the package's obligations: for a crate, whether a unit of
// the package published its coverage row (the compiler's verification walk
// ran to its end, whatever errors it reported on the way); for a `.lean`
// check, always, as its file row states the file's verdict whatever it is. A
// record that did not conclude (a package that did not compile, one whose
// unit never reached its coverage row, a package whose dependency did not
// compile) measured no obligation set, so the changed-only view
// (`crate::agent_delta`) never compares its obligations with another's. It
// is decided by what the unit published, never by whether an error was
// reported: the verifier reports its own refusals as compiler errors, and a
// package with one is measured.
//
// COMPILER ERRORS. A package with an error-level compiler diagnostic has one
// line per error (Cargo's `compiler-message` of level `error`: a compile
// error, or the verifier's own refusal), right after the header and in key
// order, before any function line:
//
//   {"compile_error":"<file>#<code>-<digest>","code":"E0308"|null,
//    "message":"mismatched types","file":…,"line":…,"col":…}
//
// Its key is the error's file, its code (`error` when it has none) and the
// first twelve hex digits of the SHA-256 of its normalized message
// ([`compile_error_key`]: whitespace runs are one space, and the source
// position rustc writes into a closure's or coroutine's type,
// `{closure@src/lib.rs:5:13: 5:15}`, is cut to its file); a second error with
// the same three in one file adds `~2`, a third `~3`, in source order. No
// line number is in the key, so an edit elsewhere in the file leaves the key
// as it was while the line's `line` and `col` move. The ordinals follow
// source order, so when the first of two such errors is fixed the survivor
// takes the unnumbered key: the view then says `CLEARED` for the `~2` key at
// the old second location and `STILL` for the survivor. Nothing is hidden
// (both locations print), but the cleared row names the survivor's former
// location. A Cargo diagnostic names no enclosing item, and a package that
// did not compile published no obligation identity to take one from, so the
// key names none. Rustc's closing `aborting due to N previous error(s)`
// counts the others and is not a line; a warning is not one either. An error
// line is disclosure: it is in the record's bytes, so in its snapshot token
// (`crate::agent_delta`), and in no verdict, count, baseline or vector — a
// package that did not compile is `could-not-run` by its missing coverage, as
// before.
//
// TEST RESULTS. The record of a `targo trust test` run that executed (or was
// refused before executing) its harnesses names in its header's `"tests"` the
// libtest arguments its harnesses were given (without the result channel):
// `"tests":["--exact","edits::one_row"]`, `"tests":[]` with none. Those
// arguments choose which cases run, so a test run is compared only with a
// test run given the same ones (`crate::agent_delta`). The record carries, after the compile-error lines and before any function line,
// one line per harness of the package and then one line per case, each in key
// order (`crate::test_results`):
//
//   {"test_harness":"test/agent_delta","concluded":false,"reason":"ended by signal 6"}
//   {"test":"test/agent_delta::edits::one_row","outcome":"failed"}
//
// A harness key is the test target's kinds and name; a case key is its
// harness key, `::` and libtest's name for the case. The outcome is `passed`,
// `failed`, `ignored` or `not concluded`, as the test binary's own harness
// reported it: disclosure, never proof, in no verdict, count, baseline or
// vector. A record without `"tests"` (every `check`) has no such line.
//
// CLEAN ISLANDS. A package whose compilation units published island rows
// (`trust_types::clean_island_rows`: one message per unit the compiler
// reaches its islands in, `islands: 0` when it has none, one row per
// declaration of the crate's `clean { … }` islands, PKG-LIVE-2) carries,
// after the test lines and before any function line, one line counting the
// units that published of the package's proof units in the run's declared
// inventory (`null` when it declared none), then per crate in name order one
// section line and then one line per island declaration in key order:
//
//   {"clean_island_units":P,"proof_units":N|null}
//   {"clean_islands":"<crate>","phase":"verified"|"front-end-error","islands":N,
//    "complete":true|false,"problems":[…]}
//   {"clean_decl":"<crate>::<Clean name>#<16 hex>","kind":"lean:theorem",
//    "status":…,"stop":…,"file":…,"line":…,"col":…,"source":"<64 hex>"|null
//    [,"basis":"unproved_fail_closed"]}
//
// A declaration's key is the one a standalone `.lean` file's declaration gets
// (`trust_types::lean_declaration_identity`) with the crate in front, so no
// island key can be a Rust obligation's. The units of one package that share a
// crate name (a library and its own test unit; a library and a binary of the
// package's name) are one section: a key keeps its worse row, `complete` is
// every unit's, the phase is `front-end-error` when any unit's is, the
// problems are every unit's, and `islands` is the most any unit had; a
// verified, complete unit with no island adds no section, only its count. A
// unit that published nothing (a Rust parse or macro error stopped it before
// its islands were read) is in no section, so a key missing from the record
// is one no unit has only when every proof unit published (`P` = `N`): the
// package's units are WHOLE. Otherwise no row of the package is proved (the
// writer states each `not-dispatched`, as a merge with a unit that is not a
// measurement does) and the view reads a missing key as not measured. A row
// states one of four verdicts only — `proved`/`solved`, `failed`/
// `solver-incomplete` with basis `unproved_fail_closed`, `unknown`/
// `unsupported`, `unknown`/`not-dispatched` — and `proved` only in a section
// that is `verified` and complete; the reader refuses any other line, a row
// before its crate's section line, a section whose `complete` disagrees
// with its problems, an island line before the units line, and a `proved`
// row in a package whose units are not whole. What `proved` means for an
// island row is the producer's (`trust_certify::clean_island_rows`;
// docs/TCB.md): never `Certified`. The
// rows are ungraded, so the listing's label is the `.lean` lane's (`PROVED`,
// `FAILED: unproved, no counterexample; failed closed`, `UNKNOWN`).
//
// An island line is disclosure, like a compile-error or test line: it is in
// the record's bytes, so in its snapshot token (`crate::agent_delta`), and in
// no verdict, count, `Summary:` line, baseline, vector or `coverage_complete`.
//
// After the header, each function's `fn` line is followed by its obligations,
// functions in def-path order and obligations in key order. Every function the
// compiler verified has its `fn` line — one whose obligations were all elided
// from publication (the zero-obligation inventory row, a test-harness
// exclusion) included, with no obligation lines after it — so a function that
// lost every obligation is told apart from a function that is gone.
//
// Every obligation line carries its grade on the three R7 axes (VF1):
// `encoding`, `discharge` and `premises`, as the compiler stated them for the
// proof authority behind the row (`trust_types::authority_grade`), or
// `ungraded`, `ungraded` and `[]` for a row no authority graded (an unproved
// row, or one from a compiler that states no grade). A grade never claims more
// than the line's status: a `proved` line may carry any grade a compiler
// states, an `unknown` line (a compiler `skipped` assumption row) only an
// `assumed` one, and every other line none; a row demoted after the compiler
// graded it is written `ungraded`. A line without the three fields, with a
// value outside that vocabulary, with a grade no compiler states (calculus
// credit other than VF5's, an incoherent encoding/discharge pair, unordered or
// repeated premises) or with a grade its status does not admit, is not a
// `trust.obligations.v1` line, and the reader refuses it. The grade is
// disclosure: no verdict, baseline comparison or diff reads it.
//
// A `failed` line also carries its `basis` (`trust_types::FailureBasis`):
// `refuted` when something refuted the obligation, `unproved_fail_closed` when
// nothing did and a fail-closed policy forced it to `failed` (the terminal
// listing's `FAILED: unproved, no counterexample; failed closed`). Every
// `failed` line has one and no other line does; the reader refuses anything
// else. Like the grade it is disclosure, and it is what lets a reader of the
// record (`crate::agent_delta`) print the listing's own label for the row.
//
// The header's lane, policy, selection, targo-trust commit and profile are the
// run's, and its `seal` is absent until A8 (`crate::package_record`); its
// outcome, vector, coverage and degraded anchors are the PACKAGE's
// (`crate::package_record::PackageFacts`, T7c), computed once per package and
// rendered into both this header and the package's `trust.package.v1` record,
// so the two cannot disagree. In a one-package run they are the run's.
//
// The records are a function of the run's rows alone, never of the order the
// compiler units finished in: a key two units published keeps the worst of its
// rows by a total order, and a def path two units published with different
// source digests (a library and a binary of one package defining the same
// path) is named, and keeps the run from being a measurement.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use trust_types::determinism::UnitOutcome;

use crate::determinism_report::UnitDeterminism;
use crate::package_record::{
    PackageFacts, PackageFactsByName, RunCoverage, coverage_package, package_record_path,
    package_records_dir,
};
use crate::types::{VerificationResult, structured_transport_evidence};

/// The schema name on every record header.
pub(crate) const OBLIGATIONS_SCHEMA: &str = "trust.obligations.v1";

/// What a run was, as the baseline header states it. A package's record
/// header takes the lane, policy, selection, targo-trust commit and profile
/// from here, and
/// its outcome, vector, coverage and degraded anchors from the package's own
/// [`PackageFacts`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RunFacts {
    /// The gate lane: `strict`, `advisory`, `memory-safe` or `certify`.
    pub(crate) lane: String,
    /// The compiler policy the lane flags selected (`TrustPolicySelection`):
    /// `strict`, `advisory`, `memory-safe` or `certify`. It is separate from
    /// the gate lane because `--allow-l0-gaps` (gate `advisory`, policy
    /// `strict`) and `--survey` (gate `advisory`, policy `advisory`) compile
    /// differently and can publish different rows.
    pub(crate) policy: String,
    /// The canonical target, feature, profile and option selection
    /// ([`canonical_selection`]).
    pub(crate) selection: String,
    /// The Trust commit this targo-trust was built from, or `unbound` in a
    /// build that embedded none ([`targo_trust_commit`]). It names the driver,
    /// never the toolchain: two seals cut from one commit share it, and a
    /// targo-trust and a trustc of different builds are not told apart by it.
    /// The seal's identity is a record's `seal`, absent until A8
    /// (`crate::package_record::SEAL_ABSENT`).
    pub(crate) targo_trust_commit: String,
    /// The budget profile id.
    pub(crate) profile: String,
    /// The verifier worker-thread cap the run passed (`--worker-threads`; 0,
    /// the default, is no cap): recorded in the budget profile and not in its
    /// id, so stated beside it. The package record carries it (the stability
    /// verb's parallelism axis reads it from there); the obligation header and
    /// the baseline header do not, since it is a scheduling choice and no
    /// verdict of a measured run depends on it.
    pub(crate) worker_threads: u64,
    /// The run's determinism outcome.
    pub(crate) outcome: UnitOutcome,
    /// The run's verdict-vector digest.
    pub(crate) vector: String,
    /// Whether the compiler's coverage accounting was complete: every
    /// eligible function was verified, and every unit that concluded published
    /// its coverage.
    pub(crate) coverage_complete: bool,
    /// How many obligation keys the compilers minted on a DEGRADED anchor
    /// (`CoverageTransportSummary::degraded_anchors`): still keys, but coarser
    /// than a content address. Stated wherever the records are, never silent.
    pub(crate) degraded_anchors: usize,
}

/// The Trust commit this binary was built from (`unbound` when the build
/// embedded none). It is not the seal's identity: T13a's identity is
/// `artifact_content_sha256` in the seal's PROVENANCE, which an installed pack
/// cannot read yet, so the records carry `seal` as absent (A8) and this commit
/// under its own name.
pub(crate) fn targo_trust_commit() -> String {
    crate::embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH")).to_string()
}

/// The selection of a Cargo argument list that decides what is compiled and
/// how, canonically: the target and feature selection flags, the Cargo profile
/// (`--release`/`-r` is `--profile=release`), every `--config` value and every
/// `-Z` option, `=`-joined; sorted and space-separated, except that `--config`
/// values keep their order (a later one overrides an earlier one); `default`
/// when there are none. Each of these changes `debug_assertions`, overflow
/// checks or the unit graph, and with them the obligations, so a baseline
/// measured under one is never compared with a run under another.
///
/// Packages are not part of it — a record and a baseline name their packages
/// themselves — and neither is `--workspace`, which only chooses packages.
/// Everything after `--` belongs to the program Cargo runs and is ignored.
/// Values are kept as the caller wrote them: a `--target` spec file or a
/// `--config` path is in the selection verbatim, absolute or not.
pub(crate) fn canonical_selection(args: &[String]) -> String {
    const BARE: &[&str] = &[
        "--lib",
        "--bins",
        "--tests",
        "--examples",
        "--benches",
        "--all-targets",
        "--all-features",
        "--no-default-features",
    ];
    const VALUED: &[&str] =
        &["--bin", "--test", "--example", "--bench", "--features", "--target", "--profile"];
    let mut tokens = Vec::new();
    let mut configs = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        let next = args.get(index + 1);
        if arg == "--" {
            break;
        }
        if BARE.contains(&arg) {
            tokens.push(arg.to_string());
        } else if matches!(arg, "--release" | "-r") {
            tokens.push("--profile=release".to_string());
        } else if let Some(&flag) = VALUED.iter().find(|flag| **flag == arg) {
            if let Some(value) = next {
                tokens.push(format!("{flag}={value}"));
                index += 1;
            }
        } else if arg == "-F" {
            if let Some(value) = next {
                tokens.push(format!("--features={value}"));
                index += 1;
            }
        } else if arg == "--config" {
            if let Some(value) = next {
                configs.push(format!("--config={value}"));
                index += 1;
            }
        } else if let Some(value) = arg.strip_prefix("--config=") {
            configs.push(format!("--config={value}"));
        } else if arg == "-Z" {
            if let Some(value) = next {
                tokens.push(format!("-Z{value}"));
                index += 1;
            }
        } else if arg.starts_with("-Z") {
            tokens.push(arg.to_string());
        } else if let Some(flag) = VALUED
            .iter()
            .find(|flag| arg.strip_prefix(**flag).is_some_and(|rest| rest.starts_with('=')))
        {
            tokens.push(format!("{flag}={}", &arg[flag.len() + 1..]));
        }
        index += 1;
    }
    tokens.sort();
    tokens.dedup();
    tokens.extend(configs);
    if tokens.is_empty() { "default".to_string() } else { tokens.join(" ") }
}

/// The selection tokens back as arguments for `targo trust check`.
pub(crate) fn selection_args(selection: &str) -> Vec<String> {
    if selection == "default" {
        return Vec::new();
    }
    selection.split(' ').filter(|token| !token.is_empty()).map(str::to_string).collect()
}

/// One obligation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct ObligationRecord {
    /// `<def path>#<local id>`.
    pub(crate) key: String,
    /// The compact kind tag.
    pub(crate) kind: String,
    /// The published status (`proved`, `failed`, `unknown`, …).
    pub(crate) status: String,
    /// What ended the search.
    pub(crate) stop: String,
    /// The location's file, line and column, when the row has one.
    pub(crate) file: Option<String>,
    pub(crate) line: Option<u32>,
    pub(crate) col: Option<u32>,
    /// The grade's encoding axis ([`trust_types::authority_grade::GradeEncoding`]),
    /// or [`UNGRADED`].
    pub(crate) encoding: String,
    /// The grade's discharge axis ([`trust_types::authority_grade::GradeDischarge`]),
    /// or [`UNGRADED`].
    pub(crate) discharge: String,
    /// The grade's premise classes ([`trust_types::authority_grade::GradePremise`]);
    /// empty for an ungraded row.
    pub(crate) premises: Vec<String>,
    /// A `failed` row's [`trust_types::FailureBasis`], spelled as
    /// [`trust_types::FailureBasis::as_str`]; `None` on every other row.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) basis: Option<String>,
}

/// The `encoding` and `discharge` of a row no proof authority graded.
pub(crate) const UNGRADED: &str = "ungraded";

/// Whether a record whose status reads `status` may state a grade discharged
/// as `discharge`: a `proved` row any admitted grade, an `unknown` row (where
/// targo files a compiler `skipped` assumption row) only an `assumed` one, and
/// no other row any grade. So a grade never claims more than the status: a row
/// targo or the compiler demoted after the compiler graded it, a refuted row,
/// or a conditional `skipped` row is written `ungraded`.
fn status_admits_grade(
    status: &str,
    discharge: trust_types::authority_grade::GradeDischarge,
) -> bool {
    use trust_types::authority_grade::GradeDischarge;
    match status {
        "proved" => true,
        "unknown" => discharge == GradeDischarge::Assumed,
        _ => false,
    }
}

/// The record's three grade fields for a row whose final status is `status`
/// and whose compiler-stated grade is `grade`: the grade when the status
/// admits it and it is one a compiler states
/// ([`trust_types::authority_grade::ObligationGrade::admitted`]), otherwise
/// [`UNGRADED`].
pub(crate) fn grade_fields(
    grade: Option<&trust_types::authority_grade::ObligationGrade>,
    status: &str,
) -> (String, String, Vec<String>) {
    match grade
        .filter(|grade| status_admits_grade(status, grade.discharge) && grade.admitted().is_ok())
    {
        Some(grade) => (
            grade.encoding.as_str().to_string(),
            grade.discharge.as_str().to_string(),
            grade.premises.iter().map(|premise| premise.as_str().to_string()).collect(),
        ),
        None => (UNGRADED.to_string(), UNGRADED.to_string(), Vec::new()),
    }
}

/// Refuse grade fields a writer could not have written: both [`UNGRADED`]
/// with no premises, or a grade spelled in `trust_types::authority_grade`'s
/// vocabulary that a compiler states (`ObligationGrade::admitted`: an admitted
/// encoding/discharge pair, so calculus credit only as VF5's authority states
/// it, with premises in declaration order and none repeated) on a status that
/// admits it.
fn check_grade_fields(
    status: &str,
    encoding: &str,
    discharge: &str,
    premises: &[String],
) -> Result<(), String> {
    use trust_types::authority_grade::{
        GradeDischarge, GradeEncoding, GradePremise, ObligationGrade,
    };
    if encoding == UNGRADED || discharge == UNGRADED {
        return if encoding == UNGRADED && discharge == UNGRADED && premises.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "an ungraded row has encoding and discharge `{UNGRADED}` and no premises, not \
                 `{encoding}`, `{discharge}` and {premises:?}"
            ))
        };
    }
    let Some(encoding) = GradeEncoding::parse(encoding) else {
        return Err(format!("unknown grade encoding `{encoding}`"));
    };
    let Some(discharge) = GradeDischarge::parse(discharge) else {
        return Err(format!("unknown grade discharge `{discharge}`"));
    };
    let premises = premises
        .iter()
        .map(|premise| {
            GradePremise::parse(premise).ok_or_else(|| format!("unknown grade premise `{premise}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let grade = ObligationGrade::new(encoding, discharge, &premises);
    grade.admitted()?;
    if !status_admits_grade(status, discharge) {
        return Err(format!("a `{status}` row cannot carry a `{}` grade", discharge.as_str()));
    }
    Ok(())
}

/// The [`trust_types::FailureBasis`] a record spells `basis`.
fn parse_failure_basis(basis: &str) -> Option<trust_types::FailureBasis> {
    [trust_types::FailureBasis::Refuted, trust_types::FailureBasis::UnprovedFailClosed]
        .into_iter()
        .find(|known| known.as_str() == basis)
}

/// Refuse a `basis` a writer could not have written: a `failed` line names
/// one of the two bases, and no other line names any.
fn check_basis(status: &str, basis: Option<&str>) -> Result<(), String> {
    match (status == trust_types::Outcome::Failed.as_str(), basis) {
        (true, Some(basis)) if parse_failure_basis(basis).is_some() => Ok(()),
        (true, Some(basis)) => Err(format!("unknown failure basis `{basis}`")),
        (true, None) => Err("a `failed` row states its `basis`".to_string()),
        (false, None) => Ok(()),
        (false, Some(basis)) => Err(format!("a `{status}` row cannot carry a basis (`{basis}`)")),
    }
}

impl ObligationRecord {
    /// The label the terminal listing prints for this row
    /// (`crate::report::listing_label`): `ASSUMED`, `CONTRACT` or
    /// `CONDITIONAL` by kind, `FAILED` with its basis when nothing refuted it,
    /// otherwise the status's own label. A status outside the published
    /// vocabulary is printed as it is spelled.
    pub(crate) fn listing_label(&self) -> String {
        match trust_types::Outcome::parse(&self.status) {
            Some(outcome) => crate::report::listing_label(
                &self.kind,
                crate::types::VerificationOutcome::from(outcome),
                self.basis.as_deref().and_then(parse_failure_basis),
            ),
            None => self.status.to_uppercase(),
        }
    }

    /// `file:line:col`, or `-` when the obligation has no location.
    pub(crate) fn location_label(&self) -> String {
        match (&self.file, self.line, self.col) {
            (Some(file), Some(line), Some(col)) => format!("{file}:{line}:{col}"),
            _ => "-".to_string(),
        }
    }

    /// Whether the obligation is proved.
    pub(crate) fn is_proved(&self) -> bool {
        self.status == trust_types::Outcome::Proved.as_str()
    }

    /// Whether the listing labels the obligation a plain `PROVED`
    /// (`crate::report::listing_label_is_plain_proof`): proved, and not an
    /// assumption, contract or conditional row.
    pub(crate) fn is_plainly_proved(&self) -> bool {
        self.is_proved() && crate::report::listing_label_is_plain_proof(&self.listing_label())
    }

    /// Whether the obligation was refuted: a counterexample, not a missing
    /// proof.
    pub(crate) fn is_failed(&self) -> bool {
        self.status == trust_types::Outcome::Failed.as_str()
    }

    /// Whether what ended the search is reproducible
    /// (`StopCause::reproducibility` rank 0). A clock, an RSS reading, a crash,
    /// an unexplained stop or a refused admission is not: such a record does
    /// not establish what the obligation's verdict is.
    pub(crate) fn stop_is_reproducible(&self) -> bool {
        trust_types::determinism::StopCause::parse(&self.stop).is_some_and(|cause| {
            cause.reproducibility() == trust_types::determinism::Reproducibility::Deterministic
        })
    }

    /// The total order duplicate rows of one key are chosen by: an unproved
    /// record before a proved one, then status, stop, file, line and column.
    /// The first is kept, so the choice never depends on which unit finished
    /// first.
    fn worst_first(&self) -> impl Ord + '_ {
        (self.is_proved(), &self.status, &self.stop, &self.file, self.line, self.col)
    }
}

/// One function: its source digest and its obligations by local id. A
/// function with no obligation is still a function: the compiler verified it
/// and published only inventory for it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FunctionRecords {
    /// The function's source digest, when the compiler stated it.
    pub(crate) source: Option<String>,
    /// Obligations by local id. A local id that occurs twice (the same
    /// function compiled in two units) keeps its WORST record
    /// ([`ObligationRecord::worst_first`]): a key is proved only where every
    /// row bearing it is.
    pub(crate) obligations: BTreeMap<String, ObligationRecord>,
}

/// One package's functions by def path.
pub(crate) type PackageRecords = BTreeMap<String, FunctionRecords>;

/// One compile error as Cargo reported it (`compiler-message` of a level
/// that starts with `error`), before it is keyed: the package its envelope
/// names, the primary span's file, the error code, the headline message, and
/// the primary span's start.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CompileError {
    pub(crate) package: String,
    pub(crate) file: Option<String>,
    pub(crate) code: Option<String>,
    pub(crate) message: String,
    pub(crate) line: Option<u32>,
    pub(crate) col: Option<u32>,
}

/// The longest message an error line keeps, in bytes; the key digests the
/// whole normalized message.
const MAX_COMPILE_ERROR_MESSAGE_BYTES: usize = 1024;

impl CompileError {
    /// The error of one Cargo `compiler-message` envelope's `message` object,
    /// in `package`, or `None` when it is not one: a level that does not
    /// start with `error`, or rustc's closing `aborting due to …` count.
    ///
    /// rustc spells an ordinary or fatal error's level `error` and an
    /// internal compiler error's (`Bug`, `DelayedBug`) `error: internal
    /// compiler error` (`rustc_errors::Level::to_str`). An ICE is an error
    /// row too, its message led by `internal compiler error: ` as rustc
    /// renders it, so a `bug!`, `span_bug!` or delayed bug prints a row. A
    /// plain panic inside rustc is reported by `rustc_driver_impl::report_ice`
    /// through its own human-readable emitter, outside the JSON stream, so it
    /// is no row: the package shows only as `not concluded`.
    pub(crate) fn of_cargo_diagnostic(
        package: &str,
        diagnostic: &serde_json::Value,
    ) -> Option<Self> {
        use serde_json::Value;
        let level = diagnostic.get("level").and_then(Value::as_str)?;
        let headline = diagnostic.get("message").and_then(Value::as_str).unwrap_or_default();
        let message = match level.strip_prefix("error").map(|rest| rest.strip_prefix(':')) {
            Some(None) if level == "error" => normalize_compile_error_message(headline),
            Some(Some(kind)) if !kind.trim().is_empty() => {
                normalize_compile_error_message(&format!("{}: {headline}", kind.trim()))
            }
            Some(Some(_)) => normalize_compile_error_message(headline),
            _ => return None,
        };
        let spans = diagnostic.get("spans").and_then(Value::as_array);
        if message.starts_with("aborting due to ") && spans.is_none_or(Vec::is_empty) {
            return None;
        }
        let code = diagnostic
            .get("code")
            .and_then(|code| code.get("code"))
            .and_then(Value::as_str)
            .filter(|code| !code.is_empty())
            .map(str::to_string);
        let primary = spans.and_then(|spans| {
            spans
                .iter()
                .find(|span| span.get("is_primary").and_then(Value::as_bool) == Some(true))
                .or_else(|| spans.first())
        });
        let at = |field: &str| {
            primary
                .and_then(|span| span.get(field))
                .and_then(Value::as_u64)
                .and_then(|value| u32::try_from(value).ok())
        };
        Some(Self {
            package: package.to_string(),
            file: primary
                .and_then(|span| span.get("file_name"))
                .and_then(Value::as_str)
                .filter(|file| !file.is_empty())
                .map(str::to_string),
            code,
            message,
            line: at("line_start"),
            col: at("column_start"),
        })
    }
}

/// A message with every run of whitespace one space, trimmed.
fn normalize_compile_error_message(message: &str) -> String {
    message.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// `message` with every source position rustc writes into a type's name cut
/// to its file: `{closure@src/lib.rs:5:13: 5:15}` is `{closure@src/lib.rs}`,
/// as are the `async block`, `coroutine` and `gen block` forms. Such a
/// position is where the closure is, so an edit above it moves it; the key
/// must not move with it.
fn without_type_positions(message: &str) -> String {
    /// The length of the `:<digits>` at the start of `text`, if any.
    fn colon_digits(text: &str) -> Option<usize> {
        let digits = text.strip_prefix(':')?.bytes().take_while(u8::is_ascii_digit).count();
        (digits > 0).then_some(1 + digits)
    }
    /// The length of the `:<line>:<col>` at the start of `text`, if any.
    fn position(text: &str) -> Option<usize> {
        let line = colon_digits(text)?;
        Some(line + colon_digits(&text[line..])?)
    }
    /// The length of the span end `: <line>:<col>` at the start of `text`.
    fn span_end(text: &str) -> Option<usize> {
        let tail = text.strip_prefix(": ")?;
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            return None;
        }
        Some(2 + digits + colon_digits(&tail[digits..])?)
    }
    let mut out = String::with_capacity(message.len());
    let mut rest = message;
    while let Some(at) = rest.find('@') {
        out.push_str(&rest[..=at]);
        rest = &rest[at + 1..];
        // The file runs to the first `:` that starts a position; it has no
        // space, brace or `@`.
        let Some(file_end) = rest
            .char_indices()
            .take_while(|(_, c)| !c.is_whitespace() && !matches!(c, '{' | '}' | '@'))
            .find(|(index, c)| *c == ':' && position(&rest[*index..]).is_some())
            .map(|(index, _)| index)
        else {
            continue;
        };
        out.push_str(&rest[..file_end]);
        rest = &rest[file_end..];
        rest = &rest[position(rest).expect("found above")..];
        if let Some(end) = span_end(rest) {
            rest = &rest[end..];
        }
    }
    out.push_str(rest);
    out
}

/// The key of a compile error before its ordinal:
/// `<file>#<code>-<first 12 hex digits of SHA-256(normalized message)>`, with
/// `-` for no file and `error` for no code. The message is normalized as the
/// module docs say: whitespace, and the source positions in type names.
pub(crate) fn compile_error_key(file: Option<&str>, code: Option<&str>, message: &str) -> String {
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(
        without_type_positions(&normalize_compile_error_message(message)).as_bytes(),
    );
    let digest: String = digest[..6].iter().map(|byte| format!("{byte:02x}")).collect();
    format!("{}#{}-{digest}", file.unwrap_or("-"), code.unwrap_or("error"))
}

/// One keyed compile error of a package's record.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct CompileErrorRecord {
    /// [`compile_error_key`], with `~<n>` on the n-th (n ≥ 2) error of the
    /// same file, code and message in source order.
    pub(crate) key: String,
    pub(crate) code: Option<String>,
    pub(crate) message: String,
    pub(crate) file: Option<String>,
    pub(crate) line: Option<u32>,
    pub(crate) col: Option<u32>,
}

impl CompileErrorRecord {
    /// The changed-only view's label for the row (`crate::agent_delta`):
    /// `ERROR E0308`, or `ERROR` with no code.
    pub(crate) fn label(&self) -> String {
        match &self.code {
            Some(code) => format!("ERROR {code}"),
            None => "ERROR".to_string(),
        }
    }

    /// `file:line:col`, the file alone, or `-`.
    pub(crate) fn location_label(&self) -> String {
        match (&self.file, self.line, self.col) {
            (Some(file), Some(line), Some(col)) => format!("{file}:{line}:{col}"),
            (Some(file), _, _) => file.clone(),
            _ => "-".to_string(),
        }
    }
}

/// Key one package's compile errors: an error reported twice at one place (a
/// library and its test target, say) is one, and errors of one file, code and
/// message are numbered in source order. Sorted by key.
pub(crate) fn key_compile_errors<'a>(
    errors: impl IntoIterator<Item = &'a CompileError>,
) -> Vec<CompileErrorRecord> {
    let unique: BTreeSet<(&Option<String>, Option<u32>, Option<u32>, &Option<String>, &String)> =
        errors
            .into_iter()
            .map(|error| (&error.file, error.line, error.col, &error.code, &error.message))
            .collect();
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut records: Vec<CompileErrorRecord> = unique
        .into_iter()
        .map(|(file, line, col, code, message)| {
            let base = compile_error_key(file.as_deref(), code.as_deref(), message);
            let ordinal = seen.entry(base.clone()).or_default();
            *ordinal += 1;
            let key = if *ordinal == 1 { base } else { format!("{base}~{ordinal}") };
            let mut message = message.clone();
            if message.len() > MAX_COMPILE_ERROR_MESSAGE_BYTES {
                let mut end = MAX_COMPILE_ERROR_MESSAGE_BYTES;
                while !message.is_char_boundary(end) {
                    end -= 1;
                }
                message.truncate(end);
                message.push('…');
            }
            CompileErrorRecord { key, code: code.clone(), message, file: file.clone(), line, col }
        })
        .collect();
    records.sort();
    records
}

/// The functions the compiler published an envelope for, by package and def
/// path, with every source digest stated for each — read from the
/// AUTHENTICATED rows, before the publication normalization elides the
/// zero-obligation inventory rows and the test-harness exclusion rows. It is
/// what tells a function that lost every obligation (still here, with no
/// obligation) from a function that is gone (absent).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FunctionInventory {
    functions: BTreeMap<String, BTreeMap<String, BTreeSet<String>>>,
    /// Functions with a row that carried no stable key.
    unkeyed: BTreeSet<String>,
}

impl FunctionInventory {
    /// The inventory of the authenticated compiler rows.
    pub(crate) fn of_rows(rows: &[VerificationResult]) -> Self {
        let mut inventory = Self::default();
        for row in rows {
            inventory.add(row);
        }
        inventory
    }

    fn add(&mut self, row: &VerificationResult) {
        let Some((package, def_path, source)) = row_function(row) else {
            self.unkeyed.insert(row.function.clone());
            return;
        };
        let digests =
            self.functions.entry(package).or_default().entry(def_path.to_string()).or_default();
        digests.extend(source);
    }
}

/// A row's `(package, def path, function source digest)`, from its identity.
fn row_function(row: &VerificationResult) -> Option<(String, String, Option<String>)> {
    let identity = structured_transport_evidence(row).and_then(|e| e.identity)?;
    let (def_path, _) = trust_types::obligation_identity::split_obligation_key(&identity.key)?;
    Some((identity.package.clone(), def_path.to_string(), identity.function_source_sha256.clone()))
}

/// The packages a run was asked about.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct RunScope {
    /// The packages the run selected (`-p`, `--workspace`, or Cargo's default
    /// members): a baseline's entry for one of these is replaced by the run's,
    /// or dropped when the run has none.
    pub(crate) selected: BTreeSet<String>,
    /// Every package in the workspace's resolve — its members and everything
    /// they depend on. A baseline package that is not one is gone (deleted, or
    /// no longer depended on) and is dropped; one that is stays, whether or not
    /// this run selected it. Empty outside Cargo, where nothing is dropped for
    /// that reason.
    pub(crate) resolved: BTreeSet<String>,
}

/// The obligations of one run, by package.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObligationRecords {
    /// What the run was.
    pub(crate) facts: RunFacts,
    /// Which packages the run was asked about.
    pub(crate) scope: RunScope,
    /// Packages by name: every function the compiler verified, with its
    /// obligations.
    pub(crate) packages: BTreeMap<String, PackageRecords>,
    /// Functions with a row that carried no stable key; the run is then
    /// could-not-run (`UnitDeterminism::unkeyed_functions`) and these rows are
    /// in no package.
    pub(crate) unkeyed_functions: Vec<String>,
    /// `<package> <def path>` of every def path the run published with two
    /// different source digests: two units (a library and a binary of one
    /// package, say) compiled two different functions under one path. Their
    /// keys cannot be told apart, so the run is not a measurement.
    pub(crate) conflicting_functions: Vec<String>,
    /// Every package the run selected or verified, or that reported a compile
    /// error, with what it established (T7c): the one source of its record
    /// header and its package record.
    pub(crate) units: PackageFactsByName,
    /// The keyed compile errors ([`key_compile_errors`]) of each package that
    /// reported one.
    pub(crate) compile_errors: BTreeMap<String, Vec<CompileErrorRecord>>,
    /// The test results of a `test` run, by package (`crate::test_results`):
    /// `Some` (every package's record names `"tests"`) for a run that
    /// executed or refused its harnesses, `None` for every other run.
    pub(crate) tests: Option<BTreeMap<String, crate::test_results::PackageTests>>,
    /// The libtest arguments of that run's harnesses, without the result
    /// channel ([`crate::test_results::harness_arguments`]).
    pub(crate) test_arguments: Vec<String>,
    /// The island sections of each package that published island rows
    /// (module docs, CLEAN ISLANDS), by crate.
    pub(crate) clean_islands: BTreeMap<String, clean_islands::PackageCleanIslands>,
}

impl ObligationRecords {
    /// Project the published rows of a run, over the function `inventory` of
    /// its authenticated rows, and account for each package the run selected
    /// or verified over its share of the rows and of the `coverage` rows.
    pub(crate) fn of_rows(
        rows: &[VerificationResult],
        inventory: &FunctionInventory,
        facts: RunFacts,
        scope: RunScope,
        coverage: &RunCoverage<'_>,
    ) -> Self {
        let mut inventory = inventory.clone();
        for row in rows {
            inventory.add(row);
        }
        let mut packages: BTreeMap<String, PackageRecords> = BTreeMap::new();
        let mut conflicting = Vec::new();
        let mut conflicting_by_package: BTreeMap<&str, usize> = BTreeMap::new();
        for (package, functions) in &inventory.functions {
            let records = packages.entry(package.clone()).or_default();
            for (def_path, digests) in functions {
                if digests.len() > 1 {
                    conflicting.push(format!("{package} {def_path}"));
                    *conflicting_by_package.entry(package).or_default() += 1;
                }
                records.insert(
                    def_path.clone(),
                    FunctionRecords {
                        source: (digests.len() == 1).then(|| digests.first().cloned()).flatten(),
                        obligations: BTreeMap::new(),
                    },
                );
            }
        }
        // Each row's package, by its stable key; a row with no key names no
        // package: it is in no package's share, and it makes every package
        // could-not-run (`crate::package_record`).
        let mut attributed: BTreeMap<String, Vec<&VerificationResult>> = BTreeMap::new();
        let mut unattributed: Vec<&VerificationResult> = Vec::new();
        for row in rows {
            let Some(evidence) = structured_transport_evidence(row) else {
                unattributed.push(row);
                continue;
            };
            let Some(identity) = evidence.identity else {
                unattributed.push(row);
                continue;
            };
            attributed.entry(identity.package.clone()).or_default().push(row);
            let Some((def_path, local_id)) =
                trust_types::obligation_identity::split_obligation_key(&identity.key)
            else {
                continue;
            };
            let status = crate::determinism_report::row_status(row).as_str().to_string();
            let (encoding, discharge, premises) = grade_fields(evidence.grade.as_ref(), &status);
            let record = ObligationRecord {
                encoding,
                discharge,
                premises,
                basis: row.failure_basis().map(|basis| basis.as_str().to_string()),
                key: identity.key.clone(),
                kind: row.kind.clone(),
                status,
                stop: crate::determinism_report::row_stop_cause(row).as_str().to_string(),
                file: row.location.as_ref().map(|span| span.file.clone()),
                line: row.location.as_ref().map(|span| span.line_start),
                col: row.location.as_ref().map(|span| span.col_start),
            };
            let function = packages
                .entry(identity.package.clone())
                .or_default()
                .entry(def_path.to_string())
                .or_default();
            function
                .obligations
                .entry(local_id.to_string())
                .and_modify(|existing| {
                    if record.worst_first() < existing.worst_first() {
                        *existing = record.clone();
                    }
                })
                .or_insert(record);
        }
        let mut coverage_by_package: BTreeMap<&str, Vec<&trust_types::CoverageTransportSummary>> =
            BTreeMap::new();
        for row in coverage.rows {
            coverage_by_package.entry(coverage_package(row)).or_default().push(row);
        }
        let mut errors_by_package: BTreeMap<&str, Vec<&CompileError>> = BTreeMap::new();
        for error in coverage.compile_errors {
            errors_by_package.entry(error.package.as_str()).or_default().push(error);
        }
        let compile_errors: BTreeMap<String, Vec<CompileErrorRecord>> = errors_by_package
            .into_iter()
            .map(|(package, errors)| (package.to_string(), key_compile_errors(errors)))
            .collect();
        let names: BTreeSet<String> = packages
            .keys()
            .chain(&scope.selected)
            .chain(attributed.keys())
            .chain(compile_errors.keys())
            .cloned()
            .chain(coverage_by_package.keys().map(|package| (*package).to_string()))
            .collect();
        // The run's keyless rows, accounted for on their own: which functions
        // they name, which of them the compiler published and which are
        // targo's transport defects (`UnitDeterminism::of_rows`). Every
        // package carries this, as the run does.
        let keyless = UnitDeterminism::of_rows(unattributed, &[]);
        let units = names
            .into_iter()
            .map(|package| {
                let own = attributed.get(&package).map(Vec::as_slice).unwrap_or_default();
                let facts = PackageFacts::of_package(
                    own.iter().copied(),
                    &keyless,
                    coverage_by_package
                        .get(package.as_str())
                        .map(Vec::as_slice)
                        .unwrap_or_default(),
                    coverage.missing.contains(&package),
                    coverage.publication_stops,
                    &package,
                    conflicting_by_package.get(package.as_str()).copied().unwrap_or(0),
                );
                (package, facts)
            })
            .collect();
        Self {
            facts,
            scope,
            packages,
            unkeyed_functions: inventory.unkeyed.into_iter().collect(),
            conflicting_functions: conflicting,
            units,
            compile_errors,
            tests: None,
            test_arguments: Vec::new(),
            clean_islands: BTreeMap::new(),
        }
    }

    /// The same records, carrying the island rows each unit published, by
    /// the unit's package (module docs, CLEAN ISLANDS). `proof_units` names
    /// the package of every proof unit the run declared, one entry per unit
    /// (`None` when it declared none). Disclosure only: no fact, vector,
    /// count or coverage above reads them.
    pub(crate) fn with_clean_islands<'a>(
        mut self,
        proof_units: Option<&[&str]>,
        units: impl IntoIterator<
            Item = (&'a str, &'a trust_types::clean_island_rows::CleanIslandRowsTransport),
        >,
    ) -> Self {
        self.clean_islands = clean_islands::sections_of_units(proof_units, units);
        self
    }

    /// The same records, carrying a `test` run's results and the libtest
    /// `arguments` its harnesses were given. Every package with a result is
    /// one the run selected, so it already has facts.
    pub(crate) fn with_tests(
        mut self,
        tests: BTreeMap<String, crate::test_results::PackageTests>,
        arguments: Vec<String>,
    ) -> Self {
        self.tests = Some(tests);
        self.test_arguments = arguments;
        self
    }

    /// The `trust.obligations.v1` bytes of one package: `None` for a package
    /// the run neither selected nor verified.
    pub(crate) fn package_ndjson(&self, package: &str) -> Option<String> {
        let unit = self.units.get(package)?;
        let header = RecordHeader {
            package,
            lane: &self.facts.lane,
            policy: &self.facts.policy,
            selection: &self.facts.selection,
            targo_trust_commit: &self.facts.targo_trust_commit,
            profile: &self.facts.profile,
            outcome: unit.determinism.outcome.as_str(),
            vector: &unit.vector_digest(),
            coverage_complete: unit.coverage_complete(),
            concluded: unit.coverage.is_some(),
            degraded_anchors: unit.degraded_anchors,
        };
        let empty = PackageRecords::new();
        let no_tests = crate::test_results::PackageTests::default();
        let no_islands = clean_islands::PackageCleanIslands::default();
        Some(render_package_ndjson_with_islands(
            &header,
            self.compile_errors.get(package).map(Vec::as_slice).unwrap_or_default(),
            self.tests.as_ref().map(|tests| {
                (self.test_arguments.as_slice(), tests.get(package).unwrap_or(&no_tests))
            }),
            self.clean_islands.get(package).unwrap_or(&no_islands),
            self.packages.get(package).unwrap_or(&empty),
        ))
    }

    /// The `trust.package.v1` record of one package (`crate::package_record`):
    /// `None` for a package the run neither selected nor verified.
    pub(crate) fn package_record_json(&self, package: &str) -> Option<String> {
        Some(self.units.get(package)?.record_json(package, &self.facts))
    }

    /// Write, for every package the run selected or verified or that reported
    /// a compile error, its obligation
    /// record `<target>/trust/obligations/<package>.ndjson` and its package
    /// record `<target>/trust/packages/<package>.json`, atomically each.
    pub(crate) fn write_records(&self, target_dir: &Path) -> io::Result<Vec<PathBuf>> {
        let obligations = records_dir(target_dir);
        let package_records = package_records_dir(target_dir);
        let mut written = Vec::new();
        for package in self.units.keys() {
            for (path, bytes) in [
                (
                    obligation_record_path(&obligations, package),
                    self.package_ndjson(package).expect("the package has facts"),
                ),
                (
                    package_record_path(&package_records, package),
                    self.package_record_json(package).expect("the package has facts"),
                ),
            ] {
                crate::durable_io::atomic_write_private(&path, bytes.as_bytes())?;
                written.push(path);
            }
        }
        Ok(written)
    }
}

/// The header facts of one package's `trust.obligations.v1` record. A crate
/// run takes them from its [`RunFacts`] and [`PackageFacts`]; a `.lean` check
/// (`crate::lean_cli`) states its own. Both render through
/// [`render_package_ndjson`], so there is one format and one writer of it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RecordHeader<'a> {
    pub(crate) package: &'a str,
    pub(crate) lane: &'a str,
    pub(crate) policy: &'a str,
    pub(crate) selection: &'a str,
    pub(crate) targo_trust_commit: &'a str,
    pub(crate) profile: &'a str,
    pub(crate) outcome: &'a str,
    pub(crate) vector: &'a str,
    pub(crate) coverage_complete: bool,
    /// Whether the rows are a measurement of the package's obligations
    /// (module docs, CONCLUDED).
    pub(crate) concluded: bool,
    pub(crate) degraded_anchors: usize,
}

/// The `trust.obligations.v1` bytes of one package that reported no compile
/// error ([`render_package_ndjson_with_errors`]).
pub(crate) fn render_package_ndjson(
    header: &RecordHeader<'_>,
    functions: &PackageRecords,
) -> String {
    render_package_ndjson_with_errors(header, &[], functions)
}

/// The `trust.obligations.v1` bytes of one package: the header line, its
/// compile-error lines in key order, then each function's `fn` line followed
/// by its obligation lines.
pub(crate) fn render_package_ndjson_with_errors(
    header: &RecordHeader<'_>,
    compile_errors: &[CompileErrorRecord],
    functions: &PackageRecords,
) -> String {
    render_package_ndjson_with_tests(header, compile_errors, None, functions)
}

/// [`render_package_ndjson_with_errors`] with a `test` run's harness
/// arguments and results: with `tests`, the header names the arguments in
/// `"tests"` and the harness and case lines follow the compile-error lines
/// (module docs, TEST RESULTS).
pub(crate) fn render_package_ndjson_with_tests(
    header: &RecordHeader<'_>,
    compile_errors: &[CompileErrorRecord],
    tests: Option<(&[String], &crate::test_results::PackageTests)>,
    functions: &PackageRecords,
) -> String {
    render_package_ndjson_with_islands(
        header,
        compile_errors,
        tests,
        &clean_islands::PackageCleanIslands::default(),
        functions,
    )
}

/// [`render_package_ndjson_with_tests`] with the package's island sections,
/// after the test lines and before the first function line (module docs,
/// CLEAN ISLANDS).
pub(crate) fn render_package_ndjson_with_islands(
    header: &RecordHeader<'_>,
    compile_errors: &[CompileErrorRecord],
    tests: Option<(&[String], &crate::test_results::PackageTests)>,
    islands: &clean_islands::PackageCleanIslands,
    functions: &PackageRecords,
) -> String {
    let mut header = serde_json::json!({
        "schema": OBLIGATIONS_SCHEMA,
        "package": header.package,
        "lane": header.lane,
        "policy": header.policy,
        "selection": header.selection,
        "seal": crate::package_record::absent(crate::package_record::SEAL_ABSENT),
        "targo_trust_commit": header.targo_trust_commit,
        "profile": header.profile,
        "outcome": header.outcome,
        "vector": header.vector,
        "coverage_complete": header.coverage_complete,
        "concluded": header.concluded,
        "degraded_anchors": header.degraded_anchors,
    });
    if let Some((arguments, _)) = tests {
        header["tests"] = serde_json::json!(arguments);
    }
    let mut out = String::new();
    push_json_line(&mut out, &header);
    let mut compile_errors: Vec<&CompileErrorRecord> = compile_errors.iter().collect();
    compile_errors.sort();
    for error in compile_errors {
        push_json_line(
            &mut out,
            &serde_json::json!({
                "compile_error": error.key,
                "code": error.code,
                "message": error.message,
                "file": error.file,
                "line": error.line,
                "col": error.col,
            }),
        );
    }
    if let Some((_, tests)) = tests {
        let mut harnesses: Vec<&crate::test_results::TestHarnessRecord> =
            tests.harnesses.iter().collect();
        harnesses.sort();
        for harness in harnesses {
            push_json_line(
                &mut out,
                &serde_json::json!({
                    "test_harness": harness.key,
                    "concluded": harness.concluded,
                    "reason": harness.reason,
                }),
            );
        }
        let mut cases: Vec<&crate::test_results::TestCaseRecord> = tests.cases.iter().collect();
        cases.sort();
        for case in cases {
            push_json_line(
                &mut out,
                &serde_json::json!({ "test": case.key, "outcome": case.outcome.as_str() }),
            );
        }
    }
    clean_islands::render(&mut out, islands);
    for (def_path, function) in functions {
        push_json_line(&mut out, &serde_json::json!({ "fn": def_path, "source": function.source }));
        for record in function.obligations.values() {
            let mut line = serde_json::json!({
                "key": record.key,
                "kind": record.kind,
                "status": record.status,
                "stop": record.stop,
                "file": record.file,
                "line": record.line,
                "col": record.col,
                "encoding": record.encoding,
                "discharge": record.discharge,
                "premises": record.premises,
            });
            if let Some(basis) = &record.basis {
                line["basis"] = serde_json::Value::String(basis.clone());
            }
            push_json_line(&mut out, &line);
        }
    }
    out
}

/// One package's `trust.obligations.v1` record, read back
/// ([`parse_package_ndjson`]): the header's facts and the obligation lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PackageObligations {
    pub(crate) package: String,
    pub(crate) lane: String,
    pub(crate) policy: String,
    pub(crate) selection: String,
    pub(crate) targo_trust_commit: String,
    pub(crate) profile: String,
    /// The package's determinism outcome, as written (`measured`, …).
    pub(crate) outcome: String,
    /// The package's verdict-vector digest.
    pub(crate) vector: String,
    pub(crate) coverage_complete: bool,
    /// Whether the rows are a measurement of the package's obligations
    /// (module docs, CONCLUDED): only then are they compared with another
    /// record's.
    pub(crate) concluded: bool,
    /// Every function line: def path to its source digest, when stated. A
    /// function whose obligations were all elided is here with none below it.
    pub(crate) functions: BTreeMap<String, Option<String>>,
    /// The obligation lines in record order: functions in def-path order,
    /// obligations in key order, one line per key (a key two units published
    /// keeps its worst row, [`ObligationRecord::worst_first`]).
    pub(crate) obligations: Vec<ObligationRecord>,
    /// The compile-error lines, in key order.
    pub(crate) compile_errors: Vec<CompileErrorRecord>,
    /// A `test` run's record: the libtest arguments its harnesses were given
    /// (its header's `"tests"`). `None` for every other record.
    pub(crate) tests: Option<Vec<String>>,
    /// The harness lines, in key order.
    pub(crate) test_harnesses: Vec<crate::test_results::TestHarnessRecord>,
    /// The case lines, in key order.
    pub(crate) test_cases: Vec<crate::test_results::TestCaseRecord>,
    /// The island sections, by crate (module docs, CLEAN ISLANDS).
    pub(crate) clean_islands: clean_islands::PackageCleanIslands,
}

/// The header line, every field named: a record of another shape is refused.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ObligationsHeader {
    schema: String,
    package: String,
    lane: String,
    policy: String,
    selection: String,
    #[serde(rename = "seal")]
    _seal: serde::de::IgnoredAny,
    targo_trust_commit: String,
    profile: String,
    outcome: String,
    vector: String,
    coverage_complete: bool,
    concluded: bool,
    #[serde(rename = "degraded_anchors")]
    _degraded_anchors: usize,
    /// Present on a `test` run's record only: its harnesses' arguments.
    #[serde(default)]
    tests: Option<Vec<String>>,
}

/// A test-harness line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TestHarnessLine {
    test_harness: String,
    concluded: bool,
    reason: Option<String>,
}

/// A test-case line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TestCaseLine {
    test: String,
    outcome: String,
}

/// A function line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FunctionLine {
    #[serde(rename = "fn")]
    def_path: String,
    source: Option<String>,
}

/// A compile-error line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CompileErrorLine {
    compile_error: String,
    code: Option<String>,
    message: String,
    file: Option<String>,
    line: Option<u32>,
    col: Option<u32>,
}

/// An obligation line.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ObligationLine {
    key: String,
    kind: String,
    status: String,
    stop: String,
    file: Option<String>,
    line: Option<u32>,
    col: Option<u32>,
    /// The grade fields are required: a line without them is refused.
    encoding: String,
    discharge: String,
    premises: Vec<String>,
    /// Present on, and only on, a `failed` line.
    #[serde(default)]
    basis: Option<String>,
}

/// Read back the bytes [`ObligationRecords::package_ndjson`] writes: the
/// header, then function and obligation lines. Anything else — another
/// schema, a field this format does not have, a line that is neither — is an
/// error naming the line. There is one format and no reader of an older one.
pub(crate) fn parse_package_ndjson(text: &str) -> Result<PackageObligations, String> {
    let mut lines = text.lines();
    let header_line = lines.next().ok_or_else(|| "the record is empty".to_string())?;
    let header: ObligationsHeader = serde_json::from_str(header_line)
        .map_err(|error| format!("line 1 is not a `{OBLIGATIONS_SCHEMA}` header: {error}"))?;
    if header.schema != OBLIGATIONS_SCHEMA {
        return Err(format!("line 1 names schema `{}`, not `{OBLIGATIONS_SCHEMA}`", header.schema));
    }
    let mut obligations = Vec::new();
    let mut functions = BTreeMap::new();
    let mut compile_errors: Vec<CompileErrorRecord> = Vec::new();
    let tests = header.tests.is_some();
    let mut test_harnesses: Vec<crate::test_results::TestHarnessRecord> = Vec::new();
    let mut test_cases: Vec<crate::test_results::TestCaseRecord> = Vec::new();
    let mut islands = clean_islands::PackageCleanIslands::default();
    let mut last_island_crate: Option<String> = None;
    for (index, line) in lines.enumerate() {
        let number = index + 2;
        let value: serde_json::Value = serde_json::from_str(line)
            .map_err(|error| format!("line {number} is not JSON: {error}"))?;
        if value.get("compile_error").is_some() {
            let error = serde_json::from_value::<CompileErrorLine>(value)
                .map_err(|error| format!("line {number} is not a compile-error line: {error}"))?;
            // After the header and before every function line, in key order,
            // each key once: as the writer puts them.
            if !functions.is_empty()
                || !obligations.is_empty()
                || !test_harnesses.is_empty()
                || !test_cases.is_empty()
                || !islands.is_empty()
            {
                return Err(format!(
                    "line {number} is a compile-error line after a test, island or function line"
                ));
            }
            if compile_errors.last().is_some_and(|last| last.key >= error.compile_error) {
                return Err(format!(
                    "line {number} is a compile-error line out of key order or repeated"
                ));
            }
            compile_errors.push(CompileErrorRecord {
                key: error.compile_error,
                code: error.code,
                message: error.message,
                file: error.file,
                line: error.line,
                col: error.col,
            });
            continue;
        }
        if value.get("test_harness").is_some() {
            let harness = serde_json::from_value::<TestHarnessLine>(value)
                .map_err(|error| format!("line {number} is not a test-harness line: {error}"))?;
            // In a test run's record only, after the compile errors and
            // before every case and function line, in key order; a harness
            // that concluded states no reason and one that did not states one.
            if !tests {
                return Err(format!(
                    "line {number} is a test-harness line in a record that is not a test run's"
                ));
            }
            if !functions.is_empty()
                || !obligations.is_empty()
                || !test_cases.is_empty()
                || !islands.is_empty()
            {
                return Err(format!(
                    "line {number} is a test-harness line after a case, island or function line"
                ));
            }
            if test_harnesses.last().is_some_and(|last| last.key >= harness.test_harness) {
                return Err(format!(
                    "line {number} is a test-harness line out of key order or repeated"
                ));
            }
            if harness.concluded == harness.reason.is_some() {
                return Err(format!(
                    "line {number} is a test-harness line whose reason does not match `concluded`"
                ));
            }
            test_harnesses.push(crate::test_results::TestHarnessRecord {
                key: harness.test_harness,
                concluded: harness.concluded,
                reason: harness.reason,
            });
            continue;
        }
        if value.get("test").is_some() {
            let case = serde_json::from_value::<TestCaseLine>(value)
                .map_err(|error| format!("line {number} is not a test-case line: {error}"))?;
            if !tests {
                return Err(format!(
                    "line {number} is a test-case line in a record that is not a test run's"
                ));
            }
            if !functions.is_empty() || !obligations.is_empty() || !islands.is_empty() {
                return Err(format!(
                    "line {number} is a test-case line after an island or function line"
                ));
            }
            if test_cases.last().is_some_and(|last| last.key >= case.test) {
                return Err(format!(
                    "line {number} is a test-case line out of key order or repeated"
                ));
            }
            let outcome = crate::test_results::CaseOutcome::parse(&case.outcome)
                .ok_or_else(|| format!("line {number} names test outcome `{}`", case.outcome))?;
            let record = crate::test_results::TestCaseRecord { key: case.test, outcome };
            // A case belongs to a harness this record states, and a case of a
            // harness that did not conclude is never `passed` or `ignored`.
            match test_harnesses.iter().find(|harness| harness.key == record.harness()) {
                None => return Err(format!("line {number} is a test case of no harness line")),
                Some(harness)
                    if !harness.concluded
                        && matches!(
                            record.outcome,
                            crate::test_results::CaseOutcome::Passed
                                | crate::test_results::CaseOutcome::Ignored
                        ) =>
                {
                    return Err(format!(
                        "line {number} is a `{}` case of a harness that did not conclude",
                        record.outcome.as_str()
                    ));
                }
                Some(_) => {}
            }
            test_cases.push(record);
            continue;
        }
        if value.get("clean_island_units").is_some()
            || value.get("clean_islands").is_some()
            || value.get("clean_decl").is_some()
        {
            // After the test lines and before every function line.
            if !functions.is_empty() || !obligations.is_empty() {
                return Err(format!("line {number} is an island line after a function line"));
            }
            clean_islands::parse_line(&mut islands, &mut last_island_crate, value)
                .map_err(|error| format!("line {number} {error}"))?;
            continue;
        }
        if value.get("fn").is_some() {
            let function = serde_json::from_value::<FunctionLine>(value)
                .map_err(|error| format!("line {number} is not a function line: {error}"))?;
            functions.insert(function.def_path, function.source);
            continue;
        }
        let line: ObligationLine = serde_json::from_value(value)
            .map_err(|error| format!("line {number} is not an obligation line: {error}"))?;
        check_grade_fields(&line.status, &line.encoding, &line.discharge, &line.premises)
            .and_then(|()| check_basis(&line.status, line.basis.as_deref()))
            .map_err(|error| format!("line {number} is not an obligation line: {error}"))?;
        obligations.push(ObligationRecord {
            encoding: line.encoding,
            discharge: line.discharge,
            premises: line.premises,
            basis: line.basis,
            key: line.key,
            kind: line.kind,
            status: line.status,
            stop: line.stop,
            file: line.file,
            line: line.line,
            col: line.col,
        });
    }
    Ok(PackageObligations {
        package: header.package,
        lane: header.lane,
        policy: header.policy,
        selection: header.selection,
        targo_trust_commit: header.targo_trust_commit,
        profile: header.profile,
        outcome: header.outcome,
        vector: header.vector,
        coverage_complete: header.coverage_complete,
        concluded: header.concluded,
        functions,
        obligations,
        compile_errors,
        tests: header.tests,
        test_harnesses,
        test_cases,
        clean_islands: islands,
    })
}

/// Read and parse one obligation record file ([`parse_package_ndjson`]),
/// bounded as a saved proof report is.
pub(crate) fn read_package_obligations(path: &Path) -> Result<PackageObligations, String> {
    let text = crate::input_limits::read_bounded_utf8_file(
        path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| format!("cannot read `{}`: {error}", path.display()))?;
    parse_package_ndjson(&text).map_err(|error| format!("`{}`: {error}", path.display()))
}

/// The obligation record file of `package` under `dir`.
pub(crate) fn obligation_record_path(dir: &Path, package: &str) -> PathBuf {
    dir.join(format!("{}.ndjson", record_file_stem(package)))
}

/// A package name as a file stem: Cargo package names are `[A-Za-z0-9_-]`, and
/// anything else (a crate name outside Cargo cannot carry one either) is
/// replaced so a record can never name a path outside its directory.
pub(crate) fn record_file_stem(package: &str) -> String {
    package
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '_' { c } else { '_' })
        .collect()
}

fn push_json_line(out: &mut String, value: &serde_json::Value) {
    out.push_str(&serde_json::to_string(value).expect("a JSON value serializes"));
    out.push('\n');
}

/// The default record directory of a Cargo target directory.
pub(crate) fn records_dir(target_dir: &Path) -> PathBuf {
    target_dir.join("trust").join("obligations")
}

pub(crate) mod clean_islands;

#[cfg(test)]
#[path = "obligations_tests.rs"]
mod tests;
