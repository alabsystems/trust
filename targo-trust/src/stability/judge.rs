//! The judgements of `targo trust stability`: per axis and package, whether
//! two legs' records agree, and whether the negative control was caught; and
//! the report the verb prints.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_types::determinism::{
    NotedStop, Reproducibility, StopCause, StopCauseTally, UnitOutcome, short_id,
};

use super::legs::PackageRecordFacts;
use super::{
    Axis, EXIT_COULD_NOT_RUN, EXIT_DIFFERING, EXIT_EQUAL, EXIT_USAGE, Report, STABILITY_SCHEMA,
};
use crate::obligations::PackageObligations;

/// The `targo_trust_commit` of a build that embedded no commit
/// (`crate::obligations::targo_trust_commit`): two such builds cannot be told
/// apart.
const UNBOUND_COMMIT: &str = "unbound";

/// An obligation's verdict as the vector holds it: published status and what
/// ended the search.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Verdict {
    pub(crate) status: String,
    pub(crate) stop: String,
}

impl Verdict {
    fn label(&self) -> String {
        format!("{}/{}", self.status, self.stop)
    }

    fn json(&self) -> serde_json::Value {
        serde_json::json!({ "status": self.status, "stop": self.stop })
    }
}

/// One package as one side of an axis recorded it: its `trust.package.v1`
/// record and its `trust.obligations.v1` record, from this host's leg or
/// another host's run alike.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UnitFacts {
    pub(crate) package: String,
    pub(crate) lane: String,
    pub(crate) policy: String,
    pub(crate) selection: String,
    pub(crate) targo_trust_commit: String,
    pub(crate) profile: String,
    pub(crate) outcome: UnitOutcome,
    pub(crate) vector: String,
    pub(crate) coverage_complete: bool,
    /// The worker-thread cap the run passed.
    pub(crate) worker_threads: u64,
    /// Obligations by stop cause, and the backstop ledger.
    pub(crate) stop_causes: StopCauseTally,
    pub(crate) noted_stops: Vec<NotedStop>,
    /// Def paths published with two source digests, whose keys cannot be told
    /// apart.
    pub(crate) conflicting_def_paths: usize,
    /// Every obligation key with its verdict.
    pub(crate) verdicts: BTreeMap<String, Verdict>,
}

fn verdicts_of(record: &PackageObligations) -> BTreeMap<String, Verdict> {
    record
        .obligations
        .iter()
        .map(|obligation| {
            (
                obligation.key.clone(),
                Verdict { status: obligation.status.clone(), stop: obligation.stop.clone() },
            )
        })
        .collect()
}

/// A record's `outcome`, of the three plan §2 names; anything else is refused.
fn parse_outcome(raw: &str) -> Result<UnitOutcome, String> {
    [UnitOutcome::Measured, UnitOutcome::NotReproducible, UnitOutcome::CouldNotRun]
        .into_iter()
        .find(|outcome| outcome.as_str() == raw)
        .ok_or_else(|| {
            format!("outcome `{raw}` is none of measured, not-reproducible, could-not-run")
        })
}

/// What a package's record establishes about it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Standing {
    /// A measurement: its vector can be compared.
    Measured,
    /// Not a measurement, for a defect its producer must fix (plan §2's
    /// `not-reproducible`): a solver fault, an unexplained stop, or an outcome
    /// no stated stop explains.
    NotReproducible(String),
    /// Not a measurement, for a limit of the host or an incomplete run: the
    /// verifier could not run, coverage is incomplete, only a backstop (a
    /// clock, an RSS reading, a refused admission) ended work, or two
    /// functions share a def path.
    CouldNotRun(String),
}

/// A stop that ended work and is no measurement: a backstop, which the plan
/// counts as the host's limit (`could-not-run`), or anything else, which is a
/// defect (`not-reproducible`).
fn is_backstop(cause: StopCause) -> bool {
    matches!(cause, StopCause::WallBackstop | StopCause::RssBackstop | StopCause::AdmissionRefused)
}

impl UnitFacts {
    /// A package from its two records, which are rendered from one value by
    /// the check that wrote them and must agree.
    pub(crate) fn of_records(
        record: PackageRecordFacts,
        obligations: PackageObligations,
    ) -> Result<Self, String> {
        for (field, package_record, obligation_header) in [
            ("package", &record.package, &obligations.package),
            ("outcome", &record.outcome, &obligations.outcome),
            ("profile", &record.profile, &obligations.profile),
            ("vector", &record.vector, &obligations.vector),
        ] {
            if package_record != obligation_header {
                return Err(format!(
                    "the package record's {field} `{package_record}` is not its obligation \
                     record's `{obligation_header}`"
                ));
            }
        }
        Ok(Self {
            verdicts: verdicts_of(&obligations),
            outcome: parse_outcome(&obligations.outcome)?,
            package: obligations.package,
            lane: obligations.lane,
            policy: obligations.policy,
            selection: obligations.selection,
            targo_trust_commit: obligations.targo_trust_commit,
            profile: obligations.profile,
            vector: obligations.vector,
            coverage_complete: obligations.coverage_complete,
            worker_threads: record.worker_threads,
            stop_causes: record.stop_causes,
            noted_stops: record.noted_stops,
            conflicting_def_paths: record.conflicting_def_paths,
        })
    }

    /// The stops the record states that are not deterministic, from its rows'
    /// tally and its backstop ledger, split into backstops and defects.
    fn nondeterministic_stops(&self) -> (Vec<String>, Vec<String>) {
        let rows = self
            .stop_causes
            .iter()
            .filter(|(cause, _)| cause.reproducibility() != Reproducibility::Deterministic)
            .map(|(cause, count)| (cause, format!("{cause}={count}")));
        let ledger = self
            .noted_stops
            .iter()
            .filter(|stop| stop.cause.reproducibility() != Reproducibility::Deterministic)
            .map(|stop| (stop.cause, format!("ledger {stop}")));
        let (backstops, defects): (Vec<_>, Vec<_>) =
            rows.chain(ledger).partition(|(cause, _)| is_backstop(*cause));
        let names = |stops: Vec<(StopCause, String)>| stops.into_iter().map(|(_, s)| s).collect();
        (names(backstops), names(defects))
    }

    /// What the record establishes: a measurement (`measured`, coverage
    /// complete, every stop deterministic, no def path published with two
    /// source digests — the rule `--save-baseline` applies), a defect, or a
    /// host's limit. A defect is named whatever else the record says, unless
    /// the run itself could not run or its coverage is incomplete, which leave
    /// its stops no account of the package.
    pub(crate) fn standing(&self) -> Standing {
        let (backstops, defects) = self.nondeterministic_stops();
        let mut reasons = vec![format!("outcome {}", self.outcome)];
        if !defects.is_empty() {
            reasons.push(format!("stops that are defects: {}", defects.join(", ")));
        }
        if !backstops.is_empty() {
            reasons.push(format!("backstops that fired: {}", backstops.join(", ")));
        }
        if !self.coverage_complete {
            reasons.push("coverage incomplete".to_string());
        }
        if self.conflicting_def_paths > 0 {
            reasons.push(format!(
                "{} def path(s) published with two source digests",
                self.conflicting_def_paths
            ));
        }
        let reason = reasons.join("; ");
        if self.outcome == UnitOutcome::CouldNotRun || !self.coverage_complete {
            return Standing::CouldNotRun(reason);
        }
        if !defects.is_empty() {
            return Standing::NotReproducible(reason);
        }
        match self.outcome {
            UnitOutcome::NotReproducible if backstops.is_empty() => Standing::NotReproducible(
                format!("{reason}; neither its rows nor its ledger state a stop that explains it"),
            ),
            UnitOutcome::Measured if !backstops.is_empty() => Standing::NotReproducible(format!(
                "{reason}: a measured outcome its own stops contradict"
            )),
            UnitOutcome::Measured if self.conflicting_def_paths == 0 => Standing::Measured,
            _ => Standing::CouldNotRun(reason),
        }
    }

    /// Obligations a `cause` stopped, by the rows' tally and the ledger's
    /// count (a stopped solve that published no row is counted only there).
    pub(crate) fn stopped_on(&self, cause: StopCause) -> (u64, u64) {
        let ledger =
            self.noted_stops.iter().filter(|stop| stop.cause == cause).map(|stop| stop.count).sum();
        (self.stop_causes.count(cause), ledger)
    }

    /// Whether the run measured anything of the package: it ran (its outcome
    /// is not `could-not-run`) and its coverage is complete.
    fn ran(&self) -> bool {
        self.outcome != UnitOutcome::CouldNotRun && self.coverage_complete
    }
}

/// One side of an axis: a leg of this host, or another host's records.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Side {
    pub(crate) label: String,
    /// Why the side has no records: the leg could not run.
    pub(crate) failure: Option<String>,
    pub(crate) units: BTreeMap<String, UnitFacts>,
    /// The Cargo configuration files above the leg's checkout that Cargo
    /// reads there (`legs::ancestor_cargo_configs`); `None` for another
    /// host's records.
    pub(crate) cargo_configs: Option<Vec<PathBuf>>,
}

/// One obligation whose verdict differs between the sides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct KeyChange {
    pub(crate) key: String,
    /// `None`: the side published no obligation under this key.
    pub(crate) left: Option<Verdict>,
    pub(crate) right: Option<Verdict>,
}

/// What both sides' records of a package state, carried by a verdict that
/// compares nothing, so a reader still sees whether they agreed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Seen {
    pub(crate) profiles: (String, String),
    pub(crate) vectors: (String, String),
    /// Obligation keys in each record.
    pub(crate) keys: (usize, usize),
}

impl Seen {
    fn of(a: &UnitFacts, b: &UnitFacts) -> Self {
        Self {
            profiles: (a.profile.clone(), b.profile.clone()),
            vectors: (a.vector.clone(), b.vector.clone()),
            keys: (a.verdicts.len(), b.verdicts.len()),
        }
    }

    fn agree(&self) -> bool {
        self.profiles.0 == self.profiles.1 && self.vectors.0 == self.vectors.1
    }

    fn label(&self) -> String {
        if self.agree() {
            format!(
                "both records state vector {} under profile {}, over {} and {} key(s)",
                short(&self.vectors.0),
                short(&self.profiles.0),
                self.keys.0,
                self.keys.1
            )
        } else {
            format!(
                "the records differ: vector {} against {}, profile {} against {}, {} against {} \
                 key(s)",
                short(&self.vectors.0),
                short(&self.vectors.1),
                short(&self.profiles.0),
                short(&self.profiles.1),
                self.keys.0,
                self.keys.1
            )
        }
    }

    fn json(&self) -> serde_json::Value {
        serde_json::json!({
            "profiles": [self.profiles.0, self.profiles.1],
            "vectors": [self.vectors.0, self.vectors.1],
            "keys": [self.keys.0, self.keys.1],
            "agree": self.agree(),
        })
    }
}

/// The verdict on one package of one axis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum UnitVerdict {
    /// Both sides measured it, under one profile, to one vector over `keys`
    /// obligation keys.
    Equal { vector: String, profile: String, keys: usize },
    /// Both sides measured it, and the profiles or the vectors differ.
    Differing {
        seen: Seen,
        /// The keys whose verdict moved, by the obligation records (which keep
        /// one row per key: two vectors that differ only in a key published
        /// twice name no key).
        keys: Vec<KeyChange>,
    },
    /// A side's record states a defect (`Standing::NotReproducible`).
    NotReproducible { reason: String, seen: Option<Seen> },
    /// A side has no measurement of it, and no defect.
    CouldNotRun { reason: String, seen: Option<Seen> },
    /// Another host's record of another lane, policy, selection, targo-trust
    /// commit or budget profile, or of a build that names no commit: not this
    /// comparison.
    NotComparable(String),
}

/// An axis's verdict over its packages and its instrument checks, in rising
/// order of what it outranks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AxisVerdict {
    Equal,
    CouldNotRun,
    /// A record states a defect: a solver fault, an unexplained stop.
    NotReproducible,
    /// An instrument check failed: the axis did not run what it names.
    Failed,
    Differing,
    NotComparable,
}

impl AxisVerdict {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            AxisVerdict::Equal => "equal",
            AxisVerdict::CouldNotRun => "could-not-run",
            AxisVerdict::NotReproducible => "not-reproducible",
            AxisVerdict::Failed => "failed",
            AxisVerdict::Differing => "differing",
            AxisVerdict::NotComparable => "not-comparable",
        }
    }
}

/// One axis, judged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AxisResult {
    pub(crate) axis: Axis,
    pub(crate) left: String,
    pub(crate) right: String,
    pub(crate) verdict: AxisVerdict,
    pub(crate) units: Vec<(String, UnitVerdict)>,
    /// What the axis's instrument checks found (failures included).
    pub(crate) notes: Vec<String>,
}

fn path_list(paths: &[PathBuf]) -> String {
    if paths.is_empty() {
        return "none".to_string();
    }
    paths.iter().map(|path| format!("`{}`", path.display())).collect::<Vec<_>>().join(", ")
}

/// Judge `axis` from its two sides. `load` is the loaded leg's `(asked,
/// held)` busy loops, stated in a note.
pub(crate) fn judge_axis(
    axis: Axis,
    left: &Side,
    right: &Side,
    load: Option<(usize, usize)>,
) -> AxisResult {
    let mut notes = Vec::new();
    let mut failed = false;
    if let Some((loops, held)) = load {
        notes.push(format!("load: {held} of {loops} busy loops ran through the loaded leg"));
    }
    if axis == Axis::Host {
        notes.push(
            "the records name no toolchain (their seal is absent until A8): this axis takes the \
             targo-trust commit both records name as the only word that both hosts ran one \
             toolchain"
                .to_string(),
        );
    }
    // Two legs Cargo reads different configuration for (a copy that does not
    // see the `.cargo/config.toml` above the caller's checkout) vary that
    // configuration as well as the axis's condition.
    let confound = match (&left.cargo_configs, &right.cargo_configs) {
        (Some(here), Some(there)) if here != there => Some(format!(
            "the legs read different Cargo configuration above their checkouts ({}: {}; {}: \
             {}), so this axis would also compare that configuration; pass --scratch under the \
             directory that holds it, or run from a copy of the workspace that no configuration \
             above applies to",
            left.label,
            path_list(here),
            right.label,
            path_list(there)
        )),
        _ => None,
    };
    // The packages compared: both sides' for a leg pair; for the host axis,
    // the ones the other host's records name (the caller brought those).
    let packages: BTreeSet<&String> = if axis == Axis::Host {
        right.units.keys().collect()
    } else {
        left.units.keys().chain(right.units.keys()).collect()
    };
    let mut units = Vec::new();
    for package in packages {
        let verdict = match (left.failure.as_ref(), right.failure.as_ref()) {
            (Some(failure), _) => UnitVerdict::CouldNotRun {
                reason: format!("{} could not run: {failure}", left.label),
                seen: None,
            },
            (_, Some(failure)) => UnitVerdict::CouldNotRun {
                reason: format!("{} could not run: {failure}", right.label),
                seen: None,
            },
            (None, None) => compare_units(
                axis,
                (&left.label, left.units.get(package)),
                (&right.label, right.units.get(package)),
                confound.as_deref(),
            ),
        };
        units.push((package.clone(), verdict));
    }
    if units.is_empty() {
        let missing = [left, right]
            .into_iter()
            .map(|side| match &side.failure {
                Some(failure) => format!("{} could not run: {failure}", side.label),
                None => format!("{} wrote {} package record(s)", side.label, side.units.len()),
            })
            .collect::<Vec<_>>()
            .join("; ");
        notes.push(format!("no package to compare: {missing}"));
    }
    match axis {
        Axis::Parallelism if right.failure.is_none() => {
            for (package, unit) in &right.units {
                if unit.worker_threads != 1 {
                    failed = true;
                    notes.push(format!(
                        "FAILED: the serial leg's record of `{package}` states worker_threads {}, \
                         not 1: it is not the run the axis names",
                        unit.worker_threads
                    ));
                }
            }
        }
        Axis::Effort if left.failure.is_none() && !left.units.is_empty() => {
            let (rows, ledger) = left.units.values().fold((0, 0), |(rows, ledger), unit| {
                let (r, l) = unit.stopped_on(StopCause::Effort);
                (rows + r, ledger + l)
            });
            if rows == 0 && ledger == 0 {
                failed = true;
                notes.push(
                    "FAILED: at `[trust] effort = 1` nothing stopped on `effort` (no row, no \
                     ledger count): the count was never exercised, so the axis would pass \
                     vacuously"
                        .to_string(),
                );
            } else {
                notes.push(format!(
                    "effort = 1: {rows} row(s) state `effort`, {ledger} stop(s) counted in the \
                     ledger"
                ));
            }
        }
        _ => {}
    }
    let verdict = units
        .iter()
        .map(|(_, unit)| match unit {
            UnitVerdict::Equal { .. } => AxisVerdict::Equal,
            UnitVerdict::Differing { .. } => AxisVerdict::Differing,
            UnitVerdict::NotReproducible { .. } => AxisVerdict::NotReproducible,
            UnitVerdict::CouldNotRun { .. } => AxisVerdict::CouldNotRun,
            UnitVerdict::NotComparable(_) => AxisVerdict::NotComparable,
        })
        .chain(failed.then_some(AxisVerdict::Failed))
        .chain(units.is_empty().then_some(AxisVerdict::CouldNotRun))
        .max()
        .unwrap_or(AxisVerdict::CouldNotRun);
    AxisResult { axis, left: left.label.clone(), right: right.label.clone(), verdict, units, notes }
}

/// The host axis's like-with-like check: the other host's record must be of
/// this host's lane, policy, selection, targo-trust commit and profile, and
/// both commits must be named.
fn host_mismatch(a: &UnitFacts, b: &UnitFacts) -> Option<String> {
    let mut mismatched: Vec<String> = [
        ("lane", &a.lane, &b.lane),
        ("policy", &a.policy, &b.policy),
        ("selection", &a.selection, &b.selection),
        ("targo-trust commit", &a.targo_trust_commit, &b.targo_trust_commit),
        ("budget profile", &a.profile, &b.profile),
    ]
    .into_iter()
    .filter(|(_, here, there)| here != there)
    .map(|(field, here, there)| format!("{field} `{here}` here, `{there}` there"))
    .collect();
    for (side, commit) in [("here", &a.targo_trust_commit), ("there", &b.targo_trust_commit)] {
        if commit == UNBOUND_COMMIT {
            mismatched.push(format!(
                "targo-trust commit `{UNBOUND_COMMIT}` {side} (a build that embedded no commit, \
                 which no other build can be told apart from)"
            ));
        }
    }
    (!mismatched.is_empty()).then(|| {
        format!(
            "the other host's record is not of this run: {}; compare like with like",
            mismatched.join(", ")
        )
    })
}

/// Compare one package's two records, either of which may be missing.
fn compare_units(
    axis: Axis,
    (left_label, a): (&str, Option<&UnitFacts>),
    (right_label, b): (&str, Option<&UnitFacts>),
    confound: Option<&str>,
) -> UnitVerdict {
    if let (Axis::Host, Some(a), Some(b)) = (axis, a, b) {
        if let Some(mismatch) = host_mismatch(a, b) {
            return UnitVerdict::NotComparable(mismatch);
        }
    }
    let seen = a.zip(b).map(|(a, b)| Seen::of(a, b));
    let mut defects = Vec::new();
    let mut limits = Vec::new();
    for (label, unit) in [(left_label, a), (right_label, b)] {
        match unit.map(UnitFacts::standing) {
            None => limits.push(format!("{label} wrote no record of it")),
            Some(Standing::Measured) => {}
            Some(Standing::NotReproducible(reason)) => defects.push(format!("{label}: {reason}")),
            Some(Standing::CouldNotRun(reason)) => limits.push(format!("{label}: {reason}")),
        }
    }
    if !defects.is_empty() {
        return UnitVerdict::NotReproducible {
            reason: format!("not reproducible ({})", defects.join("; ")),
            seen,
        };
    }
    let (Some(a), Some(b), Some(seen), true) = (a, b, seen.clone(), limits.is_empty()) else {
        return UnitVerdict::CouldNotRun {
            reason: format!("not a measurement ({})", limits.join("; ")),
            seen,
        };
    };
    if let Some(confound) = confound {
        return UnitVerdict::CouldNotRun { reason: confound.to_string(), seen: Some(seen) };
    }
    if seen.agree() {
        return UnitVerdict::Equal {
            vector: a.vector.clone(),
            profile: a.profile.clone(),
            keys: a.verdicts.len(),
        };
    }
    let keys = a
        .verdicts
        .keys()
        .chain(b.verdicts.keys())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter_map(|key| {
            let (left, right) = (a.verdicts.get(key), b.verdicts.get(key));
            (left != right).then(|| KeyChange {
                key: key.clone(),
                left: left.cloned(),
                right: right.cloned(),
            })
        })
        .collect();
    UnitVerdict::Differing { seen, keys }
}

/// The negative control's verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ControlVerdict {
    /// At least one package read not measured with a `wall-backstop` stop.
    Caught,
    /// A package ran and read as a measurement, or none showed the clock.
    Failed(String),
    /// The control leg did not run, or measured no package (none ran to a
    /// complete coverage).
    CouldNotRun(String),
}

/// The negative control, judged: its verdict, and what each package read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ControlResult {
    pub(crate) verdict: ControlVerdict,
    /// `(package, outcome, wall-backstop stops)`.
    pub(crate) units: Vec<(String, String, u64)>,
}

/// Judge the control leg: under `[trust] backstop = 1` every solve runs behind
/// a 5 ms clock, so some package must read not measured, with a
/// `wall-backstop` stop in its rows or its ledger. One such package shows the
/// instrument sees a clock; a package with nothing to solve shows nothing, so
/// it is not required of every package. A control none of whose packages ran
/// (no coverage, a row with no key) cannot show anything either way.
pub(crate) fn judge_control(side: &Side) -> ControlResult {
    if let Some(failure) = &side.failure {
        return ControlResult {
            verdict: ControlVerdict::CouldNotRun(format!("the control could not run: {failure}")),
            units: Vec::new(),
        };
    }
    let units: Vec<(String, String, u64)> = side
        .units
        .values()
        .map(|unit| {
            let (rows, ledger) = unit.stopped_on(StopCause::WallBackstop);
            (unit.package.clone(), unit.outcome.to_string(), rows + ledger)
        })
        .collect();
    let caught = side.units.values().any(|unit| {
        let (rows, ledger) = unit.stopped_on(StopCause::WallBackstop);
        unit.outcome != UnitOutcome::Measured && rows + ledger > 0
    });
    let verdict = if units.is_empty() {
        ControlVerdict::CouldNotRun("the control wrote no package record".to_string())
    } else if caught {
        ControlVerdict::Caught
    } else if !side.units.values().any(UnitFacts::ran) {
        ControlVerdict::CouldNotRun(
            "no package of the control ran to a complete coverage (each is could-not-run, or its \
             coverage is incomplete), so it shows nothing about a clock"
                .to_string(),
        )
    } else {
        ControlVerdict::Failed(
            "no package of the control read not measured with a wall-backstop stop, although \
             every solve ran behind a 5 ms clock: this instrument cannot tell a clock-decided \
             run from a measurement"
                .to_string(),
        )
    };
    ControlResult { verdict, units }
}

/// The verb's exit status: 2 when an `--against` record is not comparable; 1
/// when an axis differs, a record states a defect, an axis's instrument check
/// failed, or the control was not caught; 3 when a leg could not run; 0
/// otherwise.
pub(crate) fn exit_status(control: &ControlResult, axes: &[AxisResult]) -> u8 {
    let worst = axes.iter().map(|axis| axis.verdict).max();
    if worst == Some(AxisVerdict::NotComparable) {
        return EXIT_USAGE;
    }
    if matches!(
        worst,
        Some(AxisVerdict::Differing | AxisVerdict::Failed | AxisVerdict::NotReproducible)
    ) || matches!(control.verdict, ControlVerdict::Failed(_))
    {
        return EXIT_DIFFERING;
    }
    if worst == Some(AxisVerdict::CouldNotRun)
        || matches!(control.verdict, ControlVerdict::CouldNotRun(_))
    {
        return EXIT_COULD_NOT_RUN;
    }
    EXIT_EQUAL
}

/// How many differing keys the terminal names per package (JSON names all).
const SHOWN_KEYS: usize = 20;

fn short(digest: &str) -> String {
    short_id(digest).to_string()
}

/// Append one line of the terminal report, escaped: record contents (package
/// names, keys, stops), another host's record and paths reach it, and none
/// may move the cursor or start a new line.
fn line(out: &mut String, text: impl AsRef<str>) {
    out.push_str(&crate::escape_terminal_controls(text.as_ref()));
    out.push('\n');
}

fn equal_label(vector: &str, profile: &str, keys: usize) -> String {
    if keys == 0 {
        format!(
            "equal, vacuously: no obligation key in either record (vector {}, profile {})",
            short(vector),
            short(profile)
        )
    } else {
        format!(
            "equal over {keys} obligation key(s) (vector {}, profile {})",
            short(vector),
            short(profile)
        )
    }
}

impl Report {
    /// The human report.
    pub(crate) fn render_terminal(&self) -> String {
        let mut out = String::new();
        let legs: Vec<&str> = self.legs.iter().map(|run| run.leg.label()).collect();
        line(&mut out, format!("Stability: {} leg(s): {}", legs.len(), legs.join(", ")));
        let copy = &self.copy;
        if copy.is_self_contained() {
            line(&mut out, format!("  copies carry the workspace root `{}`", copy.root.display()));
        } else {
            // The workspace is one of the trees, or inside one (a package
            // directory at or above it that the closure reads).
            let holder = copy.trees.iter().find(|tree| copy.workspace.starts_with(tree));
            let place = match holder {
                Some(tree) if *tree != copy.workspace => {
                    let tree = if tree.as_os_str().is_empty() { Path::new(".") } else { tree };
                    format!(
                        "the workspace at `{}`, inside the package directory `{}`",
                        copy.workspace.display(),
                        tree.display()
                    )
                }
                _ => format!("the workspace at `{}`", copy.workspace.display()),
            };
            let outside = copy.trees.iter().filter(|tree| Some(*tree) != holder).count();
            line(
                &mut out,
                format!(
                    "  copies carry `{}`'s path closure: {place}, {outside} package director{} \
                     outside it and {} file(s) on the way to them",
                    copy.root.display(),
                    if outside == 1 { "y" } else { "ies" },
                    copy.files.len()
                ),
            );
        }
        for run in &self.legs {
            let state = match (&run.side.failure, run.exit) {
                (Some(failure), _) => format!("COULD NOT RUN: {failure}"),
                (None, Some(code)) => format!("exit {code}, {} package(s)", run.side.units.len()),
                (None, None) => "no exit status".to_string(),
            };
            line(&mut out, format!("  leg {} ({}): {state}", run.leg.label(), run.cwd.display()));
            for unit in run.side.units.values() {
                line(
                    &mut out,
                    format!(
                        "    {}: {}, vector {}, {} key(s), stops {}",
                        unit.package,
                        unit.outcome,
                        short(&unit.vector),
                        unit.verdicts.len(),
                        unit.stop_causes.render()
                    ),
                );
            }
            if let Some(tail) = &run.stderr_tail {
                for tail_line in tail.lines() {
                    line(&mut out, format!("    | {tail_line}"));
                }
            }
        }
        let control = match &self.control.verdict {
            ControlVerdict::Caught => "CAUGHT".to_string(),
            ControlVerdict::Failed(reason) => format!("FAILED: {reason}"),
            ControlVerdict::CouldNotRun(reason) => format!("COULD NOT RUN: {reason}"),
        };
        line(&mut out, format!("Negative control ([trust] backstop = 1): {control}"));
        for (package, outcome, stops) in &self.control.units {
            line(&mut out, format!("  {package}: {outcome}, {stops} wall-backstop stop(s)"));
        }
        for axis in &self.axes {
            line(
                &mut out,
                format!(
                    "Axis {} ({} / {}): {}",
                    axis.axis.name(),
                    axis.left,
                    axis.right,
                    axis.verdict.as_str().to_uppercase()
                ),
            );
            for note in &axis.notes {
                line(&mut out, format!("  {note}"));
            }
            for (package, unit) in &axis.units {
                render_unit(&mut out, axis, package, unit);
            }
        }
        let count =
            |verdict: AxisVerdict| self.axes.iter().filter(|axis| axis.verdict == verdict).count();
        let not_comparable = count(AxisVerdict::NotComparable);
        line(
            &mut out,
            format!(
                "Result: exit {} — axes: {} equal, {} differing, {} not reproducible, {} failed, \
                 {} could not run{}",
                self.exit,
                count(AxisVerdict::Equal),
                count(AxisVerdict::Differing),
                count(AxisVerdict::NotReproducible),
                count(AxisVerdict::Failed),
                count(AxisVerdict::CouldNotRun),
                if not_comparable > 0 {
                    format!(", {not_comparable} not comparable")
                } else {
                    String::new()
                }
            ),
        );
        out
    }

    /// The `trust.stability.v1` JSON report.
    pub(crate) fn render_json(&self) -> serde_json::Value {
        let legs: Vec<serde_json::Value> = self
            .legs
            .iter()
            .map(|run| {
                serde_json::json!({
                    "leg": run.leg.label(),
                    "cwd": run.cwd.display().to_string(),
                    "exit": run.exit,
                    "could_not_run": run.side.failure,
                    "packages": run.side.units.values().map(|unit| serde_json::json!({
                        "package": unit.package,
                        "outcome": unit.outcome.as_str(),
                        "vector": unit.vector,
                        "profile": unit.profile,
                        "keys": unit.verdicts.len(),
                        "coverage_complete": unit.coverage_complete,
                        "stop_causes": unit.stop_causes,
                        "noted_stops": unit.noted_stops,
                    })).collect::<Vec<_>>(),
                    "cargo_configs": run.side.cargo_configs.as_ref().map(|configs| {
                        configs.iter().map(|path| path.display().to_string()).collect::<Vec<_>>()
                    }),
                    "load": run.load.map(|(loops, held)| serde_json::json!({
                        "busy_loops": loops,
                        "held": held,
                    })),
                    "stderr_tail": run.stderr_tail,
                    "seconds": run.seconds,
                })
            })
            .collect();
        let (control_verdict, control_reason) = match &self.control.verdict {
            ControlVerdict::Caught => ("caught", None),
            ControlVerdict::Failed(reason) => ("failed", Some(reason)),
            ControlVerdict::CouldNotRun(reason) => ("could-not-run", Some(reason)),
        };
        let axes: Vec<serde_json::Value> = self
            .axes
            .iter()
            .map(|axis| {
                let units: Vec<serde_json::Value> =
                    axis.units.iter().map(|(package, unit)| unit_json(package, unit)).collect();
                serde_json::json!({
                    "axis": axis.axis.name(),
                    "legs": [axis.left, axis.right],
                    "verdict": axis.verdict.as_str(),
                    "notes": axis.notes,
                    "units": units,
                })
            })
            .collect();
        let paths = |paths: &[PathBuf]| {
            paths.iter().map(|path| path.display().to_string()).collect::<Vec<_>>()
        };
        serde_json::json!({
            "schema": STABILITY_SCHEMA,
            "exit": self.exit,
            "scratch": self.scratch.as_ref().map(|scratch| scratch.display().to_string()),
            "copy": {
                "root": self.copy.root.display().to_string(),
                "workspace": self.copy.workspace.display().to_string(),
                "trees": paths(&self.copy.trees),
                "files": paths(&self.copy.files),
            },
            "legs": legs,
            "control": {
                "verdict": control_verdict,
                "reason": control_reason,
                "units": self.control.units.iter().map(|(package, outcome, stops)| {
                    serde_json::json!({
                        "package": package,
                        "outcome": outcome,
                        "wall_backstop_stops": stops,
                    })
                }).collect::<Vec<_>>(),
            },
            "axes": axes,
        })
    }
}

fn render_unit(out: &mut String, axis: &AxisResult, package: &str, unit: &UnitVerdict) {
    match unit {
        UnitVerdict::Equal { vector, profile, keys } => {
            line(out, format!("  {package}: {}", equal_label(vector, profile, *keys)));
        }
        UnitVerdict::Differing { seen, keys } => {
            let mut what = Vec::new();
            if seen.profiles.0 != seen.profiles.1 {
                what.push(format!(
                    "profile {} against {}",
                    short(&seen.profiles.0),
                    short(&seen.profiles.1)
                ));
            }
            if seen.vectors.0 != seen.vectors.1 {
                what.push(format!(
                    "vector {} against {}",
                    short(&seen.vectors.0),
                    short(&seen.vectors.1)
                ));
            }
            line(
                out,
                format!(
                    "  {package}: DIFFERING: {}; {} of {} and {} obligation key(s) differ",
                    what.join(", "),
                    keys.len(),
                    seen.keys.0,
                    seen.keys.1
                ),
            );
            if keys.is_empty() {
                line(
                    out,
                    "    (no key's recorded verdict differs: the vectors differ in a key published \
                     more than once, whose record keeps its worst row)",
                );
            }
            for change in keys.iter().take(SHOWN_KEYS) {
                let side = |verdict: &Option<Verdict>| {
                    verdict.as_ref().map_or("absent".to_string(), Verdict::label)
                };
                line(
                    out,
                    format!(
                        "    {}: {} {}, {} {}",
                        change.key,
                        axis.left,
                        side(&change.left),
                        axis.right,
                        side(&change.right)
                    ),
                );
            }
            if keys.len() > SHOWN_KEYS {
                line(
                    out,
                    format!(
                        "    … {} more (--format json names every one)",
                        keys.len() - SHOWN_KEYS
                    ),
                );
            }
        }
        UnitVerdict::NotReproducible { reason, seen } => {
            line(out, format!("  {package}: NOT REPRODUCIBLE: {reason}"));
            if let Some(seen) = seen {
                line(out, format!("    {}", seen.label()));
            }
        }
        UnitVerdict::CouldNotRun { reason, seen } => {
            line(out, format!("  {package}: could not run: {reason}"));
            if let Some(seen) = seen {
                line(out, format!("    {}", seen.label()));
            }
        }
        UnitVerdict::NotComparable(reason) => {
            line(out, format!("  {package}: NOT COMPARABLE: {reason}"));
        }
    }
}

fn unit_json(package: &str, unit: &UnitVerdict) -> serde_json::Value {
    match unit {
        UnitVerdict::Equal { vector, profile, keys } => serde_json::json!({
            "package": package,
            "verdict": "equal",
            "vector": vector,
            "profile": profile,
            "keys": keys,
        }),
        UnitVerdict::Differing { seen, keys } => serde_json::json!({
            "package": package,
            "verdict": "differing",
            "profiles": [seen.profiles.0, seen.profiles.1],
            "vectors": [seen.vectors.0, seen.vectors.1],
            "keys": [seen.keys.0, seen.keys.1],
            "differing_keys": keys.iter().map(|change| serde_json::json!({
                "key": change.key,
                "left": change.left.as_ref().map(Verdict::json),
                "right": change.right.as_ref().map(Verdict::json),
            })).collect::<Vec<_>>(),
        }),
        UnitVerdict::NotReproducible { reason, seen } => serde_json::json!({
            "package": package,
            "verdict": "not-reproducible",
            "reason": reason,
            "seen": seen.as_ref().map(Seen::json),
        }),
        UnitVerdict::CouldNotRun { reason, seen } => serde_json::json!({
            "package": package,
            "verdict": "could-not-run",
            "reason": reason,
            "seen": seen.as_ref().map(Seen::json),
        }),
        UnitVerdict::NotComparable(reason) => serde_json::json!({
            "package": package,
            "verdict": "not-comparable",
            "reason": reason,
        }),
    }
}
