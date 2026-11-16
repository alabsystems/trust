// targo-trust/baseline.rs: the committed obligation baseline, `trust-baseline
// v1`, and the comparison `targo trust diff --baseline` gates on (work item T9).
//
// FORMAT. Text, LF line endings, bytewise-sorted, written by temp file and
// rename:
//
//   trust-baseline v1
//   lane <gate lane>
//   policy <compiler policy>
//   selection <canonical selection>
//   targo_trust_commit <commit | unbound>
//   profile <budget profile id>
//   package <name>
//   fn\t<def path>\t<source16 | ->\t<id16> <id16> …
//   …
//
// Only PROVED obligations are listed, grouped by function, with the first
// sixteen hex digits of the function's source digest (`-` when the compiler
// did not state one). That is the smallest file that decides "a proof was
// lost": a key is a function-local content address
// (`trust_types::obligation_identity`), so the file moves only where proofs or
// the code under them moved, and its git diff is the review.
//
// COMPARISON ([`compare`]). Each baseline function is first PAIRED with a
// function of the run ([`pair_functions`]): by source digest when exactly one
// baseline function and exactly one current function carry it (so a closure
// renumbered by a closure inserted before it, `f::{closure#0}` becoming
// `f::{closure#1}`, is still compared with itself); otherwise by def path;
// otherwise, for a function renamed and edited at once, by its proved local
// ids (a strict majority of them in exactly one unpaired function). A
// function the run verified but published no obligation for (every row elided
// as inventory) is present, with no keys. Then:
//   * a baseline key present now but not proved is LOST — when what stopped
//     the search is reproducible; a clock, an RSS reading, a crash or an
//     unexplained stop is NOT MEASURED instead, because it decides nothing;
//   * a baseline key absent now, in a function whose source digest is the
//     same (or not stated on either side), is LOST — losing EVERY key of an
//     unchanged function included;
//   * a baseline key absent now, in a function whose source changed, is
//     accepted and named (VANISHED): the obligation's code was edited;
//   * a baseline function left unpaired is gone from what the compiler
//     verified: accepted and named (REMOVED);
//   * proved keys absent from the baseline are GAINED; unproved keys in new or
//     edited functions are NEW, each named — and a NEW key that is REFUTED
//     (`failed`, a counterexample) fails the diff, because a counterexample is
//     not a missing proof.
//
// Exit status: 0 nothing lost, 1 a proof was lost or new code is refuted, 2
// usage, format, or a lane, policy or selection that differs from the
// baseline's, 3 nothing lost but the run is not a measurement (a selected
// package not measured, a key stopped by a non-reproducible cause, a def path
// published with two source digests, a row with no key; each named).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::{fmt, io};

use trust_types::determinism::UnitOutcome;
use trust_types::obligation_identity::{is_local_id, obligation_key};

use crate::obligations::{
    FunctionRecords, ObligationRecord, ObligationRecords, PackageRecords, RunFacts, RunScope,
};

/// The first line of every baseline.
pub(crate) const BASELINE_MAGIC: &str = "trust-baseline v1";

/// The exit status of a refused or failed comparison.
pub(crate) const EXIT_LOST: u8 = 1;
pub(crate) const EXIT_USAGE: u8 = 2;
pub(crate) const EXIT_NOT_MEASURED: u8 = crate::determinism_report::EXIT_COULD_NOT_RUN;

/// One function of a baseline: its source digest prefix and proved ids.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct BaselineFunction {
    /// The first sixteen hex digits of the function source digest.
    pub(crate) source: Option<String>,
    /// The proved local ids.
    pub(crate) proved: BTreeSet<String>,
}

/// A parsed baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Baseline {
    pub(crate) lane: String,
    pub(crate) policy: String,
    pub(crate) selection: String,
    /// The Trust commit the measuring targo-trust was built from
    /// (`RunFacts::targo_trust_commit`): not the seal's identity, which no
    /// baseline states until A8.
    pub(crate) targo_trust_commit: String,
    pub(crate) profile: String,
    /// Packages by name, functions by def path.
    pub(crate) packages: BTreeMap<String, BTreeMap<String, BaselineFunction>>,
}

/// Why a baseline could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FormatError {
    pub(crate) line: usize,
    pub(crate) reason: String,
}

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.reason)
    }
}

fn source16(source: Option<&str>) -> Option<String> {
    source.and_then(|digest| digest.get(..16)).map(str::to_string)
}

impl Baseline {
    /// The proved keys of `records`, for the packages in `records`.
    pub(crate) fn project(records: &ObligationRecords) -> Self {
        let packages = records
            .packages
            .iter()
            .map(|(package, functions)| {
                let functions = functions
                    .iter()
                    .filter_map(|(def_path, function)| {
                        let proved: BTreeSet<String> = function
                            .obligations
                            .iter()
                            .filter(|(_, record)| record.is_proved())
                            .map(|(id, _)| id.clone())
                            .collect();
                        (!proved.is_empty()).then(|| {
                            (
                                def_path.clone(),
                                BaselineFunction {
                                    source: source16(function.source.as_deref()),
                                    proved,
                                },
                            )
                        })
                    })
                    .collect();
                (package.clone(), functions)
            })
            .collect();
        Self {
            lane: records.facts.lane.clone(),
            policy: records.facts.policy.clone(),
            selection: records.facts.selection.clone(),
            targo_trust_commit: records.facts.targo_trust_commit.clone(),
            profile: records.facts.profile.clone(),
            packages,
        }
    }

    /// The canonical bytes. Two baselines of the same proofs render identically.
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(BASELINE_MAGIC);
        out.push('\n');
        for (name, value) in [
            ("lane", &self.lane),
            ("policy", &self.policy),
            ("selection", &self.selection),
            ("targo_trust_commit", &self.targo_trust_commit),
            ("profile", &self.profile),
        ] {
            out.push_str(&format!("{name} {value}\n"));
        }
        for (package, functions) in &self.packages {
            out.push_str(&format!("package {package}\n"));
            for (def_path, function) in functions {
                let ids: Vec<&str> = function.proved.iter().map(String::as_str).collect();
                out.push_str(&format!(
                    "fn\t{def_path}\t{}\t{}\n",
                    function.source.as_deref().unwrap_or("-"),
                    ids.join(" ")
                ));
            }
        }
        out
    }

    /// Parse the canonical bytes. Anything else — another version, a reordered
    /// or duplicated line, a malformed id — is refused: a baseline is read
    /// exactly as it was written, never repaired.
    pub(crate) fn parse(text: &str) -> Result<Self, FormatError> {
        let error = |line: usize, reason: &str| FormatError { line, reason: reason.to_string() };
        if text.contains('\r') {
            return Err(error(1, "a baseline has LF line endings only"));
        }
        let Some(body) = text.strip_suffix('\n') else {
            return Err(error(text.lines().count(), "a baseline ends with a line break"));
        };
        let mut lines = body.split('\n').enumerate().map(|(index, line)| (index + 1, line));
        let (_, magic) = lines.next().ok_or_else(|| error(1, "empty file"))?;
        if magic != BASELINE_MAGIC {
            return Err(error(1, "not a `trust-baseline v1` file"));
        }
        let mut header = |expected: &str| -> Result<String, FormatError> {
            let (line, text) = lines.next().ok_or_else(|| error(0, "truncated header"))?;
            text.strip_prefix(expected)
                .and_then(|rest| rest.strip_prefix(' '))
                .filter(|value| !value.is_empty())
                .map(str::to_string)
                .ok_or_else(|| error(line, &format!("expected the `{expected}` header line")))
        };
        let lane = header("lane")?;
        let policy = header("policy")?;
        let selection = header("selection")?;
        let targo_trust_commit = header("targo_trust_commit")?;
        let profile = header("profile")?;
        let mut packages: BTreeMap<String, BTreeMap<String, BaselineFunction>> = BTreeMap::new();
        let mut current: Option<String> = None;
        let mut previous_fn: Option<String> = None;
        for (line, text) in lines {
            if text.is_empty() {
                return Err(error(line, "a baseline has no empty lines"));
            }
            if let Some(package) = text.strip_prefix("package ") {
                if package.is_empty() || current.as_deref().is_some_and(|p| p >= package) {
                    return Err(error(line, "packages are listed once each, in byte order"));
                }
                packages.insert(package.to_string(), BTreeMap::new());
                current = Some(package.to_string());
                previous_fn = None;
                continue;
            }
            let Some(package) = current.as_ref() else {
                return Err(error(line, "a `fn` line before any `package` line"));
            };
            let fields: Vec<&str> = text.split('\t').collect();
            let [tag, def_path, source, ids] = fields.as_slice() else {
                return Err(error(line, "a `fn` line has four tab-separated fields"));
            };
            if *tag != "fn" || def_path.is_empty() {
                return Err(error(line, "expected `fn\\t<def path>\\t<source>\\t<ids>`"));
            }
            if previous_fn.as_deref().is_some_and(|p| p >= *def_path) {
                return Err(error(line, "functions are listed once each, in byte order"));
            }
            previous_fn = Some((*def_path).to_string());
            let source = match *source {
                "-" => None,
                digest if is_local_id(digest) => Some(digest.to_string()),
                _ => return Err(error(line, "a source digest is 16 lowercase hex digits or `-`")),
            };
            let proved: Vec<&str> = ids.split(' ').collect();
            if proved.iter().any(|id| !is_local_id(id))
                || proved.windows(2).any(|pair| pair[0] >= pair[1])
            {
                return Err(error(line, "proved ids are distinct 16-hex ids in byte order"));
            }
            packages.get_mut(package).expect("current package is present").insert(
                (*def_path).to_string(),
                BaselineFunction {
                    source,
                    proved: proved.into_iter().map(str::to_string).collect(),
                },
            );
        }
        Ok(Self { lane, policy, selection, targo_trust_commit, profile, packages })
    }

    /// The proved keys, `<def path>#<id>`, of one package.
    fn proved_keys(&self, package: &str) -> BTreeSet<String> {
        self.packages
            .get(package)
            .into_iter()
            .flat_map(|functions| {
                functions.iter().flat_map(|(def_path, function)| {
                    function.proved.iter().map(move |id| obligation_key(def_path, id))
                })
            })
            .collect()
    }
}

/// Why two baselines cannot be merged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MergeRefusal(pub(crate) String);

/// Whether `a` and `b` were measured alike: lane, policy and selection.
fn same_measurement(a: &Baseline, b: &Baseline) -> bool {
    a.lane == b.lane && a.policy == b.policy && a.selection == b.selection
}

/// The result of a merge: the next baseline, and each package the existing
/// file held that the merge dropped, with why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Merged {
    pub(crate) baseline: Baseline,
    pub(crate) dropped: Vec<(String, &'static str)>,
}

/// `run`'s packages replace `existing`'s. Of the packages the run did NOT
/// select, those the workspace's resolve still has are kept verbatim and the
/// others — deleted, or no longer depended on — are dropped; a package the run
/// selected but has no record of is dropped too (it holds no proof now). The two must agree on
/// lane, policy and selection — and on targo-trust commit and profile too,
/// unless nothing is kept: one header states one measurement, so a file is
/// never half one build's and half another's.
pub(crate) fn merge(
    existing: &Baseline,
    run: &Baseline,
    scope: &RunScope,
) -> Result<Merged, MergeRefusal> {
    if !same_measurement(existing, run) {
        return Err(MergeRefusal(format!(
            "the baseline was measured on lane `{}` (policy `{}`) with selection `{}`, this run \
             on lane `{}` (policy `{}`) with selection `{}`; remove the file to start a baseline \
             for this lane",
            existing.lane, existing.policy, existing.selection, run.lane, run.policy, run.selection
        )));
    }
    let mut kept: Vec<&String> = Vec::new();
    let mut dropped = Vec::new();
    for package in existing.packages.keys() {
        if run.packages.contains_key(package) {
            continue;
        }
        if scope.selected.contains(package) {
            dropped.push((package.clone(), "selected, and the run holds no proof of it"));
        } else if !scope.resolved.is_empty() && !scope.resolved.contains(package) {
            dropped.push((package.clone(), "no longer in the workspace's resolve"));
        } else {
            kept.push(package);
        }
    }
    if !kept.is_empty()
        && (existing.targo_trust_commit != run.targo_trust_commit
            || existing.profile != run.profile)
    {
        return Err(MergeRefusal(format!(
            "the baseline's targo-trust commit `{}` and profile `{}` differ from this run's \
             (`{}`, `{}`), and this run did not re-measure {} of its package(s) ({}); select \
             every package to re-base the whole file",
            existing.targo_trust_commit,
            existing.profile,
            run.targo_trust_commit,
            run.profile,
            kept.len(),
            kept.iter().map(|p| p.as_str()).collect::<Vec<_>>().join(", ")
        )));
    }
    let mut baseline = run.clone();
    for package in kept {
        baseline.packages.insert(package.clone(), existing.packages[package].clone());
    }
    Ok(Merged { baseline, dropped })
}

/// Why a key was lost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum LostReason {
    /// The key is present now and not proved.
    NotProved,
    /// The key vanished from a function whose source did not change.
    VanishedFromUnchangedSource,
}

/// One lost proof.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Lost {
    pub(crate) package: String,
    /// The baseline's def path.
    pub(crate) function: String,
    pub(crate) id: String,
    pub(crate) reason: LostReason,
    /// The current record, when the key is present now (possibly under a
    /// moved function's def path).
    pub(crate) now: Option<ObligationRecord>,
}

impl Lost {
    /// `package fn #id kind status stop file:line:col`.
    pub(crate) fn line(&self) -> String {
        match &self.now {
            Some(now) => format!(
                "{} {} #{} {} {} {} {}",
                self.package,
                self.function,
                self.id,
                now.kind,
                now.status,
                now.stop,
                now.location_label()
            ),
            None => format!(
                "{} {} #{} - vanished - - (the function's source did not change)",
                self.package, self.function, self.id
            ),
        }
    }
}

/// How a baseline function was paired with a current one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PairedBy {
    /// Exactly one baseline function and one current function carry the
    /// source digest.
    Source,
    /// The same def path.
    Path,
    /// A strict majority of the baseline function's proved local ids, found in
    /// exactly one unpaired current function (a rename with an edit).
    Ids,
}

impl PairedBy {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Source => "source",
            Self::Path => "path",
            Self::Ids => "ids",
        }
    }
}

/// Pair each baseline function with at most one current function, and each
/// current function with at most one baseline function: `base path -> (current
/// path, how)`. See the module header for the order of the rules.
pub(crate) fn pair_functions<'a>(
    base: &'a BTreeMap<String, BaselineFunction>,
    now: &'a PackageRecords,
) -> BTreeMap<&'a str, (&'a str, PairedBy)> {
    let mut paired: BTreeMap<&str, (&str, PairedBy)> = BTreeMap::new();
    let mut used: BTreeSet<&str> = BTreeSet::new();
    // 1. A source digest exactly one function on each side carries.
    let mut base_by_source: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (path, function) in base {
        if let Some(source) = function.source.as_deref() {
            base_by_source.entry(source).or_default().push(path);
        }
    }
    let mut now_by_source: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for (path, function) in now {
        if let Some(source) = source16(function.source.as_deref()) {
            now_by_source.entry(source).or_default().push(path);
        }
    }
    for (source, base_paths) in &base_by_source {
        if let ([base_path], Some([now_path])) =
            (base_paths.as_slice(), now_by_source.get(*source).map(Vec::as_slice))
        {
            paired.insert(base_path, (now_path, PairedBy::Source));
            used.insert(now_path);
        }
    }
    // 2. The same def path.
    for path in base.keys() {
        if !paired.contains_key(path.as_str())
            && now.contains_key(path)
            && used.insert(path.as_str())
        {
            paired.insert(path, (path, PairedBy::Path));
        }
    }
    // 3. The proved ids, for a function renamed and edited at once.
    let mut candidates: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (path, function) in base {
        if paired.contains_key(path.as_str()) || function.proved.is_empty() {
            continue;
        }
        for (now_path, now_function) in now {
            if used.contains(now_path.as_str()) {
                continue;
            }
            let overlap = function
                .proved
                .iter()
                .filter(|id| now_function.obligations.contains_key(*id))
                .count();
            if overlap * 2 > function.proved.len() {
                candidates.entry(path).or_default().push(now_path);
            }
        }
    }
    let mut claims: BTreeMap<&str, usize> = BTreeMap::new();
    for targets in candidates.values() {
        for target in targets {
            *claims.entry(target).or_default() += 1;
        }
    }
    for (path, targets) in &candidates {
        if let [target] = targets.as_slice() {
            if claims[target] == 1 {
                paired.insert(path, (target, PairedBy::Ids));
            }
        }
    }
    paired
}

/// The comparison of a baseline with a run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Comparison {
    pub(crate) lost: Vec<Lost>,
    /// Proved now, not proved in the baseline: `(package, record)`.
    pub(crate) gained: Vec<(String, ObligationRecord)>,
    /// Not proved now, in a function the baseline does not hold or whose
    /// source changed since: new or edited code, accepted and named — unless
    /// refuted ([`Comparison::new_failed`]).
    pub(crate) new_unproved: Vec<(String, ObligationRecord)>,
    /// Refuted now (`failed`), in a function whose source did not change, on a
    /// key the baseline did not hold proved: named, not a loss.
    pub(crate) failed_unchanged: Vec<(String, ObligationRecord)>,
    /// Baseline keys present now and not proved, but stopped by a cause that
    /// is not reproducible: not a measurement of that key.
    pub(crate) unmeasured_keys: Vec<(String, ObligationRecord)>,
    /// Baseline keys that vanished with an edit of their function:
    /// `(package, key)`.
    pub(crate) vanished_with_edit: Vec<(String, String)>,
    /// Baseline functions no current function was paired with.
    pub(crate) removed_functions: Vec<(String, String)>,
    /// Baseline functions paired with a current function under another def
    /// path: `(package, from, to, how)`.
    pub(crate) moved_functions: Vec<(String, String, String, PairedBy)>,
    /// Baseline packages the run did not measure at all.
    pub(crate) unmeasured_packages: Vec<String>,
}

impl Comparison {
    /// The new or edited code the run refuted.
    pub(crate) fn new_failed(&self) -> impl Iterator<Item = &(String, ObligationRecord)> {
        self.new_unproved.iter().filter(|(_, record)| record.is_failed())
    }
}

/// Compare `baseline` with `records`, over `packages` (every baseline package
/// when `None`).
pub(crate) fn compare(
    baseline: &Baseline,
    records: &ObligationRecords,
    packages: Option<&BTreeSet<String>>,
) -> Comparison {
    let mut comparison = Comparison::default();
    let in_scope = |package: &String| packages.is_none_or(|set| set.contains(package));
    for (package, base_functions) in baseline.packages.iter().filter(|(p, _)| in_scope(p)) {
        let Some(now_functions) = records.packages.get(package) else {
            comparison.unmeasured_packages.push(package.clone());
            continue;
        };
        let paired = pair_functions(base_functions, now_functions);
        // The baseline function each current function was paired with.
        let mut paired_now: BTreeMap<&str, (&BaselineFunction, bool)> = BTreeMap::new();
        for (def_path, base) in base_functions {
            let Some(&(now_path, how)) = paired.get(def_path.as_str()) else {
                comparison.removed_functions.push((package.clone(), def_path.clone()));
                continue;
            };
            let now = &now_functions[now_path];
            if now_path != def_path {
                comparison.moved_functions.push((
                    package.clone(),
                    def_path.clone(),
                    now_path.to_string(),
                    how,
                ));
            }
            let source_changed = match (&base.source, source16(now.source.as_deref())) {
                (Some(before), Some(after)) => *before != after,
                _ => false,
            };
            paired_now.insert(now_path, (base, source_changed));
            compare_function(&mut comparison, package, def_path, base, now, source_changed);
        }
        // Gains and new unproved obligations, against the baseline function
        // each current function was paired with (or none).
        for (now_path, now) in now_functions {
            let held = paired_now.get(now_path.as_str()).copied();
            for (id, record) in &now.obligations {
                if held.is_some_and(|(base, _)| base.proved.contains(id)) {
                    continue;
                }
                if record.is_proved() {
                    comparison.gained.push((package.clone(), record.clone()));
                } else if held.is_none_or(|(_, source_changed)| source_changed) {
                    // New code, or code edited since the baseline.
                    comparison.new_unproved.push((package.clone(), record.clone()));
                } else if record.is_failed() {
                    // The baseline lists proved keys alone, so an unproved key
                    // of an unchanged held function was unproved then too; a
                    // refutation of one is still named.
                    comparison.failed_unchanged.push((package.clone(), record.clone()));
                }
            }
        }
    }
    // Packages measured now that the baseline does not hold: entirely new code.
    for (package, functions) in records.packages.iter().filter(|(p, _)| in_scope(p)) {
        if baseline.packages.contains_key(package) {
            continue;
        }
        for record in functions.values().flat_map(|function| function.obligations.values()) {
            if record.is_proved() {
                comparison.gained.push((package.clone(), record.clone()));
            } else {
                comparison.new_unproved.push((package.clone(), record.clone()));
            }
        }
    }
    comparison.lost.sort();
    comparison.gained.sort();
    comparison.new_unproved.sort();
    comparison.failed_unchanged.sort();
    comparison.unmeasured_keys.sort();
    comparison.vanished_with_edit.sort();
    comparison.removed_functions.sort();
    comparison.moved_functions.sort();
    comparison
}

/// Compare one baseline function's proved keys with the current function it
/// was paired with.
fn compare_function(
    comparison: &mut Comparison,
    package: &str,
    def_path: &str,
    base: &BaselineFunction,
    now: &FunctionRecords,
    source_changed: bool,
) {
    for id in &base.proved {
        match now.obligations.get(id) {
            Some(record) if record.is_proved() => {}
            Some(record) if !record.stop_is_reproducible() => {
                comparison.unmeasured_keys.push((package.to_string(), record.clone()));
            }
            Some(record) => comparison.lost.push(Lost {
                package: package.to_string(),
                function: def_path.to_string(),
                id: id.clone(),
                reason: LostReason::NotProved,
                now: Some(record.clone()),
            }),
            None if source_changed => {
                comparison
                    .vanished_with_edit
                    .push((package.to_string(), obligation_key(def_path, id)));
            }
            None => comparison.lost.push(Lost {
                package: package.to_string(),
                function: def_path.to_string(),
                id: id.clone(),
                reason: LostReason::VanishedFromUnchangedSource,
                now: None,
            }),
        }
    }
}

/// The exit status of a comparison of `records` against a baseline: a LOST
/// proof or refuted new code wins, then a run that is not a measurement.
pub(crate) fn exit_status(comparison: &Comparison, records: &ObligationRecords) -> u8 {
    if !comparison.lost.is_empty() || comparison.new_failed().next().is_some() {
        return EXIT_LOST;
    }
    if records.facts.outcome != UnitOutcome::Measured
        || !records.facts.coverage_complete
        || !records.unkeyed_functions.is_empty()
        || !records.conflicting_functions.is_empty()
        || !comparison.unmeasured_packages.is_empty()
        || !comparison.unmeasured_keys.is_empty()
    {
        return EXIT_NOT_MEASURED;
    }
    0
}

/// Whether a baseline may be saved from `records`: only a measurement.
pub(crate) fn save_refusal(records: &ObligationRecords) -> Option<String> {
    if records.facts.outcome != UnitOutcome::Measured {
        return Some(format!(
            "this run is `{}`, not a measurement; a baseline is saved only from a measured run",
            records.facts.outcome
        ));
    }
    if !records.facts.coverage_complete {
        return Some(
            "the compiler's coverage accounting is incomplete: not every eligible function was \
             verified"
                .to_string(),
        );
    }
    if !records.unkeyed_functions.is_empty() {
        return Some(format!(
            "{} function(s) published obligations with no stable key: {}",
            records.unkeyed_functions.len(),
            records.unkeyed_functions.join(", ")
        ));
    }
    if !records.conflicting_functions.is_empty() {
        return Some(format!(
            "{} def path(s) were published with two different source digests (two units \
             compiled different functions under one path, so their keys cannot be told apart): \
             {}",
            records.conflicting_functions.len(),
            records.conflicting_functions.join(", ")
        ));
    }
    None
}

/// Lane, policy and selection must agree with the baseline's.
pub(crate) fn lane_mismatch(baseline: &Baseline, facts: &RunFacts) -> Option<String> {
    (baseline.lane != facts.lane
        || baseline.policy != facts.policy
        || baseline.selection != facts.selection)
        .then(|| {
            format!(
                "the baseline was measured on lane `{}` (policy `{}`) with selection `{}`, this \
                 run on lane `{}` (policy `{}`) with selection `{}`",
                baseline.lane,
                baseline.policy,
                baseline.selection,
                facts.lane,
                facts.policy,
                facts.selection
            )
        })
}

fn record_line(package: &str, record: &ObligationRecord) -> String {
    format!(
        "{package} {} {} {} {} {}",
        record.key,
        record.kind,
        record.status,
        record.stop,
        record.location_label()
    )
}

/// Human-readable report of a comparison: every key and function it decided
/// anything about, by name, then the counts.
pub(crate) fn render_terminal(
    comparison: &Comparison,
    baseline: &Baseline,
    records: &ObligationRecords,
) -> String {
    let facts = &records.facts;
    let mut out = String::new();
    if baseline.targo_trust_commit != facts.targo_trust_commit {
        out.push_str(&format!(
            "note: the baseline was measured by targo-trust commit `{}`, this run by `{}`\n",
            baseline.targo_trust_commit, facts.targo_trust_commit
        ));
    }
    if baseline.profile != facts.profile {
        out.push_str(&format!(
            "note: the baseline's budget profile is `{}`, this run's `{}`\n",
            baseline.profile, facts.profile
        ));
    }
    if facts.degraded_anchors > 0 {
        out.push_str(&format!(
            "note: {} obligation key(s) of this run were minted on a degraded anchor (a span \
             outside its file's text): those keys are coarser than a content address\n",
            facts.degraded_anchors
        ));
    }
    for lost in &comparison.lost {
        out.push_str(&format!("LOST {}\n", lost.line()));
    }
    for (package, record) in comparison.new_failed() {
        out.push_str(&format!("NEW FAILED {}\n", record_line(package, record)));
    }
    for (package, record) in &comparison.unmeasured_keys {
        out.push_str(&format!(
            "NOT MEASURED {} (a non-reproducible stop decides nothing)\n",
            record_line(package, record)
        ));
    }
    for (package, record) in &comparison.failed_unchanged {
        out.push_str(&format!(
            "FAILED {} (its function is unchanged since the baseline)\n",
            record_line(package, record)
        ));
    }
    for (package, record) in &comparison.gained {
        out.push_str(&format!(
            "GAINED {package} {} {} {}\n",
            record.key,
            record.kind,
            record.location_label()
        ));
    }
    for (package, record) in comparison.new_unproved.iter().filter(|(_, r)| !r.is_failed()) {
        out.push_str(&format!("NEW {}\n", record_line(package, record)));
    }
    for (package, key) in &comparison.vanished_with_edit {
        out.push_str(&format!("VANISHED {package} {key} (its function's source changed)\n"));
    }
    for (package, from, to, how) in &comparison.moved_functions {
        out.push_str(&format!("MOVED {package} {from} -> {to} (paired by {})\n", how.as_str()));
    }
    for (package, function) in &comparison.removed_functions {
        out.push_str(&format!("REMOVED {package} {function}\n"));
    }
    for package in &comparison.unmeasured_packages {
        out.push_str(&format!("NOT MEASURED {package}: the run produced no record for it\n"));
    }
    for function in &records.conflicting_functions {
        out.push_str(&format!(
            "NOT MEASURED {function}: published with two different source digests\n"
        ));
    }
    for function in &records.unkeyed_functions {
        out.push_str(&format!("NOT MEASURED {function}: a row with no stable key\n"));
    }
    out.push_str(&format!(
        "Baseline: {} lost, {} new failed, {} not measured, {} gained, {} new unproved, {} \
         vanished with an edit, {} removed function(s), {} moved function(s)\n",
        comparison.lost.len(),
        comparison.new_failed().count(),
        comparison.unmeasured_keys.len(),
        comparison.gained.len(),
        comparison.new_unproved.len(),
        comparison.vanished_with_edit.len(),
        comparison.removed_functions.len(),
        comparison.moved_functions.len()
    ));
    out
}

/// Machine-readable report of a comparison.
pub(crate) fn render_json(
    comparison: &Comparison,
    records: &ObligationRecords,
    exit: u8,
) -> serde_json::Value {
    let record = |package: &String, record: &ObligationRecord| {
        serde_json::json!({
            "package": package,
            "key": record.key,
            "kind": record.kind,
            "status": record.status,
            "stop": record.stop,
            "location": record.location_label(),
        })
    };
    let records_of = |list: &[(String, ObligationRecord)]| {
        list.iter().map(|(p, r)| record(p, r)).collect::<Vec<_>>()
    };
    serde_json::json!({
        "schema": "trust.baseline-diff.v1",
        "exit": exit,
        "lost": comparison.lost.iter().map(|lost| serde_json::json!({
            "package": lost.package,
            "function": lost.function,
            "id": lost.id,
            "reason": match lost.reason {
                LostReason::NotProved => "not-proved",
                LostReason::VanishedFromUnchangedSource => "vanished-from-unchanged-source",
            },
            "now": lost.now.as_ref().map(|now| record(&lost.package, now)),
        })).collect::<Vec<_>>(),
        "new_failed": comparison.new_failed().map(|(p, r)| record(p, r)).collect::<Vec<_>>(),
        "not_measured_keys": records_of(&comparison.unmeasured_keys),
        "failed_unchanged": records_of(&comparison.failed_unchanged),
        "gained": records_of(&comparison.gained),
        "new_unproved": records_of(&comparison.new_unproved),
        "vanished_with_edit": comparison.vanished_with_edit.iter().map(|(p, key)| serde_json::json!({
            "package": p, "key": key,
        })).collect::<Vec<_>>(),
        "moved": comparison.moved_functions.iter().map(|(p, from, to, how)| serde_json::json!({
            "package": p, "from": from, "to": to, "paired_by": how.as_str(),
        })).collect::<Vec<_>>(),
        "removed": comparison.removed_functions.iter().map(|(p, f)| serde_json::json!({
            "package": p, "function": f,
        })).collect::<Vec<_>>(),
        "not_measured": comparison.unmeasured_packages,
        "conflicting_functions": records.conflicting_functions,
        "unkeyed_functions": records.unkeyed_functions,
        "degraded_anchors": records.facts.degraded_anchors,
    })
}

/// Read a baseline file.
pub(crate) fn read(path: &Path) -> Result<Baseline, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read baseline `{}`: {error}", path.display()))?;
    Baseline::parse(&text).map_err(|error| format!("baseline `{}`: {error}", path.display()))
}

/// Write a baseline file atomically (temp file and rename).
pub(crate) fn write(path: &Path, baseline: &Baseline) -> io::Result<()> {
    crate::durable_io::atomic_write_private(path, baseline.render().as_bytes())
}

/// The proved keys a run would add to or remove from `previous`, for the
/// `--save-baseline` summary: `(lost, gained)` key counts per package.
pub(crate) fn key_delta(previous: &Baseline, next: &Baseline) -> (Vec<String>, Vec<String>) {
    let packages: BTreeSet<&String> =
        previous.packages.keys().chain(next.packages.keys()).collect();
    let mut lost = Vec::new();
    let mut gained = Vec::new();
    for package in packages {
        let before = previous.proved_keys(package);
        let after = next.proved_keys(package);
        lost.extend(before.difference(&after).map(|key| format!("{package} {key}")));
        gained.extend(after.difference(&before).map(|key| format!("{package} {key}")));
    }
    (lost, gained)
}

// ---------------------------------------------------------------------------
// The two commands.
// ---------------------------------------------------------------------------

/// Finish `targo trust check --save-baseline <path>`: write the run's proved
/// keys into the baseline at `path` (merged with the packages it already holds
/// that this run did not select) and return the check's own exit status. A
/// run that is not a measurement leaves the file untouched and exits 3.
pub(crate) fn finish_save_baseline(
    path: &Path,
    records: Option<&ObligationRecords>,
    check_exit: std::process::ExitCode,
) -> std::process::ExitCode {
    use std::process::ExitCode;
    let Some(records) = records else {
        eprintln!(
            "targo trust: baseline NOT saved: the run produced no live measurement (an \
             incomplete coverage inventory, an excluded Unit or an abnormal compiler exit; see \
             above); `{}` is unchanged",
            path.display()
        );
        return ExitCode::from(EXIT_NOT_MEASURED);
    };
    if let Some(refusal) = save_refusal(records) {
        eprintln!("targo trust: baseline NOT saved: {refusal}; `{}` is unchanged", path.display());
        return ExitCode::from(EXIT_NOT_MEASURED);
    }
    let run = Baseline::project(records);
    let (previous, next) = if path.exists() {
        let previous = match read(path) {
            Ok(previous) => previous,
            Err(error) => {
                eprintln!("targo trust: baseline NOT saved: {error}");
                return ExitCode::from(EXIT_USAGE);
            }
        };
        match merge(&previous, &run, &records.scope) {
            Ok(Merged { baseline, dropped }) => {
                for (package, why) in &dropped {
                    eprintln!("targo trust: baseline: package `{package}` dropped: {why}");
                }
                (Some(previous), baseline)
            }
            Err(MergeRefusal(reason)) => {
                eprintln!("targo trust: baseline NOT saved: {reason}");
                return ExitCode::from(EXIT_USAGE);
            }
        }
    } else {
        (None, run)
    };
    if let Some(previous) = &previous {
        let (lost, gained) = key_delta(previous, &next);
        for key in &lost {
            eprintln!("targo trust: baseline: no longer proved: {key}");
        }
        for key in &gained {
            eprintln!("targo trust: baseline: newly proved: {key}");
        }
    }
    if let Err(error) = write(path, &next) {
        eprintln!("targo trust: baseline NOT saved: cannot write `{}`: {error}", path.display());
        return ExitCode::from(EXIT_USAGE);
    }
    let keys: usize = next
        .packages
        .values()
        .flat_map(|functions| functions.values())
        .map(|function| function.proved.len())
        .sum();
    eprintln!(
        "targo trust: baseline saved: {keys} proved obligation key(s) in {} package(s) to `{}`",
        next.packages.len(),
        path.display()
    );
    check_exit
}

/// The lane flags that select a baseline's gate lane and compiler policy, for
/// a diff that names none; `None` for a pair no flag set selects.
fn lane_flags(lane: &str, policy: &str) -> Option<&'static [&'static str]> {
    match (lane, policy) {
        ("strict", "strict") => Some(&[]),
        ("advisory", "strict") => Some(&["--allow-l0-gaps"]),
        ("advisory", "advisory") => Some(&["--survey"]),
        ("memory-safe", "memory-safe") => Some(&["--memory-safe"]),
        ("certify", "certify") => Some(&["--certify"]),
        _ => None,
    }
}

/// The packages `-p`/`--package` name in `args`, before any `--`.
pub(crate) fn explicit_packages(args: &[String]) -> BTreeSet<String> {
    let mut packages = BTreeSet::new();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--" {
            break;
        }
        if matches!(arg, "-p" | "--package") {
            if let Some(value) = args.get(index + 1) {
                packages.insert(value.clone());
                index += 1;
            }
        } else if let Some(value) = arg.strip_prefix("--package=") {
            packages.insert(value.to_string());
        } else if let Some(value) = arg.strip_prefix("-p").filter(|value| !value.is_empty()) {
            packages.insert(value.to_string());
        }
        index += 1;
    }
    packages
}

/// The `targo trust check` argument list a diff runs: the diff's own
/// arguments without `--baseline`, plus — where the diff names none — the
/// baseline's packages, its target selection and its lane.
pub(crate) fn diff_check_args(
    args: &[String],
    baseline: &Baseline,
    names_a_lane: bool,
) -> Vec<String> {
    let mut check = Vec::with_capacity(args.len() + 8);
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "--baseline" {
            index += 2;
            continue;
        }
        if arg.starts_with("--baseline=") {
            index += 1;
            continue;
        }
        check.push(arg.clone());
        index += 1;
    }
    let separator = check.iter().position(|arg| arg == "--").unwrap_or(check.len());
    let mut added = Vec::new();
    if explicit_packages(&check).is_empty() {
        for package in baseline.packages.keys() {
            added.push("-p".to_string());
            added.push(package.clone());
        }
    }
    if crate::obligations::canonical_selection(&check) == "default" {
        added.extend(crate::obligations::selection_args(&baseline.selection));
    }
    if !names_a_lane {
        added.extend(
            lane_flags(&baseline.lane, &baseline.policy)
                .unwrap_or_default()
                .iter()
                .map(ToString::to_string),
        );
    }
    check.splice(separator..separator, added);
    check
}

/// `targo trust diff --baseline <path>`: run the live check the baseline
/// describes and compare. Exit 0 nothing lost, 1 lost, 2 usage, 3 not measured.
pub(crate) fn run_baseline_diff(
    sub_args: &crate::cli::SubcommandArgs,
    args: &[String],
    path: &Path,
) -> std::process::ExitCode {
    use std::process::ExitCode;
    let baseline = match read(path) {
        Ok(baseline) => baseline,
        Err(error) => {
            eprintln!("targo trust diff: {error}");
            return ExitCode::from(EXIT_USAGE);
        }
    };
    let names_a_lane =
        sub_args.allow_l0_gaps || sub_args.memory_safe || sub_args.certify || sub_args.survey;
    if !names_a_lane && lane_flags(&baseline.lane, &baseline.policy).is_none() {
        eprintln!(
            "targo trust diff: no lane flag selects the baseline's lane `{}` with policy `{}`; \
             name the lane",
            baseline.lane, baseline.policy
        );
        return ExitCode::from(EXIT_USAGE);
    }
    let check_args = diff_check_args(args, &baseline, names_a_lane);
    let scope = explicit_packages(args);
    let mut captured: Option<ObligationRecords> = None;
    let mut capture = |live: &crate::report::LiveCanonicalReport| -> Result<(), String> {
        captured = live.obligation_records().cloned();
        Ok(())
    };
    // The check's own exit status is not the diff's — the comparison decides,
    // and a refutation in new code fails it there — but it is stated.
    let check_exit = crate::run_subcommand_with_live_report(
        crate::types::Subcommand::Check,
        &check_args,
        Some(&mut capture),
        false,
    );
    if check_exit != ExitCode::SUCCESS {
        eprintln!(
            "targo trust diff: note: the check itself did not pass (its `Gate:` line is above); \
             this command's exit is the comparison's"
        );
    }
    let Some(records) = captured else {
        eprintln!(
            "targo trust diff: NOT MEASURED: the live check produced no measurement (an \
             incomplete coverage inventory, an excluded Unit or an abnormal compiler exit; see \
             above), so nothing can be compared"
        );
        return ExitCode::from(EXIT_NOT_MEASURED);
    };
    if let Some(mismatch) = lane_mismatch(&baseline, &records.facts) {
        eprintln!("targo trust diff: {mismatch}; compare like with like");
        return ExitCode::from(EXIT_USAGE);
    }
    let comparison = compare(&baseline, &records, (!scope.is_empty()).then_some(&scope));
    let exit = exit_status(&comparison, &records);
    match sub_args.format {
        crate::types::OutputFormat::Json => println!(
            "{}",
            serde_json::to_string_pretty(&render_json(&comparison, &records, exit))
                .expect("a JSON value serializes")
        ),
        _ => print!("{}", render_terminal(&comparison, &baseline, &records)),
    }
    if exit == EXIT_NOT_MEASURED {
        let coverage = if records.facts.coverage_complete { "" } else { ", coverage incomplete" };
        let unkeyed = if records.unkeyed_functions.is_empty() {
            String::new()
        } else {
            format!(", {} function(s) without stable keys", records.unkeyed_functions.len())
        };
        let keys = if comparison.unmeasured_keys.is_empty() {
            String::new()
        } else {
            format!(
                ", {} baseline key(s) stopped by a non-reproducible cause",
                comparison.unmeasured_keys.len()
            )
        };
        eprintln!(
            "targo trust diff: NOT MEASURED: nothing was lost, but the run is `{}`{coverage}\
             {unkeyed}{keys} — each is named above, and the stop causes are on the check's \
             `Stop causes:` line",
            records.facts.outcome
        );
    }
    ExitCode::from(exit)
}

/// One function's records keyed for tests and callers that build them by hand.
#[cfg(test)]
pub(crate) fn function_records(
    source: Option<&str>,
    records: Vec<ObligationRecord>,
) -> crate::obligations::FunctionRecords {
    crate::obligations::FunctionRecords {
        source: source.map(str::to_string),
        obligations: records
            .into_iter()
            .map(|record| {
                let (_, id) = trust_types::obligation_identity::split_obligation_key(&record.key)
                    .expect("a test record carries a well-formed key");
                (id.to_string(), record)
            })
            .collect(),
    }
}

#[cfg(test)]
#[path = "baseline_tests.rs"]
mod tests;
