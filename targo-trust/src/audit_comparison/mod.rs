//! Native comparison of historical compiler audit measurements.
//!
//! These saved rows are observational inputs, never proof, execution or landing
//! authority. The three modes preserve their distinct identity, attribution and
//! nonvacuity rules. A caller qualifying a candidate must additionally bind the
//! actual source/toolchain pair, selected populations and live run outcomes.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub(crate) mod caps;
mod cli;
mod l3;
mod l4;
mod obligations;
pub(crate) mod parse;
pub(crate) use cli::run_subcommand;

#[cfg(test)]
mod tests;

pub(crate) type Function = [String; 4];
type Identity = Vec<String>;
type Counter<T> = BTreeMap<T, usize>;
type Verdict = (String, String);
type RowDigest = (String, String, String);
const FUNCTION_COLUMNS: usize = 4;
pub(crate) const ORACLES: &[&str] = &["row", "identity", "dedup", "lowering", "size"];
const VERDICT_GATES: &[&str] = &["uncertified", "stale", "twin"];
const CONSUME_ORDER: &[&str] =
    &["ambiguous", "unique", "moved", "statement", "uncertified", "stale", "twin", "absent"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ComparisonMode {
    L3,
    L4,
    PublishedObligations,
}

#[derive(Clone, Debug)]
pub(crate) struct ComparisonPolicy {
    pub(crate) mode: ComparisonMode,
    pub(crate) deleted_cap_groups: BTreeSet<String>,
    pub(crate) required_oracles: Vec<String>,
    pub(crate) attributions: Option<PathBuf>,
}

impl ComparisonPolicy {
    pub(crate) fn validate(&self) -> Result<(), String> {
        for group in &self.deleted_cap_groups {
            if !caps::DELETED_CAPS.iter().any(|(known, _)| *known == group) {
                return Err(format!("--deleted-caps: unknown commit id {group:?}"));
            }
        }
        for oracle in &self.required_oracles {
            if !ORACLES.contains(&oracle.as_str()) {
                return Err(format!("--oracles: unknown oracle {oracle:?}"));
            }
        }
        if self.mode == ComparisonMode::L3
            && (!self.deleted_cap_groups.is_empty()
                || !self.required_oracles.is_empty()
                || self.attributions.is_some())
        {
            return Err(
                "--deleted-caps, --attributed and --oracles need --l4 or --obligations".into()
            );
        }
        if self.mode == ComparisonMode::PublishedObligations && !self.required_oracles.is_empty() {
            return Err("--oracles needs --l4".into());
        }
        Ok(())
    }

    fn judged_sites(&self) -> BTreeSet<String> {
        caps::DELETED_CAPS
            .iter()
            .chain(caps::MOVED_CAPS)
            .filter(|(group, _)| self.deleted_cap_groups.contains(*group))
            .flat_map(|(_, sites)| sites.iter().map(|site| (*site).to_owned()))
            .collect()
    }
}

pub(crate) struct AuditInputPair<'a> {
    pub(crate) parent: &'a Path,
    pub(crate) candidate: &'a Path,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ComparisonOutcome {
    Pass,
    Violation,
    CouldNotRun,
}

/// Census of the rows actually read; empty/unavailable inputs never imply pass.
#[derive(Clone, Debug, Default)]
pub(crate) struct Census {
    pub(crate) elided: usize,
    pub(crate) kept: Counter<String>,
    pub(crate) origins: Counter<String>,
    pub(crate) verdict_rows: usize,
    pub(crate) unkeyed: usize,
    pub(crate) malformed_rows: usize,
    pub(crate) ignored: Counter<String>,
    pub(crate) rowdigest_rows: usize,
    pub(crate) rowdigest_functions: usize,
    pub(crate) obligations: usize,
    pub(crate) corpora: BTreeSet<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct ComparisonReport {
    pub(crate) outcome: ComparisonOutcome,
    pub(crate) listed: Vec<String>,
    pub(crate) violations: Vec<String>,
    pub(crate) malformed: Vec<String>,
    pub(crate) unattributed: Vec<String>,
    pub(crate) parent: Census,
    pub(crate) candidate: Census,
    lines: Vec<String>,
}

impl ComparisonReport {
    fn new() -> Self {
        Self {
            outcome: ComparisonOutcome::CouldNotRun,
            listed: Vec::new(),
            violations: Vec::new(),
            malformed: Vec::new(),
            unattributed: Vec::new(),
            parent: Census::default(),
            candidate: Census::default(),
            lines: Vec::new(),
        }
    }

    fn could_not_run(message: impl Into<String>) -> Self {
        let mut report = Self::new();
        let message = message.into();
        report.malformed.push(message.clone());
        report.lines.push(format!("COULD NOT RUN: {message}"));
        report
    }

    pub(crate) fn exit_code(&self) -> u8 {
        match self.outcome {
            ComparisonOutcome::Pass => 0,
            ComparisonOutcome::Violation => 1,
            ComparisonOutcome::CouldNotRun => 3,
        }
    }

    pub(crate) fn render_terminal(&self) -> String {
        let mut text = self.lines.join("\n");
        text.push('\n');
        text
    }

    fn conclude(&mut self, outcome: ComparisonOutcome, message: impl Into<String>) {
        self.outcome = outcome;
        self.lines.push(message.into());
    }

    fn side_summaries(&mut self, parent: &parse::Audit, candidate: &parse::Audit) {
        self.parent = parent.census();
        self.candidate = candidate.census();
        for (name, side) in [("parent", &self.parent), ("candidate", &self.candidate)] {
            let tables = if side.origins.is_empty() {
                "none".into()
            } else {
                side.origins
                    .iter()
                    .map(|(key, count)| format!("{key} {count}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            self.lines.push(format!(
                "{name:9}: {} elided; kept {}; tables: {tables}; {} verdict rows ({} unkeyed); {} malformed rows",
                side.elided, string_counter(&side.kept), side.verdict_rows,
                side.unkeyed, side.malformed_rows,
            ));
        }
    }

    fn diagnostics(&mut self, by_operation: bool) {
        let mut classes = Counter::new();
        for line in &self.listed {
            increment(&mut classes, line.split('\t').next().unwrap_or("").to_owned());
        }
        for (class, count) in classes {
            self.lines.push(format!("listed ({class}): {count}"));
        }
        if by_operation {
            let mut operations = Counter::new();
            for line in &self.listed {
                if line.starts_with("verdict ")
                    || line.starts_with("rows ")
                    || line.starts_with("unjudged binding ")
                {
                    continue;
                }
                let fields = line.split('\t').collect::<Vec<_>>();
                if fields.len() >= 3 {
                    increment(
                        &mut operations,
                        (fields[0].to_owned(), fields[fields.len() - 3].to_owned()),
                    );
                }
            }
            for ((class, operation), count) in operations {
                self.lines.push(format!("  by op ({class}, {operation}): {count}"));
            }
        }
        self.lines.extend(self.listed.iter().map(|line| format!("  LISTED\t{line}")));
        self.lines.extend(self.violations.iter().map(|line| format!("  VIOLATION\t{line}")));
        self.lines.extend(self.malformed.iter().map(|line| format!("  MALFORMED\t{line}")));
        self.lines.extend(self.unattributed.iter().map(|line| format!("  UNATTRIBUTED\t{line}")));
    }
}

pub(crate) fn compare(pair: AuditInputPair<'_>, policy: &ComparisonPolicy) -> ComparisonReport {
    // The public CLI validates this as usage (2). Library callers still fail
    // closed rather than treating an invalid policy as a successful comparison.
    if let Err(error) = policy.validate() {
        return ComparisonReport::could_not_run(error);
    }
    let attributions = match parse::Attributions::read(policy.attributions.as_deref()) {
        Ok(attributions) => attributions,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    match policy.mode {
        ComparisonMode::L3 => l3::compare(pair),
        ComparisonMode::L4 => l4::compare(pair, policy, attributions),
        ComparisonMode::PublishedObligations => obligations::compare(pair, policy, attributions),
    }
}

pub(crate) fn is_crate_level(function: &[String]) -> bool {
    function.get(3).is_some_and(|scope| {
        scope == "crate"
            || scope
                .strip_prefix("crate:")
                .is_some_and(|label| !label.is_empty() && !label.contains(':'))
    })
}

fn function_of(identity: &[String]) -> Function {
    std::array::from_fn(|index| identity[index].clone())
}

fn identity(function: &Function, suffix: impl IntoIterator<Item = String>) -> Identity {
    function.iter().cloned().chain(suffix).collect()
}

fn increment<K: Ord>(counter: &mut Counter<K>, key: K) {
    *counter.entry(key).or_default() += 1;
}

fn subtract<K: Ord + Clone>(ours: &Counter<K>, theirs: &Counter<K>) -> Counter<K> {
    ours.iter()
        .filter_map(|(key, count)| {
            let difference = count.saturating_sub(*theirs.get(key).unwrap_or(&0));
            (difference != 0).then(|| (key.clone(), difference))
        })
        .collect()
}

fn sum<K>(counter: &Counter<K>) -> usize {
    counter.values().sum()
}
fn joined(function: &[String]) -> String {
    function.join("\t")
}
fn py_string(value: &str) -> String {
    format!("'{}'", value.replace('\\', "\\\\").replace('\'', "\\'"))
}
fn string_counter(counter: &Counter<String>) -> String {
    format!(
        "{{{}}}",
        counter
            .iter()
            .map(|(key, count)| format!("{}: {count}", py_string(key)))
            .collect::<Vec<_>>()
            .join(", ")
    )
}
fn verdicts(counter: &Counter<Verdict>) -> String {
    format!(
        "[{}]",
        counter
            .iter()
            .flat_map(|((status, stop), count)| {
                std::iter::repeat_n(format!("({}, {})", py_string(status), py_string(stop)), *count)
            })
            .collect::<Vec<_>>()
            .join(", ")
    )
}
fn pop_worst(reasons: &mut Counter<String>) -> Option<String> {
    let known = CONSUME_ORDER
        .iter()
        .find(|reason| reasons.get(**reason).copied().unwrap_or(0) > 0)
        .map(|reason| (*reason).to_owned());
    let reason = known.or_else(|| {
        reasons.iter().find(|(_, count)| **count > 0).map(|(reason, _)| reason.clone())
    })?;
    *reasons.get_mut(&reason).expect("selected positive count") -= 1;
    Some(reason)
}

fn reproducible(stop: &str) -> bool {
    trust_types::determinism::StopCause::parse(stop).is_some_and(|cause| {
        cause.reproducibility() == trust_types::determinism::Reproducibility::Deterministic
    })
}

pub(crate) fn clock_verdict(stop: &str) -> bool {
    matches!(stop, "wall-backstop" | "rss-backstop" | "solver-fault" | "admission-refused")
}
