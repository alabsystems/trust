//! Typed comparison of one consumer's check under the deployed seal and under a
//! candidate seal (docs/CUTTING-A-TOOLCHAIN.md §3.9, the consumer check; D27(b)).
//!
//! A cut's consumer check asks one question per consumer: does the candidate
//! make anything worse than the seal it replaces? The answer is one of three
//! verdicts, decided from two saved runs of the same command on the same tree
//! under the same budget:
//!
//! * `PASS`: the candidate's command exits 0 and loses no proof.
//! * `SHARED_RED`: the candidate is red, and nothing it shows is new.
//! * `NEW_RED`: the candidate loses a proof the deployed seal had (D27(b)),
//!   names a red the deployed seal does not, or ends in a worse way.
//!
//! Two runs that differ in tree, command or budget are not compared: a verdict
//! here depends on wall clocks and host memory until T2d lands, so a pair run
//! under unequal budgets says nothing about the compiler.
//!
//! Saved rows are observations. A verdict is a release-gate input, never a
//! proof, and it grants nothing by itself.

use std::collections::{BTreeMap, BTreeSet};

mod cli;
mod records;
mod state;

#[cfg(test)]
mod tests;

pub(crate) use cli::run_subcommand;
pub(crate) use records::{Row, Run, RunRecord};

/// What one consumer's pair of runs establishes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Verdict {
    Pass,
    SharedRed,
    NewRed,
}

impl Verdict {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::SharedRed => "SHARED_RED",
            Self::NewRed => "NEW_RED",
        }
    }
}

/// How a run's command ended. The order is from best to worst.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ending {
    /// The command exited 0.
    Green,
    /// The command finished and exited nonzero.
    Red,
    /// The run's wall-clock bound ended the command: it has no verdict.
    StoppedAtBound,
}

impl Ending {
    fn of(record: &RunRecord) -> Self {
        if record.stopped_at_bound {
            Self::StoppedAtBound
        } else if record.exit == 0 {
            Self::Green
        } else {
            Self::Red
        }
    }

    fn describe(self, exit: i32) -> String {
        match self {
            Self::Green => "exit 0".into(),
            Self::Red => format!("exit {exit}"),
            Self::StoppedAtBound => format!("stopped at its bound (exit {exit})"),
        }
    }
}

/// One thing the candidate shows that the deployed seal does not.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum NewRed {
    /// The candidate's command ended worse than the deployed seal's.
    Ending { deployed: String, candidate: String },
    /// A named red (a failing test) of the candidate that the deployed run lacks.
    Named(String),
    /// A proof at a site both records hold: proved before, not proved now.
    LostProof { site: Site, proved_before: usize, proved_now: usize, now: String, clock: bool },
    /// Proofs at sites the candidate no longer has, in a function whose new
    /// sites of the same kind are not all proved.
    LostMovedProof { package: String, function: String, kind: String, rows: usize },
}

impl NewRed {
    pub(crate) fn render(&self) -> String {
        match self {
            Self::Ending { deployed, candidate } => {
                format!("ending\tdeployed {deployed}\tcandidate {candidate}")
            }
            Self::Named(name) => format!("named red\t{name}"),
            Self::LostProof { site, proved_before, proved_now, now, clock } => format!(
                "lost proof{}\t{}\t{}\t{}\t{}:{}:{}\tproved {proved_before} -> {proved_now}\tnow {now}",
                if *clock { " (clock-stopped)" } else { "" },
                site.package,
                site.function,
                site.kind,
                site.file,
                site.line,
                site.column,
            ),
            Self::LostMovedProof { package, function, kind, rows } => format!(
                "lost proof (site moved)\t{package}\t{function}\t{kind}\t{rows} row(s) proved before sit at no candidate site, and the candidate's new sites of this kind are not all proved"
            ),
        }
    }
}

/// Where an obligation is, in terms both seals agree on. The per-obligation
/// hash in a record's key is the compiler's own and differs between seals.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Site {
    pub(crate) package: String,
    pub(crate) function: String,
    pub(crate) kind: String,
    pub(crate) file: String,
    pub(crate) line: u64,
    pub(crate) column: u64,
}

/// Facts a reader of the verdict should see, none of which decides it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Disclosures {
    /// Proved rows under each seal.
    pub(crate) proved_deployed: usize,
    pub(crate) proved_candidate: usize,
    /// Candidate `failed` rows at sites where the deployed seal has no `failed`
    /// row, by what the deployed seal recorded there. The deployed seal proved
    /// none of them: a refuted row it proved is a lost proof and a new red.
    pub(crate) candidate_only_failed: BTreeMap<String, usize>,
    /// Lost proofs whose candidate row was stopped by a clock or by memory.
    pub(crate) lost_clock_stopped: usize,
    /// Proved rows of the deployed seal whose site and kind the candidate no
    /// longer has in that function at all: the obligation is gone, not unproved.
    pub(crate) vanished: usize,
}

/// The whole result for one consumer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Comparison {
    pub(crate) verdict: Verdict,
    pub(crate) new_reds: Vec<NewRed>,
    pub(crate) disclosures: Disclosures,
}

/// Why a pair of finished runs cannot be compared.
pub(crate) fn incomparable(deployed: &RunRecord, candidate: &RunRecord) -> Option<String> {
    if deployed.consumer != candidate.consumer {
        return Some(format!(
            "the runs are of different consumers: deployed {:?}, candidate {:?}",
            deployed.consumer, candidate.consumer
        ));
    }
    if deployed.tree != candidate.tree {
        return Some(format!(
            "the runs are not of the same tree: deployed {}, candidate {}",
            deployed.tree, candidate.tree
        ));
    }
    if deployed.command != candidate.command {
        return Some("the runs are not of the same command".into());
    }
    if (deployed.cpus, deployed.memory_gib) != (candidate.cpus, candidate.memory_gib) {
        return Some(format!(
            "the runs are not under the same budget: deployed {} CPU/{} GiB, candidate {} CPU/{} GiB",
            deployed.cpus, deployed.memory_gib, candidate.cpus, candidate.memory_gib
        ));
    }
    if deployed.seal == candidate.seal {
        return Some(format!("both runs are of one seal, {}", deployed.seal));
    }
    None
}

#[derive(Default)]
struct SiteRows {
    proved: usize,
    failed: usize,
    /// Every row that is not proved, as `status/stop`, for the report.
    unproved: BTreeMap<String, usize>,
    clock: bool,
}

fn by_site(rows: &[Row]) -> BTreeMap<Site, SiteRows> {
    let mut sites = BTreeMap::<Site, SiteRows>::new();
    for row in rows {
        let entry = sites.entry(row.site.clone()).or_default();
        match row.status.as_str() {
            "proved" => entry.proved += 1,
            status => {
                if status == "failed" {
                    entry.failed += 1;
                }
                if status == "timeout" || crate::audit_comparison::clock_verdict(&row.stop) {
                    entry.clock = true;
                }
                *entry.unproved.entry(format!("{status}/{}", row.stop)).or_default() += 1;
            }
        }
    }
    sites
}

fn dispositions(rows: &SiteRows) -> String {
    if rows.unproved.is_empty() {
        return "proved (fewer rows)".into();
    }
    rows.unproved.keys().cloned().collect::<Vec<_>>().join(", ")
}

type FunctionKind = (String, String, String);

/// Compare two finished, comparable runs ([`incomparable`] answered `None`).
pub(crate) fn compare(deployed: &Run, candidate: &Run) -> Comparison {
    let mut new_reds = BTreeSet::<NewRed>::new();
    let mut disclosures = Disclosures::default();

    let before = Ending::of(&deployed.record);
    let after = Ending::of(&candidate.record);
    if after > before {
        new_reds.insert(NewRed::Ending {
            deployed: before.describe(deployed.record.exit),
            candidate: after.describe(candidate.record.exit),
        });
    }

    let known = deployed.record.reds.iter().collect::<BTreeSet<_>>();
    for name in &candidate.record.reds {
        if !known.contains(name) {
            new_reds.insert(NewRed::Named(name.clone()));
        }
    }

    let old = by_site(&deployed.rows);
    let new = by_site(&candidate.rows);
    disclosures.proved_deployed = old.values().map(|rows| rows.proved).sum();
    disclosures.proved_candidate = new.values().map(|rows| rows.proved).sum();

    // Proved rows of the deployed seal at sites the candidate does not have, and
    // what the candidate has at sites the deployed seal does not, per function
    // and kind: a site moves when the sysroot's source lines do.
    let mut unplaced = BTreeMap::<FunctionKind, usize>::new();
    let mut fresh = BTreeMap::<FunctionKind, (usize, usize)>::new();
    let function_kind =
        |site: &Site| (site.package.clone(), site.function.clone(), site.kind.clone());
    for (site, rows) in &old {
        if rows.proved == 0 {
            continue;
        }
        match new.get(site) {
            Some(now) if now.proved < rows.proved => {
                if now.clock {
                    disclosures.lost_clock_stopped += rows.proved - now.proved;
                }
                new_reds.insert(NewRed::LostProof {
                    site: site.clone(),
                    proved_before: rows.proved,
                    proved_now: now.proved,
                    now: dispositions(now),
                    clock: now.clock,
                });
            }
            Some(_) => {}
            None => *unplaced.entry(function_kind(site)).or_default() += rows.proved,
        }
    }
    for (site, rows) in &new {
        if !old.contains_key(site) {
            let entry = fresh.entry(function_kind(site)).or_default();
            entry.0 += rows.proved;
            entry.1 += rows.unproved.values().sum::<usize>();
        }
        if rows.failed > old.get(site).map_or(0, |before| before.failed) {
            let was = match old.get(site) {
                None => "absent".to_string(),
                Some(before) if before.unproved.is_empty() => "proved".to_string(),
                Some(before) => dispositions(before),
            };
            // A refuted row the deployed seal proved is already a lost proof.
            if was != "proved" {
                *disclosures.candidate_only_failed.entry(was).or_default() +=
                    rows.failed - old.get(site).map_or(0, |before| before.failed);
            }
        }
    }
    for ((package, function, kind), rows) in unplaced {
        let (proved, unproved) = fresh
            .get(&(package.clone(), function.clone(), kind.clone()))
            .copied()
            .unwrap_or((0, 0));
        let remaining = rows.saturating_sub(proved);
        let lost = remaining.min(unproved);
        disclosures.vanished += remaining - lost;
        if lost > 0 {
            new_reds.insert(NewRed::LostMovedProof { package, function, kind, rows: lost });
        }
    }

    let verdict = if !new_reds.is_empty() {
        Verdict::NewRed
    } else if after == Ending::Green {
        Verdict::Pass
    } else {
        Verdict::SharedRed
    };
    Comparison { verdict, new_reds: new_reds.into_iter().collect(), disclosures }
}
