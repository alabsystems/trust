//! The comparison's state on disk, one directory per consumer:
//!
//! ```text
//! <state>/<consumer>/deployed/run.json     the deployed seal's run
//! <state>/<consumer>/candidate/run.json    the candidate's run
//! <state>/<consumer>/verdict.json          written here
//! ```
//!
//! A verdict is recorded with the digest of the bytes it was decided from. A
//! later invocation keeps a recorded verdict whose inputs are unchanged and
//! decides the consumers that have finished since, so the command can be run
//! again at any point of a cut, on any machine that holds the state.

use std::collections::BTreeSet;
use std::io;
use std::path::Path;

use serde_json::{Value, json};

use super::records::{self, Loaded, Run};
use super::{Comparison, Verdict, compare, incomparable};

pub(crate) const VERDICT_SCHEMA: &str = "trust.seal-consumer-verdict.v1";
const VERDICT_FILE: &str = "verdict.json";

/// One consumer's line of the table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Outcome {
    Decided {
        verdict: Verdict,
        /// The recorded verdict was kept: its inputs are byte-identical.
        reused: bool,
        report: Value,
    },
    /// A run is missing or unfinished.
    Pending(String),
    /// Both runs finished and cannot be compared, or an input is malformed.
    Incomparable(String),
}

fn report(deployed: &Run, candidate: &Run, comparison: &Comparison) -> Value {
    let run = |run: &Run| {
        json!({
            "seal": run.record.seal,
            "exit": run.record.exit,
            "stopped_at_bound": run.record.stopped_at_bound,
            "rows": run.rows.len(),
            "named_reds": run.record.reds.len(),
            "digest": run.digest,
        })
    };
    let disclosures = &comparison.disclosures;
    json!({
        "schema": VERDICT_SCHEMA,
        "consumer": candidate.record.consumer,
        "tree": candidate.record.tree,
        "command": candidate.record.command,
        "budget": { "cpus": candidate.record.cpus, "memory_gib": candidate.record.memory_gib },
        "verdict": comparison.verdict.label(),
        "deployed": run(deployed),
        "candidate": run(candidate),
        "new_reds": comparison.new_reds.iter().map(super::NewRed::render).collect::<Vec<_>>(),
        "disclosures": {
            "proved_deployed": disclosures.proved_deployed,
            "proved_candidate": disclosures.proved_candidate,
            "candidate_only_failed": disclosures.candidate_only_failed,
            "lost_clock_stopped": disclosures.lost_clock_stopped,
            "vanished": disclosures.vanished,
        },
        "scope": "A release-gate comparison of saved runs. Not a proof, and no permission to publish by itself.",
    })
}

fn recorded(path: &Path, deployed: &Run, candidate: &Run) -> Option<(Verdict, Value)> {
    let bytes = std::fs::read(path).ok()?;
    let value: Value = serde_json::from_slice(&bytes).ok()?;
    let digest = |side: &str| value.get(side)?.get("digest")?.as_str().map(str::to_owned);
    if value.get("schema")?.as_str()? != VERDICT_SCHEMA
        || digest("deployed")? != deployed.digest
        || digest("candidate")? != candidate.digest
    {
        return None;
    }
    let verdict = match value.get("verdict")?.as_str()? {
        "PASS" => Verdict::Pass,
        "SHARED_RED" => Verdict::SharedRed,
        "NEW_RED" => Verdict::NewRed,
        _ => return None,
    };
    Some((verdict, value))
}

/// Decide one consumer from its directory, recording a new verdict.
pub(crate) fn decide(directory: &Path) -> Outcome {
    let load = |side: &str| records::load(&directory.join(side));
    let (deployed, candidate) = match (load("deployed"), load("candidate")) {
        (Err(error), _) | (_, Err(error)) => return Outcome::Incomparable(error.to_string()),
        (Ok(Loaded::Pending(why)), _) | (_, Ok(Loaded::Pending(why))) => {
            return Outcome::Pending(why);
        }
        (Ok(Loaded::Run(deployed)), Ok(Loaded::Run(candidate))) => (deployed, candidate),
    };
    let named = directory.file_name().map(|name| name.to_string_lossy().into_owned());
    if named.as_deref() != Some(candidate.record.consumer.as_str()) {
        return Outcome::Incomparable(format!(
            "{} holds runs of consumer {:?}",
            directory.display(),
            candidate.record.consumer
        ));
    }
    if let Some(why) = incomparable(&deployed.record, &candidate.record) {
        return Outcome::Incomparable(why);
    }
    let path = directory.join(VERDICT_FILE);
    if let Some((verdict, report)) = recorded(&path, &deployed, &candidate) {
        return Outcome::Decided { verdict, reused: true, report };
    }
    let comparison = compare(&deployed, &candidate);
    let report = report(&deployed, &candidate, &comparison);
    let mut bytes = match serde_json::to_vec_pretty(&report) {
        Ok(bytes) => bytes,
        Err(error) => return Outcome::Incomparable(format!("cannot encode the verdict: {error}")),
    };
    bytes.push(b'\n');
    if let Err(error) = crate::durable_io::atomic_write_private(&path, &bytes) {
        return Outcome::Incomparable(format!("cannot record {}: {error}", path.display()));
    }
    Outcome::Decided { verdict: comparison.verdict, reused: false, report }
}

/// The consumers a state directory holds, with every required one present.
pub(crate) fn consumers(state: &Path, required: &[String]) -> io::Result<Vec<String>> {
    let mut names = required.iter().cloned().collect::<BTreeSet<_>>();
    for entry in std::fs::read_dir(state)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            names.insert(entry.file_name().to_string_lossy().into_owned());
        }
    }
    Ok(names.into_iter().collect())
}
