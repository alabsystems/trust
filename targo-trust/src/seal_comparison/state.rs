//! The comparison's state on disk, one directory per consumer:
//!
//! ```text
//! <state>/<consumer>/deployed/run.json     the deployed seal's run
//! <state>/<consumer>/candidate/run.json    the candidate's run
//! <state>/<consumer>/verdict.json          written here
//! ```
//!
//! A verdict is recorded with the digest of the bytes it was decided from. A
//! later invocation derives the verdict again from the saved runs. It keeps
//! the report on disk if it matches the newly computed report byte for byte.

use std::collections::BTreeSet;
use std::io;
use std::path::Path;

use serde_json::{Value, json};

use super::records::{self, Loaded, Run};
use super::{Comparison, Verdict, compare, incomparable};
use crate::audit_comparison::parse::read_bytes;

pub(crate) const VERDICT_SCHEMA: &str = "trust.seal-consumer-verdict.v1";
const VERDICT_FILE: &str = "verdict.json";

/// One consumer's line of the table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Outcome {
    Decided {
        verdict: Verdict,
        /// The recorded report is byte-identical to the recomputed report.
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
    if let Some(why) = incomparable(&deployed, &candidate) {
        return Outcome::Incomparable(why);
    }
    let path = directory.join(VERDICT_FILE);
    let comparison = compare(&deployed, &candidate);
    let report = report(&deployed, &candidate, &comparison);
    let mut bytes = match serde_json::to_vec_pretty(&report) {
        Ok(bytes) => bytes,
        Err(error) => return Outcome::Incomparable(format!("cannot encode the verdict: {error}")),
    };
    bytes.push(b'\n');
    // The saved report is an output. Only this invocation's comparison can
    // decide the verdict and disclosures.
    if matches!(read_bytes(&path), Ok(recorded) if recorded == bytes) {
        return Outcome::Decided { verdict: comparison.verdict, reused: true, report };
    }
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
