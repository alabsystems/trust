//! Source-bound, complete AY census comparison for the native paired owner.
//!
//! Saved verdicts are observations, never proofs or evidence of execution. This
//! consumer retains the original pair's source binding and cannot advance its
//! execution stages. Only an existing solver-discharged identity earns credit;
//! denominator shrinkage and structural verdicts are disclosed separately.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::pair::FileIdentity;
use crate::receipts::ReceiptCheckedPair;
use crate::{Git, Result, canonical_hex, refusal, tree};

const MAX_CENSUS_BYTES: u64 = 16 * 1024 * 1024;
const CRATE_PATH: &str = "crates/ay-proof-common";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum Class {
    ProvedSolver,
    ProvedStructural,
    Failed,
    Unknown,
    RuntimeChecked,
    Skipped,
}

#[derive(Deserialize)]
struct Entry {
    class: Class,
    absent_callee: Option<String>,
    vcgen_truncated_function: Option<bool>,
}

#[derive(Clone, Deserialize, Serialize)]
struct Verdicts {
    obligations: u64,
    proved: u64,
    proved_solver_discharged: u64,
    proved_structural_no_obligations: u64,
    kernel_certified: u64,
    functions_fully_verified: u64,
    failed: u64,
    unknown: u64,
    runtime_checked: u64,
    timed_out: u64,
}

#[derive(Deserialize)]
struct Metadata {
    git_commit: String,
    crate_sources_tree: String,
    crate_sources_clean_at_commit: bool,
    crate_sources_path: String,
}

#[derive(Deserialize)]
struct Ledger {
    denominator_is_complete: bool,
    vcgen_truncated_functions: u64,
    vcgen_truncated_function_names: Vec<String>,
    total: u64,
    agrees_with_crate_rollup: bool,
    classes: BTreeMap<Class, u64>,
    entries: BTreeMap<String, Entry>,
}

#[derive(Deserialize)]
struct StrictLane {
    verdict_census_matches_advisory: bool,
}

#[derive(Deserialize)]
struct Document {
    schema_version: String,
    crate_name: String,
    metadata: Metadata,
    verdicts: Verdicts,
    obligation_ledger: Ledger,
    strict_lane: StrictLane,
}

#[derive(Serialize)]
struct SourceBinding {
    commit: String,
    crate_sources_tree: String,
    crate_sources_path: &'static str,
}

/// A new native observation. It has no deserializer and confers no proof,
/// execution, source-writer, build, candidate or publication authority.
#[derive(Serialize)]
pub struct CensusComparison {
    schema: &'static str,
    claim_scope: &'static str,
    source: SourceBinding,
    control: CensusObservation,
    candidate: CensusObservation,
    accounting: Accounting,
    regressions: Vec<String>,
}

impl CensusComparison {
    pub fn regressions(&self) -> &[String] {
        &self.regressions
    }
}

#[derive(Serialize)]
struct CensusObservation {
    input: FileIdentity,
    verdicts: Verdicts,
    complete_obligation_identities: usize,
}

#[derive(Serialize)]
struct Delta {
    before: u64,
    after: u64,
    delta: i128,
}

fn delta(before: u64, after: u64) -> Delta {
    Delta { before, after, delta: i128::from(after) - i128::from(before) }
}

#[derive(Default, Serialize)]
struct Movement {
    obligations_proved: usize,
    obligations_proved_detail: Vec<String>,
    obligations_proof_lost: usize,
    obligations_proof_lost_detail: Vec<String>,
    obligations_removed_total: usize,
    obligations_removed_by_summary: usize,
    obligations_removed_by_summary_detail: Vec<String>,
    obligations_removed_unattributed: usize,
    obligations_removed_unattributed_detail: Vec<String>,
    obligations_removed_by_previous_class: BTreeMap<Class, usize>,
    obligations_newly_asked: usize,
    obligations_newly_asked_by_class: BTreeMap<Class, usize>,
}

#[derive(Serialize)]
struct Accounting {
    mode: &'static str,
    floors_only_a_prover_can_raise: BTreeMap<&'static str, Delta>,
    disclosed_never_credited: BTreeMap<&'static str, Delta>,
    movement: Movement,
}

impl ReceiptCheckedPair {
    /// Compare retained census files against the exact AY source in this live
    /// pair. Both full input rebindings run even when reading/parsing/comparison
    /// fails. Later native workload stages must additionally bind these bytes
    /// to their real producer, original admitted attempts and actual outcomes.
    pub fn compare_ay_censuses(
        &self,
        git: &impl Git,
        control: &Path,
        candidate: &Path,
    ) -> Result<CensusComparison> {
        self.check_unchanged(git)?;
        let result = (|| {
            let ay =
                self.snapshot().sources.get("ay").ok_or_else(|| refusal("missing AY source"))?;
            let tree = git.probe(&ay.path, &["rev-parse", "HEAD:crates/ay-proof-common"])?;
            let tree = tree.strip_suffix(b"\n").unwrap_or(&tree);
            let tree = std::str::from_utf8(tree).map_err(|_| refusal("non-UTF8 AY crate tree"))?;
            if !canonical_hex(tree, 40) {
                return Err(refusal("AY crate tree is not one canonical Git object ID"));
            }
            let source = SourceBinding {
                commit: ay.commit.clone(),
                crate_sources_tree: tree.into(),
                crate_sources_path: CRATE_PATH,
            };
            let before = CensusFile::read(control)?;
            let after = CensusFile::read(candidate)?;
            let base = parse(&before.bytes, &source)?;
            let current = parse(&after.bytes, &source)?;
            let (accounting, regressions) = compare(&base, &current);
            before.check_current()?;
            after.check_current()?;
            Ok(CensusComparison {
                schema: "trust.paired-census-comparison.v1",
                claim_scope: "complete source-bound saved census observations and identity-aware accounting only; no execution, kernel checking, proof, candidate qualification or publication authority",
                source,
                control: before.observation(base.verdicts, base.obligation_ledger.entries.len()),
                candidate: after
                    .observation(current.verdicts, current.obligation_ledger.entries.len()),
                accounting,
                regressions,
            })
        })();
        match (result, self.check_unchanged(git)) {
            (Ok(report), Ok(())) => Ok(report),
            (Err(error), Ok(())) | (Ok(_), Err(error)) => Err(error),
            (Err(error), Err(drift)) => {
                Err(refusal(format!("{error}; original pair also changed: {drift}")))
            }
        }
    }
}

struct CensusFile {
    path: std::path::PathBuf,
    resolved_path: std::path::PathBuf,
    file: fs::File,
    stamp: tree::Fingerprint,
    bytes: Vec<u8>,
}

impl CensusFile {
    fn read(path: &Path) -> Result<Self> {
        let metadata = fs::symlink_metadata(path)?;
        if !metadata.is_file() || metadata.len() > MAX_CENSUS_BYTES {
            return Err(refusal("census must be a bounded exact regular file"));
        }
        let stamp = tree::Fingerprint::of(&metadata);
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(path)?;
        if tree::Fingerprint::of(&file.metadata()?) != stamp {
            return Err(refusal("census changed before opening"));
        }
        let mut bytes = Vec::new();
        (&mut file).take(MAX_CENSUS_BYTES + 1).read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MAX_CENSUS_BYTES {
            return Err(refusal("census exceeds the native input bound"));
        }
        let resolved_path = fs::canonicalize(path)?;
        let input = Self { path: path.into(), resolved_path, file, stamp, bytes };
        input.check_current()?;
        Ok(input)
    }

    fn check_current(&self) -> Result<()> {
        if tree::Fingerprint::of(&self.file.metadata()?) != self.stamp
            || tree::Fingerprint::of(&fs::symlink_metadata(&self.path)?) != self.stamp
            || tree::Fingerprint::of(&fs::symlink_metadata(&self.resolved_path)?) != self.stamp
        {
            return Err(refusal("census changed while comparing"));
        }
        Ok(())
    }

    fn observation(self, verdicts: Verdicts, count: usize) -> CensusObservation {
        CensusObservation {
            input: FileIdentity {
                path: self.path,
                resolved_path: self.resolved_path,
                sha256: tree::hash_bytes(&self.bytes),
                link_text: None,
            },
            verdicts,
            complete_obligation_identities: count,
        }
    }
}

fn parse(bytes: &[u8], source: &SourceBinding) -> Result<Document> {
    if bytes.len() as u64 > MAX_CENSUS_BYTES {
        return Err(refusal("census exceeds the native input bound"));
    }
    // Check every object, including unknown observational metadata, before the
    // typed decoder can discard any fields. Never accept last-key-wins JSON.
    serde_json::from_slice::<unique::Document>(bytes)
        .map_err(|error| refusal(format!("invalid census JSON: {error}")))?;
    let doc: Document = serde_json::from_slice(bytes)
        .map_err(|error| refusal(format!("invalid typed census: {error}")))?;
    if doc.schema_version != "ay.trust.ratchet.v3"
        || doc.crate_name != "ay-proof-common"
        || doc.metadata.git_commit != source.commit
        || doc.metadata.crate_sources_tree != source.crate_sources_tree
        || !doc.metadata.crate_sources_clean_at_commit
        || doc.metadata.crate_sources_path != CRATE_PATH
    {
        return Err(refusal("census schema/source differs from the original frozen AY"));
    }
    let ledger = &doc.obligation_ledger;
    if !ledger.denominator_is_complete
        || ledger.vcgen_truncated_functions != 0
        || !ledger.vcgen_truncated_function_names.is_empty()
        || ledger.entries.values().any(|entry| entry.vcgen_truncated_function == Some(true))
    {
        return Err(refusal("census-completeness: AY denominator is incomplete or truncated"));
    }
    if !doc.strict_lane.verdict_census_matches_advisory {
        return Err(refusal("census-lane-agreement: strict/advisory verdict censuses diverge"));
    }
    if doc.verdicts.obligations == 0
        || ledger.entries.len() as u64 != doc.verdicts.obligations
        || ledger.total != doc.verdicts.obligations
        || !ledger.agrees_with_crate_rollup
        || ledger.entries.keys().any(|key| key.is_empty())
    {
        return Err(refusal("census ledger is empty or differs from its full denominator"));
    }
    let mut counts = BTreeMap::<Class, u64>::new();
    for entry in ledger.entries.values() {
        *counts.entry(entry.class).or_default() += 1;
    }
    let count = |class| counts.get(&class).copied().unwrap_or(0);
    let v = &doc.verdicts;
    if ledger.classes != counts
        || v.proved_solver_discharged != count(Class::ProvedSolver)
        || v.proved_structural_no_obligations != count(Class::ProvedStructural)
        || u128::from(v.proved)
            != u128::from(v.proved_solver_discharged)
                + u128::from(v.proved_structural_no_obligations)
        || v.failed != count(Class::Failed)
        || v.unknown != count(Class::Unknown) + count(Class::Skipped)
        || v.runtime_checked != count(Class::RuntimeChecked)
        || v.timed_out > v.unknown
        || v.kernel_certified > v.proved_solver_discharged
    {
        return Err(refusal("census ledger classes disagree with the verdict rollup"));
    }
    Ok(doc)
}

fn compare(base: &Document, current: &Document) -> (Accounting, Vec<String>) {
    let before = &base.obligation_ledger.entries;
    let after = &current.obligation_ledger.entries;
    let still_charged = after
        .values()
        .filter_map(|entry| entry.absent_callee.as_deref())
        .filter(|callee| !callee.is_empty())
        .collect::<BTreeSet<_>>();
    let mut movement = Movement::default();
    for (key, entry) in after {
        match before.get(key) {
            None => *movement.obligations_newly_asked_by_class.entry(entry.class).or_default() += 1,
            Some(was) if entry.class == Class::ProvedSolver && was.class != Class::ProvedSolver => {
                movement.obligations_proved_detail.push(key.clone())
            }
            _ => (),
        }
    }
    for (key, entry) in before {
        match after.get(key) {
            None => {
                *movement.obligations_removed_by_previous_class.entry(entry.class).or_default() +=
                    1;
                match entry.absent_callee.as_deref().filter(|callee| !callee.is_empty()) {
                    Some(callee) if !still_charged.contains(callee) => movement
                        .obligations_removed_by_summary_detail
                        .push(format!("{key}  <- {callee}")),
                    _ => movement.obligations_removed_unattributed_detail.push(key.clone()),
                }
                if entry.class == Class::ProvedSolver {
                    movement
                        .obligations_proof_lost_detail
                        .push(format!("{key}  (REMOVED while proved)"));
                }
            }
            Some(now) if entry.class == Class::ProvedSolver && now.class != Class::ProvedSolver => {
                let class = serde_json::to_value(now.class).expect("closed class serializes");
                movement
                    .obligations_proof_lost_detail
                    .push(format!("{key}  (proved_solver -> {})", class.as_str().unwrap()));
            }
            _ => (),
        }
    }
    movement.obligations_proved = movement.obligations_proved_detail.len();
    movement.obligations_proof_lost = movement.obligations_proof_lost_detail.len();
    movement.obligations_removed_by_summary = movement.obligations_removed_by_summary_detail.len();
    movement.obligations_removed_unattributed =
        movement.obligations_removed_unattributed_detail.len();
    movement.obligations_removed_total =
        movement.obligations_removed_by_previous_class.values().sum();
    movement.obligations_newly_asked = movement.obligations_newly_asked_by_class.values().sum();
    let b = &base.verdicts;
    let c = &current.verdicts;
    let floors = BTreeMap::from([
        ("proved_solver_discharged", delta(b.proved_solver_discharged, c.proved_solver_discharged)),
        ("kernel_certified", delta(b.kernel_certified, c.kernel_certified)),
    ]);
    let disclosed = BTreeMap::from([
        ("obligations", delta(b.obligations, c.obligations)),
        ("proved_including_structural", delta(b.proved, c.proved)),
        (
            "proved_structural_no_obligations",
            delta(b.proved_structural_no_obligations, c.proved_structural_no_obligations),
        ),
        ("functions_fully_verified", delta(b.functions_fully_verified, c.functions_fully_verified)),
        ("failed", delta(b.failed, c.failed)),
        ("unknown", delta(b.unknown, c.unknown)),
        ("runtime_checked", delta(b.runtime_checked, c.runtime_checked)),
        ("timed_out", delta(b.timed_out, c.timed_out)),
    ]);
    let mut regressions = Vec::new();
    if movement.obligations_proof_lost != 0 {
        regressions.push(format!(
            "{} solver-discharged obligation(s) no longer proved: {}",
            movement.obligations_proof_lost,
            movement.obligations_proof_lost_detail.join("; ")
        ));
    }
    for (name, d) in &floors {
        if d.delta < 0 {
            regressions.push(format!("{name} FELL {} -> {} (proof floor)", d.before, d.after));
        }
    }
    if c.timed_out > b.timed_out {
        regressions.push(format!("timed_out ROSE {} -> {}", b.timed_out, c.timed_out));
    }
    for (name, class) in [("failed", Class::Failed), ("unknown", Class::Unknown)] {
        let d = &disclosed[name];
        let explained = movement.obligations_newly_asked_by_class.get(&class).copied().unwrap_or(0)
            + if class == Class::Unknown {
                movement.obligations_newly_asked_by_class.get(&Class::Skipped).copied().unwrap_or(0)
            } else {
                0
            };
        if d.delta > explained as i128 {
            regressions.push(format!(
                "{name} ROSE {} -> {}, only {explained} explained by newly-emitted obligations",
                d.before, d.after
            ));
        }
    }
    (
        Accounting {
            mode: "identity (schema v3 ledger on both sides)",
            floors_only_a_prover_can_raise: floors,
            disclosed_never_credited: disclosed,
            movement,
        },
        regressions,
    )
}

#[cfg(test)]
mod tests;
mod unique;
