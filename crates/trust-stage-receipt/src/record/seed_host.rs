//! The seed host record a receipt's seed capture selected, and the status it allows.
//!
//! The twin of `selected_host_record`, `fixed_point_lines` and the checks between the
//! release-status check and the commit check of `lines` in
//! scripts/lib/stage_receipt_provenance.py, with the same words. A seed whose selected
//! host record is the fixed-point kind (docs/PLAN.md PKG-S6) is graded
//! `unpinned-root-seed-ready`, never a release status, and that grade is given to
//! nothing else. tests/data/fixed-point-cases.json holds both readers to the same
//! verdicts on the same receipts. Nothing here reads a file: what the record says is
//! the receipt's own statement.

use crate::{Refusal, Result, Value, release_status_holds, repr};

pub(super) const ACCEPTED_STATUSES: [&str; 4] =
    ["candidate-ready", "internal-release-ready", "release-ready", UNPINNED_ROOT_STATUS];
const RELEASE_STATUSES: [&str; 2] = ["internal-release-ready", "release-ready"];
const UNPINNED_ROOT_STATUS: &str = "unpinned-root-seed-ready";
const FIXED_POINT_HOST_RECORD_SCHEMA: &str = "trust-seed-fixed-point-host-record-v1";
const FIXED_POINT_ADMISSION_KIND: &str = "fixed-point-unpinned-root";
/// The only values the fixed-point validator admits (scripts/seed_fixed_point.py).
const FIXED_POINT_DISCLOSED: [(&str, &str); 4] = [
    ("root", "unpinned-host-chain"),
    ("predecessor_pin", "none"),
    ("double_compile_diverse", "false"),
    ("stock_built_ancestor", "inferred-no-receipt"),
];
/// A single-host seed ledger never admitted one of these hosts.
const LINUX_SEED_HOSTS: [&str; 2] = ["aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"];
const HOST_RECORDS: &str = "bootstrap_lineage.validated_seed.authority.seed_ledger.host_records";

/// The seed admission lines of an accepted receipt: the fixed-point kind's two, or none.
///
/// Refuses a fixed-point seed with a release status, `unpinned-root-seed-ready` for any
/// other seed or for one that was not freshly materialized, a fixed-point record whose
/// admission or disclosure is not the validator's, host records that name no readable
/// selection or one that is not the receipt's host, and a seed with no host record whose
/// host is Linux or is not a host name.
/// `mode`, `status` and `materialization` are the ones `validate` already checked.
pub(super) fn admission_lines(
    receipt: &Value,
    mode: &str,
    status: &str,
    materialization: &Value,
) -> Result<Vec<String>> {
    let lineage = &receipt["bootstrap_lineage"];
    let host = &receipt["host"];
    let record =
        if mode == "seed" { selected_host_record(&lineage["validated_seed"], host)? } else { None };
    if mode == "seed" && record.is_none() {
        // A host that is not a name cannot be told from a Linux one, so its seed is
        // refused, never read as from some other host.
        let Some(host) = host.as_str() else {
            return Err(Refusal(format!(
                "its seed lineage holds no host record and its host is {}, not a host name: whether only its own host record could admit that seed cannot be told",
                repr(host)
            )));
        };
        if LINUX_SEED_HOSTS.contains(&host) {
            return Err(Refusal(format!(
                "its seed lineage on {host} holds no host record (a single-host seed ledger), which never admits a Linux host: a Linux seed is admitted only through its own host record (docs/PLAN.md PKG-S6), and the recreator refuses this one"
            )));
        }
    }
    let fixed_point =
        record.is_some_and(|record| record["schema"] == FIXED_POINT_HOST_RECORD_SCHEMA);
    if fixed_point && RELEASE_STATUSES.contains(&status) {
        return Err(Refusal(format!(
            "status is {status}, a release status, while its seed's selected host record is the fixed-point kind, which is graded {UNPINNED_ROOT_STATUS} and never a release"
        )));
    }
    if status == UNPINNED_ROOT_STATUS && !fixed_point {
        let seed = match record {
            Some(record) => format!("a {} record", record["schema"].as_str().unwrap_or_default()),
            None => "no such record".into(),
        };
        return Err(Refusal(format!(
            "status is {status}, which only a build from a seed whose selected host record is the fixed-point kind is given; this receipt's seed is {seed}"
        )));
    }
    let trust = &lineage["trust_from_trust"];
    if status == UNPINNED_ROOT_STATUS
        && !release_status_holds(&lineage["mode"], trust, materialization)
    {
        return Err(Refusal(format!(
            "status is {status}, which needs a freshly materialized Trust seed, while its lineage says mode {mode}, trust_from_trust {}, seed materialization {}",
            trust.as_bool().unwrap_or_default(),
            materialization.as_str().unwrap_or_default()
        )));
    }
    match record {
        Some(record) if fixed_point => fixed_point_lines(record),
        _ => Ok(Vec::new()),
    }
}

/// The host record a seed lineage's capture selected for `host` (the receipt's own), or
/// None when the capture holds no host records (a single-host ledger).
///
/// Refuses host records that name no readable selected record, a selection that is not
/// `host`'s, and a record of another kind that carries the fixed-point kind's admission
/// or disclosure: the kind of the seed would then be unknown or misstated.
fn selected_host_record<'a>(seed: &'a Value, host: &Value) -> Result<Option<&'a Value>> {
    let host_records = &seed["authority"]["seed_ledger"]["host_records"];
    if host_records.is_null() {
        return Ok(None);
    }
    // A record that is not an object indexes as null, so it has no schema either.
    let selected = host_records["selected_host"].as_str();
    let record = selected.and_then(|selected| host_records["records"].get(selected));
    let (Some(selected), Some(record), Some(schema)) =
        (selected, record, record.and_then(|record| record["schema"].as_str()))
    else {
        return Err(Refusal(format!("{HOST_RECORDS} names no selected host record with a schema")));
    };
    if host.as_str() != Some(selected) {
        return Err(Refusal(format!(
            "{HOST_RECORDS}.selected_host is {}, not this receipt's host {}: a seed capture selects its own build host's record and no other",
            repr(&host_records["selected_host"]),
            repr(host)
        )));
    }
    if record["host"].as_str() != Some(selected) {
        return Err(Refusal(format!(
            "{HOST_RECORDS}.records[{}] says host {}: the selected record is not that host's",
            repr(&host_records["selected_host"]),
            repr(&record["host"])
        )));
    }
    if schema != FIXED_POINT_HOST_RECORD_SCHEMA
        && (record.get("root_disclosure").is_some()
            || record["admission_kind"] == FIXED_POINT_ADMISSION_KIND)
    {
        return Err(Refusal(format!(
            "{HOST_RECORDS}.records[{}] is a {schema} record and carries the fixed-point kind's root_disclosure or admission_kind, which only that kind is admitted with",
            repr(&host_records["selected_host"])
        )));
    }
    Ok(Some(record))
}

/// The two lines of a seed whose selected host record is the fixed-point kind: its
/// admission, and what its root_disclosure says of the root, in the validator's words.
fn fixed_point_lines(record: &Value) -> Result<Vec<String>> {
    if record["admission_kind"] != FIXED_POINT_ADMISSION_KIND {
        return Err(Refusal(format!(
            "its seed's fixed-point host record has admission_kind {}, not {FIXED_POINT_ADMISSION_KIND}",
            repr(&record["admission_kind"])
        )));
    }
    let disclosure = &record["root_disclosure"];
    if !disclosure.is_object() {
        return Err(Refusal(
            "its seed's fixed-point host record carries no root_disclosure table".into(),
        ));
    }
    for (key, value) in FIXED_POINT_DISCLOSED {
        if disclosure[key] != value {
            return Err(Refusal(format!(
                "its seed's fixed-point host record discloses {key} {}; the only value a fixed point is admitted with is {value}",
                repr(&disclosure[key])
            )));
        }
    }
    let disclosed = FIXED_POINT_DISCLOSED.map(|(key, value)| format!("{key}={value}")).join(" ");
    Ok(vec![
        format!("stage_receipt_seed_admission={FIXED_POINT_ADMISSION_KIND}"),
        format!("stage_receipt_seed_root_disclosure={disclosed}"),
    ])
}
