//! Statements about LLVM, checked for consistency rather than re-derived here.

use crate::{Refusal, Result, Value, exact_keys, hash, is_hex, json, repr};

pub const IDENTITY_SCHEMA: &str = "trust.llvm-identity.v1";
pub const SOURCE_IDENTITY_SCHEMA: &str = "trust.llvm-source-identity.v1";
pub const BUILD_RECORD_SCHEMA: &str = "trust.llvm-build-record.v1";
pub const SOURCE_TREE: &str = "src/llvm-project";
const IDENTITY_KEYS: &[&str] = &[
    "schema",
    "mode",
    "provenance",
    "identity_stated",
    "reasons",
    "source_identity_sha256",
    "source_paths",
    "output_dirs",
    "output_fingerprint_sha256",
    "build_record",
];
const BUILD_RECORD_KEYS: &[&str] = &[
    "schema",
    "built_at_commit",
    "host",
    "source_identity_sha256",
    "source_paths",
    "bootstrap_config_sha256",
    "native_authority_sha256",
    "output_fingerprint_sha256",
];

fn sorted_keys(keys: &[&str]) -> String {
    let mut keys = keys.to_vec();
    keys.sort_unstable();
    keys.join(", ")
}

pub fn source_identity_sha256(rows: &Value) -> String {
    hash(
        format!(
            "{{\"paths\":{},\"schema\":\"{SOURCE_IDENTITY_SCHEMA}\"}}",
            json::ascii_canonical(rows)
        )
        .as_bytes(),
    )
}

fn source_rows_errors(rows: &Value, where_: &str) -> Vec<String> {
    let Some(rows) = rows.as_array().filter(|rows| !rows.is_empty()) else {
        return vec![format!("{where_} is not a non-empty list")];
    };
    let mut paths = Vec::new();
    for row in rows {
        if !exact_keys(row, &["path", "type", "oid"])
            || row["path"].as_str().is_none_or(str::is_empty)
            || !matches!(row["type"].as_str(), Some("tree" | "blob" | "commit"))
            || !is_hex(&row["oid"], &[40, 64])
        {
            return vec![format!(
                "{where_} holds a row that is not a path, an object type and an object id"
            )];
        }
        paths.push(row["path"].as_str().unwrap());
    }
    if paths.windows(2).any(|pair| pair[0] >= pair[1]) {
        return vec![format!("{where_} is not sorted by path without a repeat")];
    }
    if !paths.contains(&SOURCE_TREE) {
        return vec![format!("{where_} does not name {SOURCE_TREE}")];
    }
    Vec::new()
}

pub fn build_record_errors(value: &Value) -> Vec<String> {
    if !value.is_object() {
        return vec!["the LLVM build record is not an object".into()];
    }
    let mut errors = Vec::new();
    if !exact_keys(value, BUILD_RECORD_KEYS) {
        errors.push(format!(
            "the LLVM build record does not hold exactly the keys {}",
            sorted_keys(BUILD_RECORD_KEYS)
        ));
    }
    if value["schema"] != BUILD_RECORD_SCHEMA {
        errors.push(format!("the LLVM build record's schema is not {BUILD_RECORD_SCHEMA}"));
    }
    if !is_hex(&value["built_at_commit"], &[40, 64]) {
        errors.push("the LLVM build record's built_at_commit is not a full commit id".into());
    }
    if value["host"].as_str().is_none_or(str::is_empty) {
        errors.push("the LLVM build record's host is not a host triple".into());
    }
    for key in [
        "source_identity_sha256",
        "bootstrap_config_sha256",
        "native_authority_sha256",
        "output_fingerprint_sha256",
    ] {
        if !is_hex(&value[key], &[64]) {
            errors.push(format!("the LLVM build record's {key} is not a sha256"));
        }
    }
    let row_errors =
        source_rows_errors(&value["source_paths"], "the LLVM build record's source_paths");
    if row_errors.is_empty()
        && value["source_identity_sha256"].as_str()
            != Some(&source_identity_sha256(&value["source_paths"]))
    {
        errors.push("the LLVM build record's source_identity_sha256 is not the identity of its source_paths".into());
    }
    errors.extend(row_errors);
    errors
}

pub fn identity_errors(value: &Value, receipt: &Value) -> Vec<String> {
    if !value.is_object() {
        return vec!["llvm_identity is not an object".into()];
    }
    let mut errors = Vec::new();
    if !exact_keys(value, IDENTITY_KEYS) {
        errors.push(format!(
            "llvm_identity does not hold exactly the keys {}",
            sorted_keys(IDENTITY_KEYS)
        ));
    }
    if value["schema"] != IDENTITY_SCHEMA {
        errors.push(format!("llvm_identity.schema is not {IDENTITY_SCHEMA}"));
    }
    let mode = value["mode"].as_str();
    let provenance = value["provenance"].as_str();
    let allowed: &[&str] = match mode {
        Some("in-tree") => &["built-in-this-run", "reused", "changed-in-this-run", "unknown"],
        Some("external") => &["external"],
        Some("unknown") => &["unknown"],
        _ => &[],
    };
    if allowed.is_empty() {
        errors.push(format!(
            "llvm_identity.mode is {}, not one of in-tree, external, unknown",
            repr(&value["mode"])
        ));
    } else if provenance.is_none_or(|p| !allowed.contains(&p)) {
        errors.push(format!(
            "llvm_identity.provenance is {}; a record of mode {} says one of {}",
            repr(&value["provenance"]),
            mode.unwrap(),
            allowed.join(", ")
        ));
    }
    let stated = value["identity_stated"].as_bool();
    if stated.is_none() {
        errors.push("llvm_identity.identity_stated is neither true nor false".into());
    }
    match value["reasons"].as_array() {
        Some(reasons)
            if reasons.iter().all(|reason| reason.as_str().is_some_and(|s| !s.is_empty())) =>
        {
            if stated == Some(!reasons.is_empty()) {
                errors.push("llvm_identity.identity_stated and llvm_identity.reasons disagree: an identity is stated exactly when no reason against it is given".into());
            }
        }
        _ => errors.push("llvm_identity.reasons is not a list of sentences".into()),
    }
    let rows = &value["source_paths"];
    let identity = &value["source_identity_sha256"];
    if rows.is_empty_array() && identity.is_null() {
        if stated == Some(true) {
            errors.push("llvm_identity states an identity without a source identity".into());
        }
    } else {
        let row_errors = source_rows_errors(rows, "llvm_identity.source_paths");
        if row_errors.is_empty() && identity.as_str() != Some(&source_identity_sha256(rows)) {
            errors.push("llvm_identity.source_identity_sha256 is not the identity of llvm_identity.source_paths".into());
        }
        errors.extend(row_errors);
    }
    let output_dirs = &value["output_dirs"];
    if output_dirs
        .as_array()
        .is_none_or(|dirs| dirs.iter().any(|dir| dir.as_str().is_none_or(str::is_empty)))
    {
        errors.push("llvm_identity.output_dirs is not a list of paths".into());
    }
    let fingerprint = &value["output_fingerprint_sha256"];
    if !fingerprint.is_null() && !is_hex(fingerprint, &[64]) {
        errors.push("llvm_identity.output_fingerprint_sha256 is neither null nor a sha256".into());
    }
    let record = &value["build_record"];
    if !record.is_null() {
        errors.extend(build_record_errors(record));
    }
    if !errors.is_empty() {
        return errors;
    }
    let mode = mode.expect("validated LLVM mode");
    let provenance = provenance.expect("validated LLVM provenance");
    let stated = stated.expect("validated LLVM identity flag");
    if mode == "external" {
        if stated {
            errors.push("llvm_identity states the identity of an external LLVM: which sources an LLVM linked through --llvm-config was built from is never established".into());
        }
        if !record.is_null()
            || !fingerprint.is_null()
            || output_dirs.as_array().is_some_and(|v| !v.is_empty())
        {
            errors.push(
                "llvm_identity of an external LLVM carries an in-tree output or build record"
                    .into(),
            );
        }
        if !rows.is_empty_array() || !identity.is_null() {
            errors.push("llvm_identity of an external LLVM carries a source identity: this checkout's LLVM sources do not describe an LLVM linked through --llvm-config".into());
        }
    } else if !stated {
        if !record.is_null() {
            errors.push(
                "llvm_identity quotes a build record for an identity it does not state".into(),
            );
        }
    } else if mode == "in-tree" {
        if !["built-in-this-run", "reused"].contains(&provenance) {
            errors.push(format!(
                "llvm_identity states the identity of an LLVM whose provenance is {provenance}"
            ));
        }
        if output_dirs.as_array().is_some_and(Vec::is_empty) || fingerprint.is_null() {
            errors.push(
                "llvm_identity states the identity of an in-tree LLVM without its output".into(),
            );
        }
        if record.is_null() {
            errors.push(
                "llvm_identity states the identity of an in-tree LLVM without a build record"
                    .into(),
            );
        } else {
            for (what, mine, recorded) in [
                ("source identity", identity, &record["source_identity_sha256"]),
                ("output", fingerprint, &record["output_fingerprint_sha256"]),
                ("host", &receipt["host"], &record["host"]),
                (
                    "bootstrap config",
                    &receipt["bootstrap_lineage"]["config_sha256"],
                    &record["bootstrap_config_sha256"],
                ),
                (
                    "native tool and SDK authority",
                    &receipt["build_authority"]["authority_sha256"],
                    &record["native_authority_sha256"],
                ),
            ] {
                if mine != recorded {
                    errors.push(format!(
                        "llvm_identity's build record is for another {what} than this receipt's"
                    ));
                }
            }
            if provenance == "built-in-this-run"
                && record["built_at_commit"] != receipt["compiler"]["source_commit"]
            {
                errors.push("llvm_identity says LLVM was built in this run, and its build record names another commit than this receipt's".into());
            }
        }
    } else {
        errors.push("llvm_identity states the identity of an LLVM of unknown mode".into());
    }
    errors
}

pub(crate) fn lines(receipt: &Value) -> Result<Vec<String>> {
    let Some(value) = receipt.get("llvm_identity") else {
        return Ok(vec!["stage_receipt_llvm=not-recorded".into()]);
    };
    let errors = identity_errors(value, receipt);
    if !errors.is_empty() {
        return Err(Refusal(errors.join("; ")));
    }
    let in_tree = value["mode"] == "in-tree";
    let field = |key: &str| {
        if in_tree { value[key].as_str().unwrap_or("not-recorded") } else { "not-recorded" }
    };
    let source_tree = if in_tree {
        value["source_paths"]
            .as_array()
            .and_then(|rows| rows.iter().find(|row| row["path"] == SOURCE_TREE))
            .and_then(|row| row["oid"].as_str())
            .unwrap_or("not-recorded")
    } else {
        "not-recorded"
    };
    let built_at = if in_tree {
        value["build_record"]["built_at_commit"].as_str().unwrap_or("not-recorded")
    } else {
        "not-recorded"
    };
    Ok(vec![
        format!("stage_receipt_llvm={}", value["mode"].as_str().unwrap()),
        format!(
            "stage_receipt_llvm_identity={}",
            if value["identity_stated"] == true { "stated" } else { "not-stated" }
        ),
        format!("stage_receipt_llvm_provenance={}", value["provenance"].as_str().unwrap()),
        format!("stage_receipt_llvm_source_sha256={}", field("source_identity_sha256")),
        format!("stage_receipt_llvm_source_tree={source_tree}"),
        format!("stage_receipt_llvm_built_at_commit={built_at}"),
        format!("stage_receipt_llvm_output_sha256={}", field("output_fingerprint_sha256")),
    ])
}

pub(crate) fn unstated(receipt: &Value) -> String {
    let Some(value) = receipt.get("llvm_identity") else {
        return "its tool-provenance.json holds no llvm_identity record: it was written by a recreator from before 2026-10-13".into();
    };
    if value["identity_stated"] == true {
        return String::new();
    }
    format!(
        "its tool-provenance.json says the identity is not stated (mode {}, provenance {}): {}",
        value["mode"].as_str().unwrap(),
        value["provenance"].as_str().unwrap(),
        value["reasons"]
            .as_array()
            .unwrap()
            .iter()
            .map(|reason| reason.as_str().unwrap())
            .collect::<Vec<_>>()
            .join("; ")
    )
}
