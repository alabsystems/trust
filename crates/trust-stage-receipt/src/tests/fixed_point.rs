//! The fixed-point seed and native stage tool cases both stage-receipt readers are held to.
//!
//! tests/data/fixed-point-cases.json says how each receipt is built from a recorded
//! reference case and gives its exact verdict. These tests hold the Rust reader to it;
//! scripts/tests/stage_receipt_reader_parity_test.py holds the Python reader to the same.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use super::{materialize, reference, unhex, write_files};
use crate::{Object, RECEIPT_NAME, Value, exact_keys, hash, inspect, json};

const RECEIPT_DIGEST: &str = "<receipt>";
const TOOLCHAIN: &str = "<toolchain>";

fn fixture() -> Value {
    let value = json::parse(include_bytes!("../../tests/data/fixed-point-cases.json")).unwrap();
    assert_eq!(value["schema"], "trust.stage-receipt.fixed-point-cases.v1");
    value
}

/// The table `path` names: a word step is a key of a table, an integer step an index
/// of a list (as Python's `table[step]` reads both).
fn table_mut<'a>(value: &'a mut Value, path: &[Value]) -> &'a mut Object {
    let mut current = value;
    for step in path {
        current = match (current, step) {
            (Value::Object(object), Value::String(key)) => {
                object.get_mut(key).unwrap_or_else(|| panic!("{path:?}: no {key}"))
            }
            (Value::Array(values), Value::Number(_)) => {
                let index = step.as_u64().and_then(|index| usize::try_from(index).ok());
                index
                    .and_then(|index| values.get_mut(index))
                    .unwrap_or_else(|| panic!("{path:?}: no item {step}"))
            }
            _ => panic!("{path:?}: {step} is not in a table or a list"),
        };
    }
    let Value::Object(object) = current else {
        panic!("an edit's parent is not a table: {path:?}")
    };
    object
}

/// `receipt` after `edits`, each of which sets or deletes one key of an existing table.
fn edited(receipt: &Value, edits: &Value, paths: &Value) -> Value {
    let mut receipt = receipt.clone();
    for edit in edits.as_array().unwrap() {
        let (set, path) = if exact_keys(edit, &["set", "to"]) {
            (true, &edit["set"])
        } else if exact_keys(edit, &["delete"]) {
            (false, &edit["delete"])
        } else {
            panic!("an edit is neither a set nor a delete: {edit}");
        };
        let mut keys = path.as_array().unwrap().clone();
        if let Some(name) =
            keys[0].as_str().and_then(|key| key.strip_prefix('@')).map(str::to_owned)
        {
            let mut full = paths[name.as_str()].as_array().unwrap().clone();
            full.extend(keys.drain(1..));
            keys = full;
        }
        let (key, parents) = keys.split_last().unwrap();
        let key = key.as_str().unwrap_or_else(|| panic!("an edit's key is not a word: {keys:?}"));
        let table = table_mut(&mut receipt, parents);
        if set {
            table.insert(key.into(), edit["to"].clone());
        } else {
            assert!(table.contains_key(key), "an edit deletes a key that is not there: {keys:?}");
            let kept = std::mem::take(table);
            for (name, value) in &kept {
                if name != key {
                    table.insert(name.clone(), value.clone());
                }
            }
        }
    }
    receipt
}

/// Each stage-relative name of the table `links` under `root`, a symbolic link whose text
/// is the name of a file in the same directory, which need not exist.
fn make_links(root: &Path, links: &Value) {
    for (name, target) in links.as_object().unwrap() {
        let target = target.as_str().unwrap();
        assert!(
            !name.starts_with('/') && name.split('/').all(|part| !matches!(part, "" | "." | ".."))
        );
        assert!(!matches!(target, "" | "." | "..") && !target.contains('/'), "{name} -> {target}");
        let path = root.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink(target, path).unwrap();
        #[cfg(not(unix))]
        panic!("a fixture link needs a unix host: {name} -> {target}");
    }
}

#[test]
fn every_fixed_point_case_gets_the_verdict_both_readers_are_held_to() {
    let fixture = fixture();
    let paths = &fixture["paths"];
    let commit = fixture["commit"].as_str().unwrap();
    let base_case =
        &reference()["file_cases"][fixture["reference_case"].as_u64().unwrap() as usize];
    assert_eq!(base_case["commit"], commit);
    let base = json::parse(&unhex(base_case["raw_hex"].as_str().unwrap())).unwrap();
    let fixed_point = edited(&base, &fixture["fixed_point"], paths);
    let native_lld = edited(&base, &fixture["native_lld"], paths);
    let mut labels = BTreeSet::new();
    let mut statuses = BTreeSet::new();
    let mut failures = Vec::new();
    let (mut accepted, mut refused) = (0, 0);
    for case in fixture["cases"].as_array().unwrap() {
        let label = case["label"].as_str().unwrap();
        assert!(labels.insert(label), "two cases are labelled {label}");
        let start = match case["from"].as_str().unwrap() {
            "base" => &base,
            "fixed-point" => &fixed_point,
            "native-lld" => &native_lld,
            other => panic!("{label}: no starting receipt {other}"),
        };
        let raw = edited(start, &case["edits"], paths).to_string();
        let temporary = tempfile::tempdir().unwrap();
        materialize(temporary.path(), base_case);
        // A case's own stage files, beside the reference case's.
        if let Some(files) = case.get("files") {
            assert!(files.get(RECEIPT_NAME).is_none(), "{label}: a case file is the receipt");
            write_files(temporary.path(), files);
        }
        // Its own symbolic links, each named in its own directory.
        if let Some(links) = case.get("links") {
            assert!(links.get(RECEIPT_NAME).is_none(), "{label}: a case link is the receipt");
            make_links(temporary.path(), links);
        }
        fs::write(temporary.path().join(RECEIPT_NAME), &raw).unwrap();
        let actual = inspect(temporary.path(), commit);
        match (case.get("lines"), case.get("refusal")) {
            (Some(lines), None) => {
                let digest = hash(raw.as_bytes());
                let lines = lines.as_array().unwrap();
                assert_eq!(
                    lines
                        .iter()
                        .filter(|line| line.as_str().unwrap().contains(RECEIPT_DIGEST))
                        .count(),
                    1
                );
                let expected = lines
                    .iter()
                    .map(|line| line.as_str().unwrap().replace(RECEIPT_DIGEST, &digest))
                    .collect::<Vec<_>>();
                match actual {
                    Ok(actual) if actual.provenance_lines() == expected => {}
                    Ok(actual) => failures.push(format!(
                        "{label}: lines {:?}, expected {expected:?}",
                        actual.provenance_lines()
                    )),
                    Err(refusal) => failures.push(format!("{label}: refused: {refusal}")),
                }
                statuses.extend(
                    expected.into_iter().filter(|l| l.starts_with("stage_receipt_status=")),
                );
                accepted += 1;
            }
            (None, Some(refusal)) => {
                let refusal = refusal
                    .as_str()
                    .unwrap()
                    .replace(TOOLCHAIN, &temporary.path().display().to_string());
                match actual {
                    Err(actual) if actual.0 == refusal => {}
                    Err(actual) => failures.push(format!("{label}: refused: {actual}")),
                    Ok(_) => failures.push(format!("{label}: accepted")),
                }
                refused += 1;
            }
            _ => panic!("{label}: neither lines nor a refusal"),
        }
    }
    assert!(failures.is_empty(), "{} case(s):\n{}", failures.len(), failures.join("\n"));
    // Both kinds of verdict and every accepted status: an emptied fixture is no parity.
    assert!(accepted >= 13 && refused >= 85, "fixture population changed: {accepted}/{refused}");
    assert_eq!(
        statuses,
        [
            "stage_receipt_status=candidate-ready",
            "stage_receipt_status=internal-release-ready",
            "stage_receipt_status=release-ready",
            "stage_receipt_status=unpinned-root-seed-ready",
        ]
        .map(String::from)
        .into()
    );
}

#[test]
fn an_edit_changes_what_the_reader_is_given() {
    // The instrument: the cases start from the reference case's own receipt, and an
    // edit reaches the bytes the reader reads.
    let fixture = fixture();
    let paths = &fixture["paths"];
    let base_case =
        &reference()["file_cases"][fixture["reference_case"].as_u64().unwrap() as usize];
    let base = json::parse(&unhex(base_case["raw_hex"].as_str().unwrap())).unwrap();
    assert_eq!(edited(&base, &json::parse(b"[]").unwrap(), paths), base);
    let edit = json::parse(br#"[{"set":["@seed","materialization_status"],"to":"x"}]"#).unwrap();
    let changed = edited(&base, &edit, paths);
    assert_eq!(changed["bootstrap_lineage"]["validated_seed"]["materialization_status"], "x");
    assert_ne!(base["bootstrap_lineage"]["validated_seed"]["materialization_status"], "x");
    let edit = json::parse(br#"[{"delete":["@seed"]}]"#).unwrap();
    assert!(edited(&base, &edit, paths)["bootstrap_lineage"].get("validated_seed").is_none());
    // An integer step reaches a row of a list: the native-lld start's rust-lld row.
    let native = edited(&base, &fixture["native_lld"], paths);
    assert!(base.get("native_stage_tools").is_none());
    assert_eq!(native["native_stage_tools"][0]["status"], "bound");
    let edit = json::parse(br#"[{"set":["@lld","status"],"to":"x"}]"#).unwrap();
    assert_eq!(edited(&native, &edit, paths)["native_stage_tools"][0]["status"], "x");
}
