// Unit tests for the `.lean` check's obligation record: each row's status is
// the check's verdict, read through Clean's own per-command outcomes, and a
// rejected file never records a `proved` row.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use super::*;
use crate::obligations::{PackageObligations, parse_package_ndjson};

/// Check `files` (name, source) together in one batch, as `targo trust check`
/// does, and read back each file's record.
fn records(files: &[(&str, &str)]) -> Vec<PackageObligations> {
    let dir = tempfile::tempdir().unwrap();
    let paths: Vec<PathBuf> = files
        .iter()
        .map(|(name, source)| {
            let path = dir.path().join(name);
            std::fs::write(&path, source).unwrap();
            path
        })
        .collect();
    let mut checked = super::super::check_batch(&paths, false);
    super::super::refuse_standin_imports_for_check(&mut checked);
    file_records(&checked)
        .iter()
        .map(|(_, bytes)| parse_package_ndjson(bytes).expect("the record reads back"))
        .collect()
}

/// `(def path, kind, status, stop)` of every row.
fn rows(record: &PackageObligations) -> Vec<(String, String, String, String)> {
    record
        .obligations
        .iter()
        .map(|row| {
            let (path, _) =
                trust_types::obligation_identity::split_obligation_key(&row.key).expect("a key");
            (path.to_string(), row.kind.clone(), row.status.clone(), row.stop.clone())
        })
        .collect()
}

fn row(path: &str, kind: &str, status: &str, stop: &str) -> (String, String, String, String) {
    (path.to_string(), kind.to_string(), status.to_string(), stop.to_string())
}

const ACCEPTED: &str = "\
open Nat
namespace N
theorem a : 1 = 1 := rfl
def double (n : Nat) : Nat := n + n
end N
#check N.double
example : 2 = 2 := rfl
set_option pp.all true in
theorem c : 3 = 3 := rfl
";

#[test]
fn an_accepted_file_records_its_verdict_and_every_declaration_clean_named() {
    let [record] = records(&[("Ok.lean", ACCEPTED)]).try_into().unwrap();
    assert_eq!(
        rows(&record),
        [
            row(FILE_ROW, "lean:file", "proved", "solved"),
            row("N.a", "lean:theorem", "proved", "solved"),
            row("N.double", "lean:def", "proved", "solved"),
            row("c", "lean:theorem", "proved", "solved"),
            row("example", "lean:example", "proved", "solved"),
        ]
    );
    assert!(record.coverage_complete);
    assert_eq!(record.outcome, "measured");
    let c = record.obligations.iter().find(|r| r.key.starts_with("c#")).unwrap();
    assert_eq!(c.line, Some(9), "Clean's span of `theorem c` is its keyword");
}

/// The review's first blocker: `rfl` changed to `sorry` is refused by the
/// publish audit, whose whole-batch diagnostic sits at byte 0 (inside `ok`'s
/// span). `s` is the declaration it names, so `s` is failed; `ok` is not
/// proved either, because the refused batch registered nothing.
#[test]
fn a_sorry_is_failed_and_nothing_in_its_refused_batch_is_proved() {
    let [record] =
        records(&[("S.lean", "theorem ok : 1 = 1 := rfl\ntheorem s : 2 = 2 := sorry\n")])
            .try_into()
            .unwrap();
    assert_eq!(
        rows(&record),
        [
            row(FILE_ROW, "lean:file", "failed", "solver-incomplete"),
            row("ok", "lean:theorem", "unknown", "not-dispatched"),
            row("s", "lean:theorem", "failed", "solver-incomplete"),
        ]
    );
    assert!(!record.coverage_complete);
    // A rejected proof refutes nothing: never stopped `solved` (a decided
    // verdict), and labelled as failing closed, never as refuted.
    for failed in record.obligations.iter().filter(|row| row.is_failed()) {
        assert_eq!(failed.basis.as_deref(), Some("unproved_fail_closed"), "{failed:?}");
        assert_eq!(failed.listing_label(), "FAILED: unproved, no counterexample; failed closed");
    }
    assert!(
        record.obligations.iter().filter(|row| !row.is_failed()).all(|row| row.basis.is_none())
    );
}

/// The review's second blocker: an error in no declaration (a `#check` of a
/// name that does not exist) still changes the record: the file row is failed
/// and no declaration is proved.
#[test]
fn an_error_outside_every_declaration_changes_the_record() {
    let good = "theorem a : 1 = 1 := rfl\n";
    let [accepted] = records(&[("A.lean", good)]).try_into().unwrap();
    let [rejected] =
        records(&[("A.lean", &format!("{good}#check nonexistentThing\n"))]).try_into().unwrap();
    assert_eq!(rows(&accepted)[0], row(FILE_ROW, "lean:file", "proved", "solved"));
    assert_eq!(
        rows(&rejected),
        [
            row(FILE_ROW, "lean:file", "failed", "solver-incomplete"),
            row("a", "lean:theorem", "unknown", "not-dispatched"),
        ]
    );
    assert_ne!(accepted.vector, rejected.vector);
    assert!(!rejected.coverage_complete);
}

#[test]
fn a_declaration_under_set_option_in_is_its_own_failed_row() {
    let [record] = records(&[("Q.lean", "set_option pp.all true in\ntheorem c : 3 = 4 := rfl\n")])
        .try_into()
        .unwrap();
    assert_eq!(
        rows(&record),
        [
            row(FILE_ROW, "lean:file", "failed", "solver-incomplete"),
            row("c", "lean:theorem", "failed", "solver-incomplete"),
        ]
    );
}

/// One invocation is one all-or-nothing batch: a file beside a rejected
/// sibling (its own declarations kernel-checked) has no proved row, because
/// the batch registered nothing and the reference recheck did not run; the
/// check prints it NOT ACCEPTED (`lean_cli::FileReport`).
#[test]
fn a_file_beside_a_rejected_sibling_records_no_proof() {
    let records = records(&[
        ("A.lean", "theorem a : 1 = 1 := rfl\n"),
        ("B.lean", "theorem b : 1 = 2 := rfl\n"),
    ]);
    assert_eq!(
        rows(&records[0]),
        [
            row(FILE_ROW, "lean:file", "unknown", "not-dispatched"),
            row("a", "lean:theorem", "unknown", "not-dispatched"),
        ]
    );
    assert_eq!(
        rows(&records[1]),
        [
            row(FILE_ROW, "lean:file", "failed", "solver-incomplete"),
            row("b", "lean:theorem", "failed", "solver-incomplete")
        ]
    );
}

#[test]
fn a_file_clean_cannot_parse_has_only_its_file_row_and_is_not_complete() {
    let [record] = records(&[("P.lean", "theorem broken : := (\n")]).try_into().unwrap();
    assert_eq!(rows(&record), [row(FILE_ROW, "lean:file", "failed", "solver-incomplete")]);
    assert!(!record.coverage_complete);
}

#[test]
fn two_lean_paths_never_share_a_record_file() {
    let target = std::path::Path::new("/t");
    let flat = record_path(target, "/x/b_c.lean");
    let nested = record_path(target, "/x/b/c.lean");
    assert_ne!(flat, nested);
    assert!(flat.starts_with("/t/trust/obligations"), "{}", flat.display());
}

/// One resolver for every record a `.lean` check writes (its obligation
/// records and snapshots, and its `trust.lean-run.v1` timing record):
/// `--target-dir`, else the Cargo environment, else the governing workspace
/// root's `target/` from the current directory; outside every workspace,
/// nowhere.
#[test]
fn a_lean_check_without_a_target_writes_nowhere() {
    let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
    let _env = ["CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR"].map(crate::tests::TestEnvVar::unset);
    let bare = tempfile::tempdir().unwrap();
    let cwd = std::fs::canonicalize(bare.path()).unwrap();
    assert_eq!(record_target_dir_in(None, || Ok(cwd.clone())), Ok(None));

    let explicit = cwd.join("out");
    assert_eq!(record_target_dir_in(Some(&explicit), || Ok(cwd.clone())), Ok(Some(explicit)));

    // A workspace member's directory names the workspace root's target/,
    // where Cargo writes a crate-mode check's records, not the member's.
    std::fs::write(cwd.join("Cargo.toml"), "[workspace]\nmembers = [\"member\"]\n").unwrap();
    let member = cwd.join("member");
    std::fs::create_dir_all(&member).unwrap();
    std::fs::write(member.join("Cargo.toml"), "[package]\nname = \"member\"\n").unwrap();
    assert_eq!(record_target_dir_in(None, || Ok(member.clone())), Ok(Some(cwd.join("target"))));
    assert_eq!(record_target_dir_in(None, || Ok(cwd.clone())), Ok(Some(cwd.join("target"))));
}
