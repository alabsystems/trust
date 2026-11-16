//! A Lean invocation commits one batch. Local kernel success in a refused
//! batch must not become a public proof claim in either output format.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

fn check(files: &[&Path], target: &Path, json: bool) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo-trust"));
    command
        .env_remove("ATERM_SESSION_ID")
        .env_remove("CLAUDE_CODE_SESSION_ID")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .env_remove("CARGO_TARGET_DIR")
        .current_dir(target.parent().expect("owned scratch directory"))
        .arg("check")
        .args(files)
        .arg("--target-dir")
        .arg(target);
    if json {
        command.arg("--json");
    }
    command.output().expect("run the source-built Lean front door")
}

fn records(target: &Path, source: &Path) -> Vec<Value> {
    let canonical = source.canonicalize().expect("fixture source").display().to_string();
    let mut matching = std::fs::read_dir(target.join("trust/obligations"))
        .expect("actual obligation records")
        .map(|entry| {
            let path = entry.expect("record entry").path();
            std::fs::read_to_string(path)
                .expect("record bytes")
                .lines()
                .map(|line| serde_json::from_str::<Value>(line).expect("record JSON"))
                .collect::<Vec<_>>()
        })
        .filter(|rows| rows[0]["package"] == canonical)
        .collect::<Vec<_>>();
    assert_eq!(matching.len(), 1, "one actual record for {canonical}");
    matching.remove(0)
}

fn fixtures(root: &Path, second: &str) -> [PathBuf; 2] {
    let first = root.join("Good.lean");
    let second_path = root.join("Sibling.lean");
    std::fs::write(&first, "theorem acceptedLocally : 1 = 1 := rfl\n").unwrap();
    std::fs::write(&second_path, second).unwrap();
    [first, second_path]
}

#[test]
fn a_rejected_first_file_keeps_its_checked_sibling_unaccepted() {
    let scratch = tempfile::tempdir().unwrap();
    let [good, bad] = fixtures(scratch.path(), "theorem rejectedProof : 1 = 2 := rfl\n");
    for (index, json) in [false, true].into_iter().enumerate() {
        let target = scratch.path().join(format!("target-{index}"));
        let files = [&bad as &Path, &good];
        let output = check(&files, &target, json);
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert_eq!(output.status.code(), Some(1), "{stdout}\n{stderr}");
        if json {
            let report: Value = serde_json::from_str(&stdout).unwrap();
            assert_eq!(report["accepted"], 0, "{report}");
            assert_eq!(report["not_accepted"], 1, "{report}");
            assert_eq!(report["rejected"], 1, "{report}");
            let files = report["files"].as_array().unwrap();
            assert_eq!(files.len(), 2);
            assert!(files.iter().all(|file| file["accepted"] == false), "{report}");
            let locally_checked =
                files.iter().find(|file| file["path"] == good.display().to_string()).unwrap();
            assert_eq!(locally_checked["status"], "not-accepted");
            assert_eq!(
                locally_checked["batch_refused_by"],
                serde_json::json!([bad.display().to_string()])
            );
            assert_eq!(locally_checked["diagnostics"], serde_json::json!([]));
            assert_eq!(locally_checked["registered"], serde_json::json!(["acceptedLocally"]));
        } else {
            let verdicts = stdout
                .lines()
                .filter(|line| {
                    line.starts_with("PROVED ")
                        || line.starts_with("REJECTED ")
                        || line.starts_with("NOT ACCEPTED ")
                })
                .collect::<Vec<_>>();
            assert_eq!(verdicts.len(), 2, "{stdout}");
            assert!(!stdout.contains("PROVED "), "{stdout}");
            assert!(
                verdicts.contains(
                    &format!("NOT ACCEPTED {} — its batch was refused by {}; 1 declaration(s) kernel-checked in the refused batch, none accepted", good.display(), bad.display()).as_str()
                ),
                "{stdout}"
            );
            assert!(verdicts.contains(&format!("REJECTED {}", bad.display()).as_str()), "{stdout}");
        }

        let good_record = records(&target, &good);
        assert_eq!(good_record[0]["coverage_complete"], false);
        let good_rows =
            good_record.iter().filter(|row| row.get("key").is_some()).collect::<Vec<_>>();
        assert_eq!(good_rows.len(), 2, "file and theorem rows are retained");
        assert!(
            good_rows
                .iter()
                .all(|row| row["status"] == "unknown" && row["stop"] == "not-dispatched")
        );
        let bad_record = records(&target, &bad);
        // Coverage counts enumerated rows, not successful proofs: this file's
        // own complete inventory can be failed while its sibling stays unknown.
        assert_eq!(bad_record[0]["coverage_complete"], true);
        let bad_rows = bad_record.iter().filter(|row| row.get("key").is_some()).collect::<Vec<_>>();
        assert!(bad_rows.iter().any(|row| row["status"] == "failed"));
        assert!(bad_rows.iter().all(|row| row["status"] != "proved" && row["basis"] != "refuted"));
        assert!(bad_rows.iter().filter(|row| row["status"] == "failed").all(|row| row["stop"]
            == "solver-incomplete"
            && row["basis"] == "unproved_fail_closed"));
    }
}

#[test]
fn an_accepted_lean_batch_reports_both_exact_kernel_checked_files() {
    let scratch = tempfile::tempdir().unwrap();
    let [first, second] = fixtures(scratch.path(), "theorem acceptedSibling : 2 = 2 := rfl\n");
    {
        let target = scratch.path().join("target-json");
        let output = check(&[&first, &second], &target, true);
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert_eq!(output.status.code(), Some(0), "{stdout}\n{stderr}");
        let report: Value = serde_json::from_str(&stdout).unwrap();
        assert_eq!(report["accepted"], 2, "{report}");
        assert_eq!(report["not_accepted"], 0, "{report}");
        assert_eq!(report["rejected"], 0, "{report}");
        assert_eq!(report["files"].as_array().unwrap().len(), 2);
        assert!(report["files"].as_array().unwrap().iter().all(|file| file["accepted"] == true));
        for file in [&first, &second] {
            let record = records(&target, file);
            assert_eq!(record[0]["coverage_complete"], true);
            let rows = record.iter().filter(|row| row.get("key").is_some()).collect::<Vec<_>>();
            assert_eq!(rows.len(), 2, "file and theorem rows are retained");
            assert!(rows.iter().all(|row| row["status"] == "proved" && row["stop"] == "solved"));
        }
    }
}
