use serde_json::{Value, json};

use super::*;
use crate::tests::{TestGit, receipt_pair_fixture};

fn binding() -> SourceBinding {
    SourceBinding {
        commit: "a".repeat(40),
        crate_sources_tree: "b".repeat(40),
        crate_sources_path: CRATE_PATH,
    }
}

fn document(rows: &[(&str, &str, Option<&str>)]) -> Value {
    let mut entries = serde_json::Map::new();
    let mut classes = BTreeMap::<&str, u64>::new();
    for &(id, class, callee) in rows {
        let mut entry = json!({"class":class, "at":"lib.rs:7"});
        if let Some(callee) = callee {
            entry["absent_callee"] = json!(callee);
        }
        assert!(entries.insert(id.into(), entry).is_none());
        *classes.entry(class).or_default() += 1;
    }
    let n = |class| classes.get(class).copied().unwrap_or(0);
    json!({
        "schema_version":"ay.trust.ratchet.v3", "crate_name":"ay-proof-common",
        "metadata":{"git_commit":"a".repeat(40),"crate_sources_tree":"b".repeat(40),
            "crate_sources_clean_at_commit":true,"crate_sources_path":CRATE_PATH},
        "verdicts":{"obligations":rows.len(), "proved":n("proved_solver")+n("proved_structural"),
            "proved_solver_discharged":n("proved_solver"), "proved_structural_no_obligations":n("proved_structural"),
            "kernel_certified":n("proved_solver"), "functions_fully_verified":0,
            "failed":n("failed"), "unknown":n("unknown")+n("skipped"), "runtime_checked":n("runtime_checked"), "timed_out":0},
        "obligation_ledger":{"entries":entries,"classes":classes,"total":rows.len(),"agrees_with_crate_rollup":true,
            "denominator_is_complete":true,"vcgen_truncated_functions":0,"vcgen_truncated_function_names":[]},
        "strict_lane":{"verdict_census_matches_advisory":true}
    })
}

fn checked(doc: &Value) -> Document {
    parse(&serde_json::to_vec(doc).unwrap(), &binding()).unwrap()
}
fn accounting(base: &Value, current: &Value) -> (Value, Vec<String>) {
    let (a, r) = compare(&checked(base), &checked(current));
    (serde_json::to_value(a).unwrap(), r)
}

#[test]
fn unchanged_full_population_and_line_drift_have_no_fabricated_gain_or_loss() {
    let before = document(&[
        ("f|slice|lib.rs#0", "proved_solver", None),
        ("g|assert|lib.rs#0", "unknown", None),
    ]);
    let mut after = before.clone();
    after["obligation_ledger"]["entries"]["f|slice|lib.rs#0"]["at"] = json!("lib.rs:9000");
    let (a, r) = accounting(&before, &after);
    assert!(r.is_empty());
    for key in [
        "obligations_proved",
        "obligations_proof_lost",
        "obligations_removed_total",
        "obligations_newly_asked",
    ] {
        assert_eq!(a["movement"][key], 0);
    }
}

#[test]
fn only_same_obligation_moving_to_solver_discharged_earns_credit() {
    let before = document(&[("f|slice|lib.rs#0", "unknown", None)]);
    let after = document(&[
        ("f|slice|lib.rs#0", "proved_solver", None),
        ("new|assert|lib.rs#0", "proved_solver", None),
        ("structural|no_obligations|?#0", "proved_structural", None),
    ]);
    let (a, r) = accounting(&before, &after);
    assert!(r.is_empty());
    assert_eq!(a["movement"]["obligations_proved_detail"], json!(["f|slice|lib.rs#0"]));
    assert_eq!(a["movement"]["obligations_proved"], 1);
    assert_eq!(
        a["movement"]["obligations_newly_asked_by_class"],
        json!({"proved_solver":1,"proved_structural":1})
    );
    assert_eq!(a["floors_only_a_prover_can_raise"]["proved_solver_discharged"]["delta"], 2);
    assert_eq!(a["disclosed_never_credited"]["proved_structural_no_obligations"]["delta"], 1);
}

#[test]
fn disappearing_unknowns_are_denominator_shrinkage_even_when_counts_improve() {
    let before = document(&[("stay", "unknown", None), ("removed", "unknown", Some("callee"))]);
    let after = document(&[("stay", "unknown", None)]);
    let (a, r) = accounting(&before, &after);
    assert!(r.is_empty());
    assert_eq!(a["movement"]["obligations_proved"], 0);
    assert_eq!(
        a["movement"]["obligations_removed_by_summary_detail"],
        json!(["removed  <- callee"])
    );
    assert_eq!(a["disclosed_never_credited"]["unknown"]["delta"], -1);
    assert_eq!(a["disclosed_never_credited"]["obligations"]["delta"], -1);
    let after = document(&[("stay", "unknown", Some("callee"))]);
    let (a, _) = accounting(&before, &after);
    assert_eq!(a["movement"]["obligations_removed_unattributed_detail"], json!(["removed"]));
}

#[test]
fn replacement_proof_does_not_hide_lost_identity_when_proof_floor_stays_equal() {
    let before = document(&[("old", "proved_solver", None)]);
    let after = document(&[("new", "proved_solver", None)]);
    let (a, r) = accounting(&before, &after);
    assert_eq!(a["floors_only_a_prover_can_raise"]["proved_solver_discharged"]["delta"], 0);
    assert_eq!(a["movement"]["obligations_proved"], 0);
    assert_eq!(a["movement"]["obligations_proof_lost"], 1);
    assert_eq!(r.len(), 1);
    assert!(r[0].contains("REMOVED while proved"));
}

#[test]
fn lost_solver_and_kernel_floors_are_independent_regressions() {
    let before = document(&[("f", "proved_solver", None)]);
    let after = document(&[("f", "runtime_checked", None)]);
    let (a, r) = accounting(&before, &after);
    assert_eq!(a["movement"]["obligations_proof_lost"], 1);
    assert_eq!(r.len(), 3);
    let mut after = before.clone();
    after["verdicts"]["kernel_certified"] = json!(0);
    let (_, r) = accounting(&before, &after);
    assert_eq!(r, ["kernel_certified FELL 1 -> 0 (proof floor)"]);
}

#[test]
fn new_skipped_and_failed_rows_explain_only_their_actual_rollup_rise() {
    let before = document(&[("stay", "unknown", None)]);
    let after = document(&[
        ("stay", "unknown", None),
        ("new-skip", "skipped", None),
        ("new-fail", "failed", None),
    ]);
    let (a, r) = accounting(&before, &after);
    assert!(r.is_empty());
    assert_eq!(a["movement"]["obligations_newly_asked_by_class"], json!({"failed":1,"skipped":1}));
    let before = document(&[("stay", "runtime_checked", None)]);
    let after = document(&[("stay", "unknown", None)]);
    assert!(accounting(&before, &after).1[0].starts_with("unknown ROSE"));
    let after = document(&[("stay", "failed", None)]);
    assert!(accounting(&before, &after).1[0].starts_with("failed ROSE"));
}

#[test]
fn timeouts_cannot_be_excused_by_newly_asked_unknowns() {
    let before = document(&[("stay", "unknown", None)]);
    let mut after = document(&[("stay", "unknown", None), ("new", "unknown", None)]);
    after["verdicts"]["timed_out"] = json!(1);
    assert_eq!(accounting(&before, &after).1, ["timed_out ROSE 0 -> 1"]);
}

#[test]
fn every_original_completeness_and_lane_field_refuses_independently() {
    let complete = document(&[("f", "unknown", None)]);
    for (section, key, bad) in [
        ("obligation_ledger", "denominator_is_complete", json!(false)),
        ("obligation_ledger", "vcgen_truncated_functions", json!(1)),
        ("obligation_ledger", "vcgen_truncated_functions", json!(false)),
        ("strict_lane", "verdict_census_matches_advisory", json!(false)),
    ] {
        let mut broken = complete.clone();
        broken[section][key] = bad;
        assert!(
            parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err(),
            "{section}.{key}"
        );
        broken[section].as_object_mut().unwrap().remove(key);
        assert!(
            parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err(),
            "missing {section}.{key}"
        );
    }
}

#[test]
fn rollup_and_all_identity_classes_must_describe_one_complete_population() {
    let complete = document(&[("f", "proved_solver", None), ("g", "skipped", None)]);
    for key in [
        "obligations",
        "proved",
        "proved_solver_discharged",
        "proved_structural_no_obligations",
        "failed",
        "unknown",
        "runtime_checked",
        "kernel_certified",
    ] {
        let mut broken = complete.clone();
        broken["verdicts"][key] = json!(99);
        assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err(), "{key}");
    }
    for (key, bad) in [
        ("total", json!(1)),
        ("agrees_with_crate_rollup", json!(false)),
        ("classes", json!({"proved_solver":2})),
    ] {
        let mut broken = complete.clone();
        broken["obligation_ledger"][key] = bad;
        assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err(), "{key}");
    }
    let mut broken = complete.clone();
    broken["obligation_ledger"]["entries"]["f"]["class"] = json!("future_authority");
    assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err());
    assert!(parse(&serde_json::to_vec(&document(&[])).unwrap(), &binding()).is_err());
    let mut broken = complete;
    broken["obligation_ledger"]["entries"].as_object_mut().unwrap().remove("f");
    assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err());
}

#[test]
fn truncation_cannot_hide_behind_top_level_complete_boolean() {
    let complete = document(&[("f", "unknown", None)]);
    let mut broken = complete.clone();
    broken["obligation_ledger"]["entries"]["f"]["vcgen_truncated_function"] = json!(true);
    assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err());
    let mut broken = complete;
    broken["obligation_ledger"]["vcgen_truncated_function_names"] = json!(["f"]);
    assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err());
}

#[test]
fn source_schema_commit_tree_cleanliness_and_crate_path_are_all_required() {
    let complete = document(&[("f", "unknown", None)]);
    for (key, bad) in [
        ("git_commit", json!("c".repeat(40))),
        ("crate_sources_tree", json!("c".repeat(40))),
        ("crate_sources_clean_at_commit", json!(false)),
        ("crate_sources_path", json!("another/crate")),
    ] {
        let mut broken = complete.clone();
        broken["metadata"][key] = bad;
        assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err(), "{key}");
    }
    for key in ["schema_version", "crate_name"] {
        let mut broken = complete.clone();
        broken[key] = json!("other");
        assert!(parse(&serde_json::to_vec(&broken).unwrap(), &binding()).is_err());
    }
}

#[test]
fn malformed_duplicates_including_unknown_metadata_and_wrong_numeric_types_refuse() {
    let raw = serde_json::to_string(&document(&[("f", "unknown", None)])).unwrap();
    for suffix in [
        r#", "extra":{"same":1,"same":2}}"#,
        r#", "extra":[{"same":1,"\u0073ame":2}]}"#,
        r#", "extra":NaN}"#,
    ] {
        let broken = format!("{}{}", raw.strip_suffix('}').unwrap(), suffix);
        assert!(parse(broken.as_bytes(), &binding()).is_err());
    }
    for bad in ["true", "-1", "1.0", "1e0", "18446744073709551616", "null", "\"1\""] {
        let broken = raw.replace("\"obligations\":1", &format!("\"obligations\":{bad}"));
        assert_ne!(broken, raw);
        assert!(parse(broken.as_bytes(), &binding()).is_err(), "{bad}");
    }
    assert!(parse(format!("{raw} {{}}").as_bytes(), &binding()).is_err());
    let deep = format!("{}0{}", "[".repeat(256), "]".repeat(256));
    assert!(parse(deep.as_bytes(), &binding()).is_err());
}

#[test]
fn census_file_refuses_links_fifo_oversize_and_replacement_without_blocking() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("census.json");
    fs::write(&path, b"{}").unwrap();
    let held = CensusFile::read(&path).unwrap();
    let other = dir.path().join("replacement");
    fs::write(&other, b"{}").unwrap();
    fs::rename(&other, &path).unwrap();
    assert!(held.check_current().is_err());
    let link = dir.path().join("link");
    std::os::unix::fs::symlink(&path, &link).unwrap();
    assert!(CensusFile::read(&link).is_err());
    fs::File::create(&path).unwrap().set_len(MAX_CENSUS_BYTES + 1).unwrap();
    assert!(CensusFile::read(&path).is_err());
    fs::remove_file(&path).unwrap();
    let name = std::ffi::CString::new(path.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: this test owns the directory and its live NUL-terminated path.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    assert!(CensusFile::read(&path).is_err());
}

fn pair_with_census(
    dir: &tempfile::TempDir,
) -> (ReceiptCheckedPair, std::path::PathBuf, std::path::PathBuf, Value) {
    let request = receipt_pair_fixture(dir);
    let source = request.ay.join("crates/ay-proof-common/src");
    fs::create_dir_all(&source).unwrap();
    fs::write(source.join("lib.rs"), "pub fn fixture() {}\n").unwrap();
    TestGit::run(&request.ay, &["add", "."]);
    TestGit::run(&request.ay, &["commit", "-qm", "real AY crate tree"]);
    let commit =
        String::from_utf8(TestGit.probe(&request.ay, &["rev-parse", "HEAD"]).unwrap()).unwrap();
    let tree = String::from_utf8(
        TestGit.probe(&request.ay, &["rev-parse", "HEAD:crates/ay-proof-common"]).unwrap(),
    )
    .unwrap();
    let pair = crate::pair::inspect(&TestGit, request).unwrap().check_receipts(&TestGit).unwrap();
    let mut doc = document(&[("f|assert|lib.rs#0", "unknown", None)]);
    doc["metadata"]["git_commit"] = json!(commit.trim());
    doc["metadata"]["crate_sources_tree"] = json!(tree.trim());
    let control = dir.path().join("control-census.json");
    let candidate = dir.path().join("candidate-census.json");
    for path in [&control, &candidate] {
        fs::write(path, serde_json::to_vec(&doc).unwrap()).unwrap();
    }
    (pair, control, candidate, doc)
}

#[test]
fn live_pair_consumes_exact_source_bound_bytes_without_advancing_execution() {
    let dir = tempfile::tempdir().unwrap();
    let (pair, control, candidate, _) = pair_with_census(&dir);
    let report = pair.compare_ay_censuses(&TestGit, &control, &candidate).unwrap();
    assert!(report.regressions().is_empty());
    let json = serde_json::to_value(&report).unwrap();
    assert_eq!(json["control"]["input"]["sha256"], tree::hash_bytes(&fs::read(&control).unwrap()));
    assert_eq!(
        json["control"]["input"]["resolved_path"],
        fs::canonicalize(&control).unwrap().to_str().unwrap()
    );
    assert!(json["claim_scope"].as_str().unwrap().contains("no execution"));
    assert!(pair.report().pending_stages.contains(&"admitted-supervised-execution"));
    assert!(pair.report().pending_stages.contains(&"complete-source-bound-ay-census"));
    fs::write(
        pair.snapshot().sources["ay"].path.join("crates/ay-proof-common/src/lib.rs"),
        "changed\n",
    )
    .unwrap();
    assert!(pair.compare_ay_censuses(&TestGit, &control, &candidate).is_err());
}

#[test]
fn final_complete_rebinding_runs_even_when_census_parsing_fails() {
    struct DriftDuringTree {
        changed: std::cell::Cell<bool>,
    }
    impl Git for DriftDuringTree {
        fn validate_repository(&self, root: &Path) -> Result<()> {
            TestGit.validate_repository(root)
        }
        fn probe(&self, root: &Path, args: &[&str]) -> Result<Vec<u8>> {
            let result = TestGit.probe(root, args)?;
            if args == ["rev-parse", "HEAD:crates/ay-proof-common"] {
                fs::write(root.join("crates/ay-proof-common/src/lib.rs"), "changed during read\n")?;
                self.changed.set(true);
            }
            Ok(result)
        }
    }
    let dir = tempfile::tempdir().unwrap();
    let (pair, control, candidate, _) = pair_with_census(&dir);
    fs::write(&candidate, b"not JSON").unwrap();
    let git = DriftDuringTree { changed: std::cell::Cell::new(false) };
    let error = pair.compare_ay_censuses(&git, &control, &candidate).err().unwrap();
    assert!(git.changed.get());
    assert!(error.0.contains("invalid census JSON"), "{error}");
    assert!(error.0.contains("original pair also changed"), "{error}");
}
