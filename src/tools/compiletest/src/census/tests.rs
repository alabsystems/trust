// Trust: exercise the ordinary collector and census with intentionally invalid
// execution directives. Collection queries Bootstrap's TEST_RUSTC; these unit
// tests never compile or execute their synthetic Rust subjects.
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::{SystemTime, UNIX_EPOCH};

use camino::{Utf8Path, Utf8PathBuf};

use super::*;
use crate::common::trust_verification_isolation_tests::trust_lane_config_from;
use crate::directives::DirectivesCache;
use crate::{Stamp, TestCollectorCx, collect_tests_from_dir};

struct Fixture(Utf8PathBuf);

impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "compiletest-census-self-test-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        Self(Utf8PathBuf::from_path_buf(root).unwrap())
    }

    fn collect(&self, source: &str) -> (Arc<Config>, Vec<CollectedTest>) {
        self.collect_with_mode(source, TestMode::Ui)
    }

    fn collect_with_mode(&self, source: &str, mode: TestMode) -> (Arc<Config>, Vec<CollectedTest>) {
        let suite = self.0.join("tests").join(mode.to_string());
        fs::create_dir_all(&suite).unwrap();
        let file = suite.join("compile-flags-incremental.rs");
        fs::write(&file, source).unwrap();
        fs::create_dir(suite.join("auxiliary")).unwrap();
        fs::write(suite.join("auxiliary/helper.rs"), "pub fn helper() {}\n").unwrap();
        let mut config = trust_lane_config_from(&[]);
        // The parser-only helper deliberately names a nonexistent compiler.
        // Real collection lazily queries target specifications, as the existing
        // directives tests do through Bootstrap's genuine compiler under test.
        config.rustc_path =
            std::env::var("TEST_RUSTC").expect("must be configured by bootstrap").into();
        config.mode = mode;
        config.suite = mode.to_string().parse().unwrap();
        config.src_root = self.0.clone();
        config.src_test_suite_root = suite;
        config.build_root = self.0.join("build");
        config.build_test_suite_root = config.build_root.join("test").join(mode.to_string());
        fs::create_dir_all(&config.build_test_suite_root).unwrap();
        config.force_rerun = true;
        let config = Arc::new(config);
        let cx = TestCollectorCx {
            cache: DirectivesCache::load(&config),
            common_inputs_stamp: Stamp::from_path(&file),
            modified_tests: vec![],
            config: config.clone(),
        };
        let collected =
            collect_tests_from_dir(&cx, &cx.config.src_test_suite_root, Utf8Path::new("")).unwrap();
        assert!(!collected.poisoned);
        (config, collected.tests)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn plans_invalid_self_test_revisions_without_executing_their_validation() {
    let fixture = Fixture::new();
    let (config, tests) = fixture.collect(
        "//@ revisions: good bad bad-space\n\
         //@ check-pass\n\
         //@ aux-build: helper.rs\n\
         //@[bad] compile-flags: -Cincremental=true\n\
         //@[bad] should-fail\n\
         //@[bad-space] compile-flags: -C incremental=dir\n\
         //@[bad-space] should-fail\n\
         fn main() {}\n",
    );
    let directory = fixture.0.join("census");
    let census = Census::create(&directory).unwrap();
    census.plan(&config, &tests).unwrap();
    let raw = fs::read_to_string(directory.join("events.jsonl")).unwrap();
    let records =
        raw.lines().map(|line| serde_json::from_str::<Value>(line).unwrap()).collect::<Vec<_>>();
    let planned = records.iter().filter(|row| row["event"] == "planned").collect::<Vec<_>>();
    assert_eq!(planned.len(), 3);
    assert_eq!(records.last().unwrap()["planned"], 3);
    for row in planned {
        assert_eq!(row["all_revisions"], json!(["good", "bad", "bad-space"]));
        assert_eq!(row["source"]["status"], "read");
        assert_eq!(row["direct_auxiliary_inputs"].as_array().unwrap().len(), 1);
        assert_eq!(row["direct_auxiliary_inputs"][0]["status"], "read");
        if row["revision"] == "good" {
            assert_eq!(row["properties_status"], "loaded");
            assert_eq!(row["expected_harness_failure"], false);
            assert!(row["compile_flags"].is_array());
        } else {
            assert_eq!(
                row["properties_status"],
                "deferred-to-expected-failure-self-test-execution"
            );
            assert_eq!(row["expected_harness_failure"], true);
            assert!(row["compile_flags"].is_null());
            assert!(row["run_flags"].is_null());
            assert!(
                row["source_directives"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|line| line.as_str().unwrap().contains("incremental="))
            );
        }
    }
    // Deferral must not change the execution-time validation those self-tests
    // are intended to exercise, including the split -C spelling.
    for test in tests.iter().filter(|test| test.desc.should_fail == ShouldFail::Yes) {
        assert!(
            catch_unwind(AssertUnwindSafe(|| TestProps::from_file(
                &test.testpaths.file,
                test.variant.revision(),
                &config
            )))
            .is_err()
        );
    }
}

#[test]
fn ordinary_invalid_directives_are_still_refused() {
    let fixture = Fixture::new();
    let (config, tests) =
        fixture.collect("//@ check-pass\n//@ compile-flags: -Cincremental=true\nfn main() {}\n");
    let census = Census::create(&fixture.0.join("census")).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| census.plan(&config, &tests))).is_err());
}

#[test]
fn ignored_debugger_cases_keep_their_loaded_auxiliary_inputs() {
    let fixture = Fixture::new();
    let (config, tests) =
        fixture.collect_with_mode("//@ aux-build: helper.rs\nfn main() {}\n", TestMode::DebugInfo);
    assert_eq!(tests.len(), 3);
    // The ordinary collector skips its directive scan when no debugger exists.
    assert!(tests.iter().all(|test| test.desc.is_ignored()
        && test.auxiliary_inputs.all_aux_path_strings().next().is_none()));
    let directory = fixture.0.join("census");
    let census = Census::create(&directory).unwrap();
    census.plan(&config, &tests).unwrap();
    let raw = fs::read_to_string(directory.join("events.jsonl")).unwrap();
    let records =
        raw.lines().map(|line| serde_json::from_str::<Value>(line).unwrap()).collect::<Vec<_>>();
    let planned = records.iter().filter(|row| row["event"] == "planned").collect::<Vec<_>>();
    assert_eq!(planned.len(), 3);
    assert_eq!(records.last().unwrap()["planned"], 3);
    for row in planned {
        assert_eq!(row["properties_status"], "loaded");
        assert_eq!(row["direct_auxiliary_inputs"].as_array().unwrap().len(), 1);
        assert_eq!(row["direct_auxiliary_inputs"][0]["status"], "read");
    }
}
