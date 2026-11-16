//! Consumer controls use saved diagnostic observations only. They do not
//! fabricate a successful production ProbeAttempt, SDK or native admission.
use std::cell::RefCell;
use std::collections::VecDeque;
use std::os::unix::fs::PermissionsExt as _;
use std::rc::Rc;

use trust_resource_controller::accounting::CpuTimes;

use super::*;
use crate::dependencies::{DependencyResolver, ResolverCapture, ResolverRequest};
use crate::tests::{TestGit, receipt_pair_fixture};

struct Metadata;
impl DependencyResolver for Metadata {
    fn resolve(&mut self, request: &ResolverRequest) -> Result<ResolverCapture> {
        let document = json!({"version":1,
            "packages":[{"id":"fixture","name":"fixture","source":null,
                "manifest_path":request.cwd.join("Cargo.toml")}],
            "workspace_members":["fixture"],
            "resolve":{"root":"fixture","nodes":[{"id":"fixture","dependencies":[],"deps":[],"features":[]}]}});
        Ok(ResolverCapture {
            stdout: serde_json::to_vec(&document).unwrap(),
            stderr: vec![],
            outcome: ResolverOutcome::Exit(0),
            cleanup_confirmed: true,
            output_limit_exceeded: false,
            failure: None,
            execution: Some(json!({"fixture":"saved metadata, no admission"})),
        })
    }
}

fn dependencies(request: crate::pair::Request, probes_consistent: bool) -> DependencyAttempt {
    // Prepare the actual cache input before inspection. The saved metadata
    // fixture does not run Cargo's ordinary cache-directory initialization.
    fs::create_dir_all(&request.cargo_home).unwrap();
    let pair = crate::pair::inspect(&TestGit, request).unwrap().check_receipts(&TestGit).unwrap();
    DependencyAttempt::run(
        pair,
        json!({"fixture":"saved probe consistency only"}),
        probes_consistent,
        &TestGit,
        &mut Metadata,
    )
}

fn capture(stdout: &[u8]) -> Capture {
    Capture {
        stdout: stdout.to_vec(),
        stderr: vec![],
        outcome: ResolverOutcome::Exit(0),
        cause: Some(CompletionCause::Exited),
        retirement_confirmed: true,
        stdout_eof: true,
        stderr_eof: true,
        output_limit_exceeded: false,
        failure: None,
        measurement: Some(Measurement {
            target_runtime_ns: Some(0),
            accounting: Observation {
                scope: Scope::ChildAndWaitedDescendantsV1,
                cpu_times: Some(CpuTimes { user_ns: 0, system_ns: 0 }),
                peak_rss_bytes: Some(0),
            },
        }),
        producer_observation: json!({"fixture":"saved observations; no actual execution"}),
    }
}

const INVENTORY: &[u8] = b"case_a: test\ncase_b: test\n\n2 tests, 0 benchmarks\n";
const SUMMARY: &[u8] = b"running 2 tests\ncase_a ... ok\ncase_b ... ok\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n";

#[derive(Clone)]
enum Mode {
    Complete,
    CandidateDenominator,
    SampleFailure,
    MissingMeasurement,
    BadArtifacts(u8),
    EarlySample,
    LostTerminal,
    SourceDrift(PathBuf),
    ArtifactDrift,
    FailedInventory,
    RefusedStart,
    Oversized(u8),
}
#[derive(Default)]
struct Counts {
    starts: usize,
    events: usize,
    stops: usize,
    root_active: bool,
}
struct ProducerFixture {
    mode: Mode,
    counts: Rc<RefCell<Counts>>,
}
impl ProducerFixture {
    fn new(mode: Mode) -> Self {
        Self { mode, counts: Rc::new(RefCell::new(Counts::default())) }
    }
}
impl Producer for ProducerFixture {
    fn start(&mut self, request: &Request) -> Result<Box<dyn Run>> {
        let mut counts = self.counts.borrow_mut();
        assert!(!counts.root_active, "candidate started before original control retirement");
        counts.starts += 1;
        if matches!(self.mode, Mode::RefusedStart) {
            return Err(refusal("native workload purpose unavailable before project work"));
        }
        if matches!(self.mode, Mode::Oversized(5)) {
            return Err(refusal("x".repeat(evidence::MAX_OBSERVATION_BYTES + 1)));
        }
        counts.root_active = true;
        drop(counts);
        // These nonexecuted regular inputs exercise the consumer only. They
        // cannot be admitted by a real produced-image/runtime owner.
        fs::create_dir_all(&request.target_directory).unwrap();
        let mut artifacts = Vec::new();
        for target in TARGETS {
            let path = request.target_directory.join(target);
            fs::write(&path, format!("diagnostic artifact {target}")).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
            artifacts
                .push(Artifact { target: target.into(), input: file_identity(&path).unwrap() });
        }
        let artifact_path = artifacts[0].input.path.clone();
        if let Mode::BadArtifacts(mode) = self.mode {
            match mode {
                0 => {
                    artifacts.pop();
                }
                1 => artifacts[1].target = artifacts[0].target.clone(),
                2 => {
                    fs::remove_file(&artifacts[1].input.path).unwrap();
                    fs::hard_link(&artifacts[0].input.path, &artifacts[1].input.path).unwrap();
                    artifacts[1].input = file_identity(&artifacts[1].input.path).unwrap();
                }
                _ => unreachable!(),
            }
        }
        let mut events = VecDeque::from([Event::Compiled(Compilation {
            stdout: b"actual compiler observations would be retained here".to_vec(),
            stderr: vec![],
            succeeded: true,
            workers_retired: true,
            output_complete: true,
            artifacts,
            unit_observations: if matches!(self.mode, Mode::Oversized(0)) {
                oversized_observation()
            } else {
                json!({"fixture":"no compiled unit accounting claim"})
            },
        })]);
        if matches!(self.mode, Mode::EarlySample) {
            events.push_back(Event::Harness {
                target: TARGETS[0].into(),
                action: Action::Sample { repetition: 1 },
                capture: capture(SUMMARY),
            });
        }
        for target in TARGETS {
            let mut observed = capture(INVENTORY);
            if matches!(self.mode, Mode::Oversized(1)) {
                observed.producer_observation = oversized_observation();
            }
            if matches!(self.mode, Mode::Oversized(4)) {
                observed.stderr = vec![0xff; 1024 * 1024 + 1];
            }
            if request.side == Side::Candidate && matches!(self.mode, Mode::CandidateDenominator) {
                observed.stdout =
                    b"case_changed: test\ncase_b: test\n\n2 tests, 0 benchmarks\n".to_vec();
            }
            if matches!(self.mode, Mode::FailedInventory) {
                observed.outcome = ResolverOutcome::Exit(8);
                observed.stdout = b"partial\0\xff inventory".to_vec();
                observed.stderr = b"failed inventory bytes\0".to_vec();
            }
            events.push_back(Event::Harness {
                target: target.into(),
                action: Action::Inventory,
                capture: observed,
            });
        }
        for target in TARGETS {
            for repetition in 1..=request.repetitions {
                let mut observed = capture(SUMMARY);
                if matches!(self.mode, Mode::SampleFailure | Mode::ArtifactDrift)
                    && target == TARGETS[0]
                    && repetition == 1
                {
                    observed.outcome = ResolverOutcome::Exit(9);
                    observed.stdout = b"failed sample prefix\0\xff".to_vec();
                    observed.stderr = b"actual failed stderr\0".to_vec();
                }
                if matches!(self.mode, Mode::LostTerminal) {
                    observed.retirement_confirmed = false;
                    observed.failure = Some("original target delivery unknown".into());
                }
                if matches!(self.mode, Mode::MissingMeasurement) {
                    observed.measurement.as_mut().unwrap().accounting.cpu_times = None;
                }
                events.push_back(Event::Harness {
                    target: target.into(),
                    action: Action::Sample { repetition },
                    capture: observed,
                });
            }
        }
        events.push_back(Event::Finished { capture: capture(b"original root terminal bytes\0") });
        Ok(Box::new(RunFixture {
            events,
            mode: self.mode.clone(),
            counts: self.counts.clone(),
            artifact_path,
            repetitions: request.repetitions,
        }))
    }
    fn start_observation(&self) -> Option<Value> {
        if matches!(self.mode, Mode::Oversized(2)) {
            return Some(oversized_observation());
        }
        Some(json!({"fixture":"attempt selected, no admission"}))
    }
}
struct RunFixture {
    events: VecDeque<Event>,
    mode: Mode,
    counts: Rc<RefCell<Counts>>,
    artifact_path: PathBuf,
    repetitions: u32,
}
impl Run for RunFixture {
    fn advance(&mut self) -> Result<Event> {
        let event = self.events.pop_front().expect("consumer resumed after final checkpoint");
        self.counts.borrow_mut().events += 1;
        match (&self.mode, &event) {
            (
                Mode::SourceDrift(path),
                Event::Harness { target, action: Action::Sample { repetition }, .. },
            ) if target == TARGETS[1] && *repetition == self.repetitions => {
                fs::write(path, b"source changed after final sample").unwrap()
            }
            (
                Mode::ArtifactDrift,
                Event::Harness { target, action: Action::Sample { repetition: 1 }, .. },
            ) if target == TARGETS[0] => {
                fs::write(&self.artifact_path, b"artifact changed after failed sample").unwrap()
            }
            _ => {}
        }
        if matches!(event, Event::Finished { .. }) {
            self.counts.borrow_mut().root_active = false;
        }
        Ok(event)
    }
    fn stop(&mut self) -> Result<Capture> {
        let mut counts = self.counts.borrow_mut();
        counts.stops += 1;
        counts.root_active = false;
        let mut observed = capture(b"retained original stop bytes");
        observed.cause = Some(CompletionCause::Cancelled);
        Ok(observed)
    }
    fn observation(&self) -> Value {
        if matches!(self.mode, Mode::Oversized(3)) {
            return oversized_observation();
        }
        json!({"remaining_events":self.events.len(),"fixture":"diagnostic owner only"})
    }
}

fn oversized_observation() -> Value {
    Value::Array(vec![Value::Null; 65_537])
}

#[test]
fn oversized_observations_and_raw_prefixes_stop_without_unbounded_retention_or_success() {
    for mode in 0..6 {
        let temporary = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mut producer = ProducerFixture::new(Mode::Oversized(mode));
        let attempt = execute(&temporary, request, &mut producer);
        assert!(!attempt.consistent(), "mode {mode}");
        assert_eq!(producer.counts.borrow().starts, 1, "mode {mode}");
        assert_eq!(
            producer.counts.borrow().events,
            match mode {
                0 => 1,
                1 | 4 => 2,
                3 => 8,
                _ => 0,
            },
            "mode {mode}"
        );
        assert_eq!(
            producer.counts.borrow().stops,
            usize::from(!matches!(mode, 3 | 5)),
            "mode {mode}"
        );
        assert!(!attempt.sides[1].attempted);
        assert!(
            attempt.errors.iter().any(|error| error.contains("bounds")),
            "mode {mode}: {:?}",
            attempt.errors
        );
        let side = &attempt.report()["sides"][0];
        match mode {
            0 => assert_eq!(side["records"][0]["unit_observations"]["omitted"], true),
            1 => assert_eq!(side["records"][1]["capture"]["producer_observation"]["omitted"], true),
            2 => assert_eq!(side["start"]["omitted"], true),
            3 => assert_eq!(side["live_owner_observation"]["omitted"], true),
            4 => {
                let capture = &side["records"][1]["capture"];
                assert_eq!(capture["stderr_seen_bytes"], 1024 * 1024 + 1);
                assert_eq!(capture["stderr_hex"].as_str().unwrap().len(), 2 * 1024 * 1024);
                assert_eq!(capture["stderr_consumer_truncated"], true);
                assert!(capture["stderr_sha256"].is_null());
            }
            5 => {
                let error = &side["records"][0]["error"];
                assert_eq!(
                    error["serialized_observation_prefix_bytes"],
                    evidence::MAX_OBSERVATION_BYTES
                );
                assert_eq!(error["truncated_or_invalid"], true);
            }
            _ => unreachable!(),
        }
    }
}

fn execute(
    temporary: &tempfile::TempDir,
    request: crate::pair::Request,
    producer: &mut ProducerFixture,
) -> WorkloadAttempt {
    dependencies(request, true).execute_workloads(
        &TestGit,
        producer,
        Options {
            output: temporary.path().join("out"),
            repetitions: 2,
            timeout: Duration::from_secs(3600),
        },
    )
}

#[test]
fn same_original_pair_retains_complete_disjoint_side_population_and_zero_measurements() {
    let temporary = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let original =
        serde_json::to_value(crate::pair::inspect(&TestGit, request.clone()).unwrap().snapshot())
            .unwrap();
    let mut producer = ProducerFixture::new(Mode::Complete);
    let attempt = execute(&temporary, request, &mut producer);
    assert!(attempt.consistent(), "{}", attempt.report());
    attempt.check_unchanged(&TestGit).unwrap();
    assert_eq!(producer.counts.borrow().starts, 2);
    assert_eq!(producer.counts.borrow().events, 16);
    assert_eq!(producer.counts.borrow().stops, 0);
    let report = attempt.report();
    assert_eq!(report["dependencies"]["receipts"]["inputs"], original);
    for side in report["sides"].as_array().unwrap() {
        assert_eq!(side["planned_actions"].as_array().unwrap().len(), 8);
        assert!(
            side["planned_actions"].as_array().unwrap().iter().all(|a| a["status"] == "observed")
        );
        assert_eq!(
            side["records"][3]["capture"]["measurement"]["accounting"]["cpu_times"]["user_ns"],
            0
        );
    }
    assert!(
        report["pending_stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v == "native-AY-census-production")
    );
}

#[test]
fn candidate_denominator_mismatch_disqualifies_complete_prior_control_samples() {
    let temporary = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let mut producer = ProducerFixture::new(Mode::CandidateDenominator);
    let attempt = execute(&temporary, request, &mut producer);
    assert!(!attempt.consistent());
    assert!(attempt.sides[0].finished);
    assert_eq!(attempt.sides[0].samples.len(), 4);
    assert!(attempt.sides[1].samples.is_empty());
    assert!(attempt.errors.iter().any(|e| e.contains("denominator differs")));
    assert_eq!(producer.counts.borrow().stops, 1);
    assert_eq!(
        attempt.report()["sides"][1]["planned_actions"][3]["status"],
        "unobserved-possibly-started"
    );
}

#[test]
fn incomplete_duplicate_and_hardlinked_target_populations_never_reach_inventory() {
    for mode in 0..3 {
        let temporary = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mut producer = ProducerFixture::new(Mode::BadArtifacts(mode));
        let attempt = execute(&temporary, request, &mut producer);
        assert!(!attempt.consistent(), "mode {mode}");
        assert_eq!(producer.counts.borrow().events, 1);
        assert_eq!(producer.counts.borrow().starts, 1);
        assert_eq!(producer.counts.borrow().stops, 1);
        assert!(!attempt.sides[1].attempted);
    }
}

#[test]
fn all_inventories_precede_samples_and_failed_raw_inventory_does_not_shrink_plan() {
    for mode in [Mode::EarlySample, Mode::FailedInventory] {
        let temporary = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mut producer = ProducerFixture::new(mode.clone());
        let attempt = execute(&temporary, request, &mut producer);
        assert!(!attempt.consistent());
        assert_eq!(producer.counts.borrow().events, 2);
        let report = attempt.report();
        assert_eq!(report["sides"][1]["planned_actions"][0]["status"], "not-started");
        if matches!(mode, Mode::FailedInventory) {
            assert_eq!(
                report["sides"][0]["records"][1]["capture"]["stdout_hex"],
                hex(b"partial\0\xff inventory")
            );
        }
    }
}

#[test]
fn known_failed_samples_and_missing_measurements_retain_full_remaining_population() {
    for mode in [Mode::SampleFailure, Mode::MissingMeasurement] {
        let temporary = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mut producer = ProducerFixture::new(mode);
        let attempt = execute(&temporary, request, &mut producer);
        assert!(!attempt.consistent());
        assert!(attempt.errors.is_empty(), "{:?}", attempt.errors);
        assert!(!attempt.failures.is_empty());
        assert!(attempt.sides.iter().all(|s| s.finished));
        assert_eq!(producer.counts.borrow().events, 16);
        assert_eq!(producer.counts.borrow().stops, 0);
    }
}

#[test]
fn source_and_artifact_drift_after_actual_observed_sample_stop_original_before_any_later_action() {
    for artifact in [false, true] {
        let temporary = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mode = if artifact {
            Mode::ArtifactDrift
        } else {
            Mode::SourceDrift(request.ay.join("Cargo.lock"))
        };
        let mut producer = ProducerFixture::new(mode);
        let attempt = execute(&temporary, request, &mut producer);
        assert!(!attempt.consistent());
        assert_eq!(producer.counts.borrow().starts, 1);
        assert_eq!(producer.counts.borrow().events, if artifact { 4 } else { 7 });
        assert_eq!(producer.counts.borrow().stops, 1);
        assert!(attempt.check_unchanged(&TestGit).is_err());
        if artifact {
            assert_eq!(
                attempt.report()["sides"][0]["records"][3]["capture"]["stdout_hex"],
                hex(b"failed sample prefix\0\xff")
            );
        }
    }
}

#[test]
fn unknown_terminal_stops_and_retains_observed_bytes_without_inventing_retirement() {
    let temporary = tempfile::tempdir().unwrap();
    let request = receipt_pair_fixture(&temporary);
    let mut producer = ProducerFixture::new(Mode::LostTerminal);
    let attempt = execute(&temporary, request, &mut producer);
    assert!(!attempt.consistent());
    assert_eq!(producer.counts.borrow().events, 4);
    assert_eq!(producer.counts.borrow().stops, 1);
    assert_eq!(
        attempt.report()["sides"][0]["records"][3]["capture"]["retirement_confirmed"],
        false
    );
}

#[test]
fn failed_original_probe_predicate_and_old_host_refusal_never_become_success_from_observations() {
    for good_probes in [false, true] {
        let temporary = tempfile::tempdir().unwrap();
        let request = receipt_pair_fixture(&temporary);
        let mut producer = ProducerFixture::new(Mode::RefusedStart);
        let attempt = dependencies(request, good_probes).execute_workloads(
            &TestGit,
            &mut producer,
            Options {
                output: temporary.path().join("out"),
                repetitions: 2,
                timeout: Duration::from_secs(3600),
            },
        );
        assert!(!attempt.consistent());
        assert_eq!(producer.counts.borrow().events, 0);
        assert_eq!(producer.counts.borrow().starts, usize::from(good_probes));
        assert_eq!(
            attempt.report()["dependencies"]["compiler_probes"]["fixture"],
            "saved probe consistency only"
        );
        assert_eq!(attempt.report()["requested_options"]["repetitions"], 2);
    }
}

#[test]
fn forbidden_frozen_or_cache_output_and_source_alias_refuse_before_any_writer() {
    for mode in 0..5 {
        let temporary = tempfile::tempdir().unwrap();
        let mut request = receipt_pair_fixture(&temporary);
        let dependency = temporary.path().join("supplied-dependency");
        fs::create_dir(&dependency).unwrap();
        fs::write(dependency.join("Cargo.toml"), "[package]\nname='bound'\nversion='0.1.0'\n")
            .unwrap();
        request.dependency_roots.push(dependency.clone());
        let alias = temporary.path().join("source-alias");
        std::os::unix::fs::symlink(&request.ay, &alias).unwrap();
        let output = match mode {
            0 => request.ay.join("new-results"),
            1 => request.candidate.join("new-results"),
            2 => request.cargo_home.join("new-results"),
            3 => dependency.join("new-results"),
            4 => alias.join("new-results"),
            _ => unreachable!(),
        };
        let mut producer = ProducerFixture::new(Mode::Complete);
        let attempt = dependencies(request, true).execute_workloads(
            &TestGit,
            &mut producer,
            Options { output: output.clone(), repetitions: 2, timeout: Duration::from_secs(3600) },
        );
        assert!(!attempt.consistent(), "mode {mode}");
        assert_eq!(producer.counts.borrow().starts, 0);
        assert!(
            attempt.errors.iter().any(|error| error.contains("aliases a frozen input")),
            "mode {mode}: {:?}",
            attempt.errors
        );
        assert!(!output.exists(), "mode {mode}: forbidden input was written");
    }
}
