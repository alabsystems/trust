// Native proof artifact, ownership and cross-process reuse regressions.

use trust_types::{Formula, Sort, SourceSpan, VcKind};

use super::*;

fn actual_add1_fixture() -> (VerificationCondition, ProofEvidence) {
    let input: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/native_add1_overflow.json")).unwrap();
    (
        serde_json::from_value(input["vc"].clone()).unwrap(),
        serde_json::from_value(input["evidence"].clone()).unwrap(),
    )
}

#[test]
fn actual_add1_disjunctive_proof_exports_and_replays_in_a_fresh_process() {
    let directory = Directory::new();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    let produced = directory.0.join("produced");
    let imported = directory.0.join("imported");
    private_dir(&produced).unwrap();
    private_dir(&imported).unwrap();
    let (vc, captured) = actual_add1_fixture();
    let proof = certify_vc_with_artifacts(&vc, &produced).expect("unchanged actual VC certifies");
    assert_eq!(proof, captured, "actual producer term, context and full-row lineage");
    assert_eq!(
        store.publish_session(&produced).unwrap(),
        1,
        "actual producer must export its proof"
    );
    store.prepare_session(&imported).unwrap();
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "proof_artifacts::tests::actual_add1_fresh_process_child", "--nocapture"])
        .env("TRUST_ADD1_REPLAY_TEST_ROOT", &imported)
        .output()
        .unwrap();
    assert!(output.status.success(), "fresh child: {output:?}");
    print!("{}", String::from_utf8_lossy(&output.stdout));
}

#[test]
fn actual_add1_fresh_process_child() {
    let Some(root) = std::env::var_os("TRUST_ADD1_REPLAY_TEST_ROOT") else { return };
    let (vc, captured) = actual_add1_fixture();
    let (proof, stop) =
        replay_vc_with_artifacts_reporting_stop_and_audit_until(&vc, Path::new(&root), None);
    assert_eq!(stop, None);
    let proof = proof.expect("actual proof replay, without any producer/search fallback");
    assert_eq!(proof.evidence(), &captured);
    let audit = proof.audit().expect("same admitted current proof carries its observation");
    assert_eq!(audit.kind(), ReplayKind::CurrentKernelRecheck);
    assert!(audit.matches(&vc, proof.evidence()));
    assert!(super::super::replay_vc_evidence(&vc, proof.evidence()));
    println!("actual add1 fresh-process replay: {}", serde_json::to_string(audit).unwrap());

    let mut rebound = vc.clone();
    rebound.location.line_start += 1;
    rebound.location.line_end += 1;
    let (second, stop) =
        replay_vc_with_artifacts_reporting_stop_and_audit_until(&rebound, Path::new(&root), None);
    assert_eq!(stop, None);
    let second = second.expect("same mathematics, fresh exact current row");
    let second_audit = second.audit().unwrap();
    assert_eq!(second_audit.kind(), ReplayKind::CurrentProcessReference);
    assert!(second_audit.matches(&rebound, second.evidence()));
    assert!(!second_audit.matches(&vc, second.evidence()));
    assert_ne!(second.evidence(), proof.evidence(), "fresh full-row lineage");
}

fn actual_disjunction(formula: &mut Formula) -> &mut Vec<Formula> {
    fn find(formula: &mut Formula) -> Option<&mut Vec<Formula>> {
        match formula {
            Formula::Or(arms) => Some(arms),
            Formula::And(children) => children.iter_mut().find_map(find),
            _ => None,
        }
    }
    find(formula).expect("captured actual overflow disjunction")
}

#[test]
fn actual_add1_artifact_rejects_changed_disjunction_context_and_vc() {
    let directory = Directory::new();
    let (vc, proof) = actual_add1_fixture();
    let ProofEvidence::CleanCic { term, context, .. } = proof else { panic!("actual Clean proof") };
    let mut payload = vc.clone();
    actual_disjunction(&mut payload.formula)[0] = Formula::Bool(true);
    let mut order = vc.clone();
    actual_disjunction(&mut order.formula).swap(0, 1);
    let mut type_ = vc.clone();
    actual_disjunction(&mut type_.formula)[0] = Formula::Int(0);
    let mut changed_vc = vc.clone();
    changed_vc.formula = Formula::Or(vec![changed_vc.formula, Formula::Bool(true)]);

    for (index, current) in [payload, order, type_, changed_vc].into_iter().enumerate() {
        // An attacker may rename a hint and recompute its transport key. The
        // CURRENT hypotheses and kernel must still reject this old proof.
        let identity = super::super::ObligationIdentity::from_vc(&current).unwrap();
        let violation = violation_key(&current).unwrap();
        let candidate = SavedProof {
            schema: 2,
            violation: violation.clone(),
            term: term.clone(),
            context: context.clone(),
        };
        let path = directory.0.join(format!("changed-{index}.json"));
        atomic_write_new(
            &directory.0,
            path.file_name().unwrap().to_str().unwrap(),
            &serde_json::to_vec(&candidate).unwrap(),
        )
        .unwrap();
        assert!(replay(&current, &identity, &violation, &path).is_none(), "mutation {index}");
    }

    // A genuine False proof under a DIFFERENT context is still no proof of
    // this current VC, even with a correct key and freshly recomputed lineage.
    let other = super::super::certify_vc(&obligation()).unwrap();
    let ProofEvidence::CleanCic { term: foreign_term, context: foreign_context, .. } = other else {
        panic!("actual foreign mathematics")
    };
    let mut corrupt_term = term.clone();
    corrupt_term[0] ^= 0xff;
    for (index, (term, context)) in [
        (foreign_term, foreign_context),
        (term.clone(), [context.as_slice(), &[0]].concat()),
        (corrupt_term, context.clone()),
    ]
    .into_iter()
    .enumerate()
    {
        let violation = violation_key(&vc).unwrap();
        let candidate = SavedProof { schema: 2, violation: violation.clone(), term, context };
        let name = format!("foreign-{index}.json");
        atomic_write_new(&directory.0, &name, &serde_json::to_vec(&candidate).unwrap()).unwrap();
        let identity = super::super::ObligationIdentity::from_vc(&vc).unwrap();
        assert!(replay(&vc, &identity, &violation, &directory.0.join(name)).is_none());
    }
}

fn obligation() -> VerificationCondition {
    let x = || Formula::Var("x".into(), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion { message: "persisted proof".into() },
        function: "proof_artifacts::fresh_process".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::current_dir().unwrap().join(format!(
            ".proof-artifact-test-{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed),
        ));
        private_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct Children(Vec<std::process::Child>);
impl Drop for Children {
    fn drop(&mut self) {
        for child in &mut self.0 {
            if child.try_wait().ok().flatten().is_none() {
                let _ = child.kill();
            }
            let _ = child.wait();
        }
    }
}

#[test]
fn replay_audit_carries_actual_kernel_and_reference_paths_with_exact_current_binding() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let source = home.0.join("audit-source");
    let run = home.0.join("audit-run");
    private_dir(&source).unwrap();
    private_dir(&run).unwrap();
    let mut original = obligation();
    // A distinct mathematical key keeps parallel tests' legitimate live fact
    // caches intact while making this test's first replay genuinely cold.
    let variable = format!(
        "audit_original_{}_{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    );
    original.formula = Formula::And(vec![
        Formula::Lt(Box::new(Formula::Var(variable.clone(), Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(Formula::Int(0)), Box::new(Formula::Var(variable, Sort::Int))),
    ]);
    let (cold, stop) =
        replay_vc_with_artifacts_reporting_stop_and_audit_until(&original, &run, None);
    assert!(cold.is_none() && stop.is_none());
    let (produced, stop) =
        certify_vc_with_artifacts_reporting_stop_and_audit_until(&original, &source, None);
    assert_eq!(stop, None);
    let produced = produced.expect("actual native proof production");
    assert!(produced.audit().is_none(), "production is not observed artifact replay");
    assert!(super::super::reference_certificate_for(produced.evidence()).is_some());
    store.publish_session(&source).unwrap();
    store.prepare_session(&run).unwrap();

    let mut first = original.clone();
    first.function = "proof_artifacts::audit_first_current_row".into();
    let (replayed, stop) =
        replay_vc_with_artifacts_reporting_stop_and_audit_until(&first, &run, None);
    assert_eq!(stop, None);
    let (first_evidence, first_audit) =
        replayed.expect("actual current-kernel replay").into_parts();
    let first_audit = first_audit.expect("admitted replay observation");
    assert_eq!(first_audit.kind(), ReplayKind::CurrentKernelRecheck);
    assert!(first_audit.matches(&first, &first_evidence));
    assert!(super::super::replay_vc_evidence(&first, &first_evidence));
    assert!(!first_audit.matches(&original, &first_evidence));

    let mut second = first.clone();
    second.function = "proof_artifacts::audit_second_current_row".into();
    let (replayed, stop) =
        certify_vc_with_artifacts_reporting_stop_and_audit_until(&second, &run, None);
    assert_eq!(stop, None);
    let (second_evidence, second_audit) =
        replayed.expect("actual accepted-reference replay").into_parts();
    let second_audit = second_audit.expect("second admitted replay observation");
    assert_eq!(second_audit.kind(), ReplayKind::CurrentProcessReference);
    assert!(second_audit.matches(&second, &second_evidence));
    assert!(!second_audit.matches(&first, &second_evidence));
    assert!(!second_audit.matches(&second, &first_evidence));
    assert!(super::super::replay_vc_evidence(&second, &second_evidence));
    let json = serde_json::to_value(&second_audit).unwrap();
    assert_eq!(json["schema"], 1);
    assert_eq!(json["kind"], "current_process_reference");
    assert_eq!(json["function"], second.function.as_str());
    for field in ["full_vc_sha256", "proof_evidence_sha256", "lineage_sha256"] {
        assert_eq!(json[field].as_str().unwrap().len(), 64);
    }
    let mut changed = second.clone();
    changed.location.line_start += 1;
    assert!(!second_audit.matches(&changed, &second_evidence));
    changed = second.clone();
    changed.kind = VcKind::Assertion { message: "different current claim".into() };
    assert!(!second_audit.matches(&changed, &second_evidence));
    changed.formula = Formula::Bool(true);
    assert!(!second_audit.matches(&changed, &second_evidence));

    // Even a mismatching deep row presented on an ordinary small compiler
    // worker stack must use the bounded codec stack instead of aborting.
    let mut deep = second.clone();
    for _ in 0..512 {
        deep.formula = Formula::Not(Box::new(deep.formula));
    }
    let matched = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn_scoped(scope, || second_audit.matches(&deep, &second_evidence))
            .unwrap()
            .join()
            .unwrap()
    });
    assert!(!matched);

    let (expired, stop) = replay_vc_with_artifacts_reporting_stop_and_audit_until(
        &second,
        &run,
        Some(Instant::now() - Duration::from_secs(1)),
    );
    assert!(expired.is_none());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
    super::super::INJECTED_TEST_STOPS.lock().unwrap().push((
        second.function.as_str().to_owned(),
        trust_types::determinism::StopCause::WallBackstop,
    ));
    let (stopped, stop) =
        replay_vc_with_artifacts_reporting_stop_and_audit_until(&second, &run, None);
    super::super::INJECTED_TEST_STOPS
        .lock()
        .unwrap()
        .retain(|(name, _)| name != second.function.as_str());
    assert!(stopped.is_none());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
}

#[test]
fn replay_audit_is_withheld_for_unobserved_or_stopped_candidates_without_changing_evidence() {
    let vc = obligation();
    let evidence = super::super::certify_vc(&vc).expect("actual native certificate");
    let no_observation =
        CandidateProof { evidence: evidence.clone(), replay: None }.admit_audit(&vc, false, None);
    assert!(no_observation.audit().is_none());
    assert_eq!(no_observation.evidence(), &evidence);
    for (stopped, deadline) in
        [(true, None), (false, Some(Instant::now() - Duration::from_secs(1)))]
    {
        let withheld = CandidateProof {
            evidence: evidence.clone(),
            replay: Some(ReplayKind::CurrentKernelRecheck),
        }
        .admit_audit(&vc, stopped, deadline);
        assert!(withheld.audit().is_none());
        assert_eq!(withheld.evidence(), &evidence);
    }
}

#[test]
fn pre_solver_replay_is_read_only_on_a_cold_or_corrupt_pool() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let root = home.0.join("run");
    private_dir(&root).unwrap();
    store.prepare_session(&root).unwrap();
    let vc = obligation();
    // A producer holding the cold key must not turn a lookup into a wait.
    let _held = store.try_search_lease(&violation_key(&vc).unwrap()).unwrap();
    let start = Instant::now();
    assert_eq!(replay_vc_with_artifacts_reporting_stop_until(&vc, &root, None), (None, None));
    assert!(start.elapsed() < Duration::from_secs(1));
    let name = filename(&violation_key(&vc).unwrap());
    atomic_write(store.objects_directory(), &name, b"invalid proof bytes").unwrap();
    assert_eq!(replay_vc_with_artifacts_reporting_stop_until(&vc, &root, None), (None, None));
    assert!(!root.join(DIRECTORY).join("outgoing").exists());
    assert_eq!(read_bounded(&store.objects_directory().join(name)).unwrap(), b"invalid proof bytes");
}

#[test]
fn pre_solver_replay_rebinds_the_current_row_and_preserves_stops() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let source = home.0.join("source");
    let root = home.0.join("run");
    private_dir(&source).unwrap();
    private_dir(&root).unwrap();
    let original = obligation();
    assert!(certify_vc_with_artifacts(&original, &source).is_some());
    store.publish_session(&source).unwrap();
    store.prepare_session(&root).unwrap();
    let mut current = original.clone();
    current.function = "pre_solver_replay::moved".into();
    let (evidence, stop) = replay_vc_with_artifacts_reporting_stop_until(&current, &root, None);
    assert_eq!(stop, None);
    let evidence = evidence.expect("current-kernel checked proof");
    assert!(super::super::reference_certificate_for(&evidence).is_some());
    assert!(super::super::replay_vc_evidence(&current, &evidence));
    assert!(!super::super::replay_vc_evidence(&original, &evidence));
    let (expired, stop) = replay_vc_with_artifacts_reporting_stop_until(
        &current,
        &root,
        Some(Instant::now() - Duration::from_secs(1)),
    );
    assert!(expired.is_none());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
    super::super::INJECTED_TEST_STOPS.lock().unwrap().push((
        current.function.as_str().to_owned(),
        trust_types::determinism::StopCause::WallBackstop,
    ));
    let (stopped, stop) = replay_vc_with_artifacts_reporting_stop_until(&current, &root, None);
    super::super::INJECTED_TEST_STOPS
        .lock()
        .unwrap()
        .retain(|(name, _)| name != current.function.as_str());
    assert!(stopped.is_none());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
    current.formula =
        Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
    assert_eq!(replay_vc_with_artifacts_reporting_stop_until(&current, &root, None), (None, None));
}

#[test]
fn shared_search_child() {
    let Some(root) = std::env::var_os("TRUST_TEST_SHARED_PROOF_ROOT") else { return };
    let root = PathBuf::from(root);
    let counter = PathBuf::from(std::env::var_os("TRUST_TEST_SHARED_PROOF_COUNTER").unwrap());
    let mut vc = obligation();
    vc.function = format!("shared_process_{}", std::process::id()).into();
    let evidence = certify_using_until(
        &vc,
        &root,
        Some(Instant::now() + Duration::from_secs(30)),
        |identity| {
            if std::env::var_os("TRUST_TEST_SHARED_PROOF_CRASH").is_some() {
                std::process::exit(23);
            }
            let mut count = OpenOptions::new().create(true).append(true).open(&counter).unwrap();
            writeln!(count, "{}", std::process::id()).unwrap();
            super::super::certify_with_identity_on_stack(&vc.formula, identity)
        },
    )
    .expect("a shared proof must be produced or replayed");
    assert!(super::super::reference_certificate_for(&evidence).is_some());
}

#[cfg(unix)]
#[test]
fn eight_processes_run_one_proof_search() {
    use std::process::{Command, Stdio};
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let held = store
        .try_search_lease(&violation_key(&obligation()).unwrap())
        .unwrap()
        .expect("hold cold search until every client waits");
    let counter = home.0.join("producer-count");
    let mut children = Children(Vec::new());
    let mut waiting = Vec::new();
    for index in 0..8 {
        let root = home.0.join(format!("run-{index}"));
        private_dir(&root).unwrap();
        store.prepare_session(&root).unwrap();
        let observed = home.0.join(format!("waited-{index}"));
        children.0.push(
            Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "proof_artifacts::tests::shared_search_child", "--nocapture"])
                .env("TRUST_TEST_SHARED_PROOF_ROOT", root)
                .env("TRUST_TEST_SHARED_PROOF_COUNTER", &counter)
                .env("TRUST_TEST_PROOF_LEASE_WAITED", &observed)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap(),
        );
        waiting.push(observed);
    }
    let deadline = Instant::now() + Duration::from_secs(20);
    while !waiting.iter().all(|path| path.exists()) {
        assert!(Instant::now() < deadline, "all eight clients must reach the held lease");
        std::thread::sleep(Duration::from_millis(5));
    }
    drop(held);
    while let Some(child) = children.0.pop() {
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "child failed: {output:?}");
    }
    assert_eq!(fs::read_to_string(counter).unwrap().lines().count(), 1);
    println!("shared proof: 8 processes, 1 search producer, 8 current-process certificates");
}

#[cfg(unix)]
#[test]
fn dead_search_owner_releases_the_lease() {
    use std::process::Command;
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let counter = home.0.join("producer-count");
    let failed = home.0.join("failed");
    private_dir(&failed).unwrap();
    store.prepare_session(&failed).unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "proof_artifacts::tests::shared_search_child", "--nocapture"])
        .env("TRUST_TEST_SHARED_PROOF_ROOT", failed)
        .env("TRUST_TEST_SHARED_PROOF_COUNTER", &counter)
        .env("TRUST_TEST_SHARED_PROOF_CRASH", "1")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(23));
    let retry = home.0.join("retry");
    private_dir(&retry).unwrap();
    store.prepare_session(&retry).unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "proof_artifacts::tests::shared_search_child", "--nocapture"])
        .env("TRUST_TEST_SHARED_PROOF_ROOT", retry)
        .env("TRUST_TEST_SHARED_PROOF_COUNTER", &counter)
        .output()
        .unwrap();
    assert!(output.status.success(), "retry failed: {output:?}");
    assert_eq!(fs::read_to_string(counter).unwrap().lines().count(), 1);
}

#[cfg(unix)]
#[test]
fn waiting_for_a_proof_respects_the_current_deadline() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let run = home.0.join("run");
    private_dir(&run).unwrap();
    store.prepare_session(&run).unwrap();
    let vc = obligation();
    let _held = store.try_search_lease(&violation_key(&vc).unwrap()).unwrap().unwrap();
    let (evidence, stop) = super::super::with_stop_scope(|| {
        certify_using_until(&vc, &run, Some(Instant::now() + Duration::from_millis(30)), |_| {
            panic!("a waiting row must not search after its deadline")
        })
    });
    assert!(evidence.is_none());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
}

#[test]
fn fresh_process_child() {
    let Some(root) = std::env::var_os("TRUST_PROOF_ARTIFACT_TEST_ROOT") else { return };
    let root = PathBuf::from(root);
    let old_vc = obligation();
    let store = ProofArtifactStore::from_session(&root).unwrap();
    store.import(&root, &filename(&violation_key(&old_vc).unwrap())).unwrap().unwrap();
    let raw: SavedProof = serde_json::from_slice(
        &read_bounded(
            &root.join(DIRECTORY).join("incoming").join(filename(&violation_key(&old_vc).unwrap())),
        )
        .unwrap(),
    )
    .unwrap();
    let old_identity = super::super::ObligationIdentity::from_vc(&old_vc).unwrap();
    let old = ProofEvidence::CleanCic {
        lineage: super::super::lineage_digest(&raw.term, &raw.context, &old_identity),
        term: raw.term,
        context: raw.context,
        kernel_recheck: None,
    };
    assert!(super::super::reference_certificate_for(&old).is_none());
    let mut vc = old_vc;
    vc.function = "moved_module::renamed_function".into();
    vc.location.file = "moved/module.rs".into();
    vc.location.line_start = 42;
    vc.location.line_end = 42;
    vc.kind = VcKind::Assertion { message: "same mathematics at a new site".into() };
    assert!(!super::super::recheck_presented_linear_int_vc(&vc, &old));
    let barrier = std::sync::Barrier::new(8);
    let results = std::thread::scope(|scope| {
        let handles = (0..8)
            .map(|index| {
                let mut row = vc.clone();
                row.function = format!("moved_module::renamed_function_{index}").into();
                let root = &root;
                let barrier = &barrier;
                scope.spawn(move || {
                    barrier.wait();
                    let (evidence, heartbeats) = super::super::kernel_stop::census::measure(|| {
                        certify_using(&row, root, |_| {
                            panic!("a persisted proof must bypass reconstruction in a new process")
                        })
                    });
                    (evidence.expect("current kernel must accept the imported proof"), heartbeats)
                })
            })
            .collect::<Vec<_>>();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect::<Vec<_>>()
    });
    assert_eq!(
        results.iter().filter(|(_, heartbeats)| *heartbeats > 0).count(),
        1,
        "exactly one caller should perform kernel work in the current process"
    );
    let mut lineages = std::collections::HashSet::new();
    for (evidence, _) in &results {
        assert_ne!(evidence, &old, "each new row must earn its own lineage");
        assert!(super::super::reference_certificate_for(evidence).is_some());
        let ProofEvidence::CleanCic { lineage, .. } = evidence else { panic!("CIC proof") };
        lineages.insert(lineage.bytes);
    }
    assert_eq!(lineages.len(), 8);
    println!(
        "imported proof: 8 fresh row bindings, {} caller performing current-process kernel checks, 0 reconstructions",
        results.iter().filter(|(_, heartbeats)| *heartbeats > 0).count()
    );
    assert!(super::super::reference_certificate_for(&old).is_none());
}

#[test]
fn persisted_proof_bypasses_search_in_a_new_process() {
    let directory = Directory::new();
    let first = directory.0.join("first");
    let second = directory.0.join("second");
    private_dir(&first).unwrap();
    private_dir(&second).unwrap();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    let evidence = certify_vc_with_artifacts(&obligation(), &first).unwrap();
    assert!(super::super::reference_certificate_for(&evidence).is_some());
    assert_eq!(store.publish_session(&first).unwrap(), 1);
    store.prepare_session(&second).unwrap();
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "proof_artifacts::tests::fresh_process_child", "--nocapture"])
        .env("TRUST_PROOF_ARTIFACT_TEST_ROOT", &second)
        .output()
        .unwrap();
    assert!(output.status.success(), "child: {output:?}");
    print!("{}", String::from_utf8_lossy(&output.stdout));
}

#[test]
fn corrupted_and_changed_obligations_use_normal_search() {
    let directory = Directory::new();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    let vc = obligation();
    certify_vc_with_artifacts(&vc, &directory.0).unwrap();
    store.publish_session(&directory.0).unwrap();
    store.prepare_session(&directory.0).unwrap();
    let violation = violation_key(&vc).unwrap();
    let path = directory.0.join(DIRECTORY).join("incoming").join(filename(&violation));
    fs::write(path, b"{broken json}").unwrap();
    fs::write(store.objects_directory().join(filename(&violation)), b"{broken json}").unwrap();
    let mut searched = false;
    assert!(
        certify_using(&vc, &directory.0, |_| {
            searched = true;
            None
        })
        .is_none()
    );
    assert!(searched);
    let mut changed = vc;
    changed.formula =
        Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
    searched = false;
    assert!(
        certify_using(&changed, &directory.0, |_| {
            searched = true;
            None
        })
        .is_none()
    );
    assert!(searched);
}

#[test]
fn copied_proof_cannot_authorize_a_different_current_context() {
    let directory = Directory::new();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    let vc = obligation();
    certify_vc_with_artifacts(&vc, &directory.0).unwrap();
    store.publish_session(&directory.0).unwrap();
    store.prepare_session(&directory.0).unwrap();
    let violation = violation_key(&vc).unwrap();
    let incoming = directory.0.join(DIRECTORY).join("incoming");
    assert!(
        certify_using(&vc, &directory.0, |_| {
            panic!("warm the accepted mathematics without reconstruction")
        })
        .is_some()
    );
    let mut saved: SavedProof =
        serde_json::from_slice(&fs::read(incoming.join(filename(&violation))).unwrap()).unwrap();
    let mut changed = vc;
    changed.formula =
        Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
    let changed_violation = violation_key(&changed).unwrap();
    saved.violation = changed_violation.clone();
    atomic_write(&incoming, &filename(&changed_violation), &serde_json::to_vec(&saved).unwrap())
        .unwrap();
    let mut searched = false;
    assert!(
        certify_using(&changed, &directory.0, |_| {
            searched = true;
            None
        })
        .is_none()
    );
    assert!(searched, "even a forged mathematical key cannot skip current context checks");
}

#[test]
fn reusable_mathematics_cannot_bypass_current_row_admission() {
    let directory = Directory::new();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    let mut vc = obligation();
    certify_vc_with_artifacts(&vc, &directory.0).unwrap();
    store.publish_session(&directory.0).unwrap();
    store.prepare_session(&directory.0).unwrap();
    vc.kind = VcKind::ContractInvariant { expression: "unbound source invariant".into() };
    assert!(vc.kernel_authority_refusal().is_some());
    assert!(
        certify_using(&vc, &directory.0, |_| {
            panic!("a refused row must neither replay nor search")
        })
        .is_none()
    );
}

#[test]
fn independent_projects_share_mathematics_but_not_row_authority() {
    let home = Directory::new();
    let first_project = Directory::new();
    let second_project = Directory::new();
    let mut first_vc = obligation();
    first_vc.location.file = first_project.0.join("lib.rs").display().to_string();
    let first = certify_vc_with_artifacts(&first_vc, &first_project.0).unwrap();
    let first_store = ProofArtifactStore::open(&home.0).unwrap();
    assert_eq!(first_store.publish_session(&first_project.0).unwrap(), 1);

    let second_store = ProofArtifactStore::open(&home.0).unwrap();
    second_store.prepare_session(&second_project.0).unwrap();
    let mut second_vc = first_vc;
    second_vc.location.file = second_project.0.join("lib.rs").display().to_string();
    second_vc.function = "independent_project::same_mathematics".into();
    let second = certify_using(&second_vc, &second_project.0, |_| {
        panic!("another project must reuse the imported mathematical proof")
    })
    .unwrap();
    assert_ne!(first, second);
    assert!(super::super::reference_certificate_for(&second).is_some());
    assert!(!super::super::recheck_presented_linear_int_vc(&second_vc, &first));

    let another_home = Directory::new();
    let isolated_store = ProofArtifactStore::open(&another_home.0).unwrap();
    let isolated_run = Directory::new();
    isolated_store.prepare_session(&isolated_run.0).unwrap();
}

#[test]
fn retention_is_bounded_and_does_not_change_imported_snapshots() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let put = |id: u8, content: &[u8]| {
        let name = format!("{id:064x}.json");
        atomic_write(store.objects_directory(), &name, content).unwrap();
        let path = store.objects_directory().join(name);
        fs::File::options()
            .write(true)
            .open(&path)
            .unwrap()
            .set_times(fs::FileTimes::new().set_modified(
                std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(id.into()),
            ))
            .unwrap();
        path
    };
    let old = put(1, b"old!");
    let recent = put(2, b"new!");
    let newest = put(3, b"last");
    let snapshot = Directory::new();
    store.prepare_session(&snapshot.0).unwrap();
    for path in [&old, &recent, &newest] {
        store.import(&snapshot.0, path.file_name().unwrap().to_str().unwrap()).unwrap().unwrap();
    }
    let imported_old = snapshot.0.join(DIRECTORY).join("incoming").join(old.file_name().unwrap());
    fs::write(store.objects_directory().join("unrelated.txt"), b"keep").unwrap();

    store.prune_to_budget(2, 8).unwrap();
    assert!(!old.exists());
    assert!(recent.exists() && newest.exists());
    assert_eq!(fs::read(&imported_old).unwrap(), b"old!");
    assert_eq!(fs::read(store.objects_directory().join("unrelated.txt")).unwrap(), b"keep");

    store.prune_to_budget(5, 4).unwrap();
    assert!(!recent.exists());
    assert!(newest.exists());
    let oversized = put(9, b"bad");
    fs::File::options()
        .write(true)
        .open(&oversized)
        .unwrap()
        .set_len(MAX_ARTIFACT_BYTES + 1)
        .unwrap();
    store.prune_to_budget(MAX_SNAPSHOT_FILES, MAX_SNAPSHOT_BYTES).unwrap();
    assert!(!oversized.exists());
    assert!(newest.exists());
}

#[cfg(unix)]
#[test]
fn store_refuses_a_shared_writable_ancestor() {
    use std::os::unix::fs::PermissionsExt;
    let directory = Directory::new();
    fs::set_permissions(&directory.0, fs::Permissions::from_mode(0o777)).unwrap();
    assert!(ProofArtifactStore::open(&directory.0).is_err());
}

#[test]
fn stopped_producer_does_not_publish_a_hint() {
    let directory = Directory::new();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    store.prepare_session(&directory.0).unwrap();
    let vc = obligation();
    let (evidence, stop) = super::super::with_stop_scope(|| {
        certify_using(&vc, &directory.0, |identity| {
            let evidence = super::super::certify_with_identity_on_stack(&vc.formula, identity);
            super::super::note_certify_stop(trust_types::determinism::StopCause::WallBackstop);
            evidence
        })
    });
    assert!(evidence.is_some());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
    assert!(!directory.0.join(DIRECTORY).join("outgoing").exists());
    assert!(proof_files(store.objects_directory()).unwrap().is_empty());
}

#[test]
fn a_session_locator_cannot_redirect_writes_outside_the_pool_layout() {
    let directory = Directory::new();
    let unrelated = Directory::new();
    private_dir(&directory.0.join(DIRECTORY)).unwrap();
    let locator = SessionPool { schema: 1, directory: unrelated.0.clone() };
    atomic_write(&directory.0.join(DIRECTORY), "pool.json", &serde_json::to_vec(&locator).unwrap())
        .unwrap();
    assert!(ProofArtifactStore::from_session(&directory.0).is_none());
    assert!(certify_vc_with_artifacts(&obligation(), &directory.0).is_some());
    assert_eq!(fs::read_dir(&unrelated.0).unwrap().count(), 0);
}

#[test]
fn entry_point_stop_is_not_erased_by_a_successful_producer() {
    let directory = Directory::new();
    let mut vc = obligation();
    vc.function = "proof_artifacts::entry_point_stop".into();
    super::super::INJECTED_TEST_STOPS.lock().unwrap().push((
        vc.function.as_str().to_string(),
        trust_types::determinism::StopCause::WallBackstop,
    ));
    let (evidence, stop) = certify_vc_with_artifacts_reporting_stop(&vc, &directory.0);
    super::super::INJECTED_TEST_STOPS
        .lock()
        .unwrap()
        .retain(|(function, _)| function != vc.function.as_str());
    assert!(evidence.is_some());
    assert_eq!(stop, Some(trust_types::determinism::StopCause::WallBackstop));
    assert!(!directory.0.join(DIRECTORY).join("outgoing").exists());
}

#[cfg(unix)]
#[test]
fn partial_and_symlinked_files_are_not_imported() {
    let directory = Directory::new();
    let store = ProofArtifactStore::open(&directory.0).unwrap();
    let first = directory.0.join("first");
    let second = directory.0.join("second");
    private_dir(&first).unwrap();
    private_dir(&second).unwrap();
    let outgoing = first.join(DIRECTORY).join("outgoing");
    private_dir(outgoing.parent().unwrap()).unwrap();
    private_dir(&outgoing).unwrap();
    fs::write(outgoing.join(".interrupted.partial"), b"partial").unwrap();
    let name = filename(&violation_key(&obligation()).unwrap());
    let outside = directory.0.join("outside");
    fs::write(&outside, b"do not read").unwrap();
    std::os::unix::fs::symlink(&outside, outgoing.join(name)).unwrap();
    assert_eq!(store.publish_session(&first).unwrap(), 0);
    store.prepare_session(&second).unwrap();
}

#[test]
fn concurrent_writes_publish_whole_artifacts() {
    let directory = Directory::new();
    let first = vec![b'a'; 64 * 1024];
    let second = vec![b'b'; 64 * 1024];
    let barrier = std::sync::Barrier::new(8);
    std::thread::scope(|scope| {
        for index in 0..8 {
            let barrier = &barrier;
            let root = &directory.0;
            let bytes = if index % 2 == 0 { &first } else { &second };
            scope.spawn(move || {
                barrier.wait();
                atomic_write(root, "same.json", bytes).unwrap();
                let observed = read_bounded(&root.join("same.json")).unwrap();
                assert!(observed.iter().all(|byte| *byte == observed[0]));
                assert_eq!(observed.len(), bytes.len());
            });
        }
    });
    let observed = read_bounded(&directory.0.join("same.json")).unwrap();
    assert!(observed == first || observed == second);
}

#[test]
fn demanded_proof_import_avoids_whole_pool_copy_and_freezes_consumed_bytes() {
    let home = Directory::new();
    let source = Directory::new();
    let eager = Directory::new();
    let lazy = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let vc = obligation();
    certify_vc_with_artifacts(&vc, &source.0).unwrap();
    assert_eq!(store.publish_session(&source.0).unwrap(), 1);
    let name = filename(&violation_key(&vc).unwrap());
    let original = read_bounded(&store.objects_directory().join(&name)).unwrap();
    // Populate bounded irrelevant records without invoking more proof search.
    // The demanded key retains the producer's actual current-kernel proof.
    for index in 0..511 {
        atomic_write(store.objects_directory(), &format!("{index:064x}.json"), &original).unwrap();
    }
    let pool = proof_files(store.objects_directory()).unwrap();
    assert_eq!(pool.len(), 512);
    let pool_bytes = pool.iter().map(|file| file.bytes).sum::<u64>();
    let start = Instant::now();
    // Exact old production mechanism, retained here as a comparative control.
    assert_eq!(
        store
            .copy_to(store.objects_directory(), &eager.0.join(DIRECTORY).join("incoming"))
            .unwrap(),
        512
    );
    let eager_elapsed = start.elapsed();
    let start = Instant::now();
    store.prepare_session(&lazy.0).unwrap();
    let lazy_elapsed = start.elapsed();
    let incoming = lazy.0.join(DIRECTORY).join("incoming");
    assert!(proof_files(&incoming).unwrap().is_empty());
    assert!(
        certify_using(&vc, &lazy.0, |_| panic!("demanded proof must avoid reconstruction"))
            .is_some()
    );
    let imported = proof_files(&incoming).unwrap();
    assert_eq!(imported.len(), 1);
    assert_eq!(imported[0].name, name);
    assert_eq!(read_bounded(&incoming.join(&name)).unwrap(), original);
    atomic_write(store.objects_directory(), &name, b"corrupted replacement").unwrap();
    assert!(replay_vc_with_artifacts_reporting_stop_until(&vc, &lazy.0, None).0.is_some());
    store.prune_to_budget(0, 0).unwrap();
    assert!(replay_vc_with_artifacts_reporting_stop_until(&vc, &lazy.0, None).0.is_some());
    assert_eq!(read_bounded(&incoming.join(&name)).unwrap(), original);
    println!(
        "proof hint demand: pool={} files/{} bytes; eager startup={} files/{} bytes/{:?}; lazy startup=0 files/0 bytes/{:?}; one demanded proof={} files/{} bytes, 0 reconstructions",
        pool.len(),
        pool_bytes,
        pool.len(),
        pool_bytes,
        eager_elapsed,
        lazy_elapsed,
        imported.len(),
        imported[0].bytes,
    );
}

#[test]
fn import_budget_cannot_reset_overflow_or_expand_past_aggregate_bounds() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let name = format!("{:064x}.json", 1);
    atomic_write(store.objects_directory(), &name, b"bounded hint").unwrap();
    for budget in [
        ImportBudget { schema: 1, files: MAX_SNAPSHOT_FILES, bytes: 0 },
        ImportBudget { schema: 1, files: 0, bytes: MAX_SNAPSHOT_BYTES },
        ImportBudget { schema: 1, files: usize::MAX, bytes: u64::MAX },
        ImportBudget { schema: 99, files: 0, bytes: 0 },
    ] {
        let run = Directory::new();
        store.prepare_session(&run.0).unwrap();
        let directory = run.0.join(DIRECTORY);
        atomic_write(&directory, "import-budget.json", &serde_json::to_vec(&budget).unwrap())
            .unwrap();
        assert!(store.import(&run.0, &name).ok().flatten().is_none());
        assert!(proof_files(&directory.join("incoming")).unwrap().is_empty());
        assert!(store.prepare_session(&run.0).is_err(), "another prepare cannot reset capacity");
        let observed: ImportBudget =
            serde_json::from_slice(&read_bounded(&directory.join("import-budget.json")).unwrap())
                .unwrap();
        assert_eq!(observed.files, budget.files);
        assert_eq!(observed.bytes, budget.bytes);
    }
}

#[test]
fn imports_reserve_exactly_once_and_keep_corrupt_consumed_snapshots() {
    let home = Directory::new();
    let run = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    store.prepare_session(&run.0).unwrap();
    let first = format!("{:064x}.json", 1);
    let second = format!("{:064x}.json", 2);
    atomic_write(store.objects_directory(), &first, b"first").unwrap();
    atomic_write(store.objects_directory(), &second, b"second").unwrap();
    let captured = store.import(&run.0, &first).unwrap().unwrap();
    assert_eq!(store.import(&run.0, &first).unwrap().unwrap(), captured);
    store.import(&run.0, &second).unwrap().unwrap();
    let budget: ImportBudget = serde_json::from_slice(
        &read_bounded(&run.0.join(DIRECTORY).join("import-budget.json")).unwrap(),
    )
    .unwrap();
    assert_eq!((budget.files, budget.bytes), (2, 11));
    fs::write(&captured, b"corrupt but already consumed").unwrap();
    atomic_write(store.objects_directory(), &first, b"different producer").unwrap();
    store.import(&run.0, &first).unwrap().unwrap();
    assert_eq!(fs::read(captured).unwrap(), b"corrupt but already consumed");
}

#[cfg(unix)]
#[test]
fn import_contention_and_interrupted_reservations_are_bounded_misses() {
    let home = Directory::new();
    let run = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    store.prepare_session(&run.0).unwrap();
    let name = format!("{:064x}.json", 1);
    atomic_write(store.objects_directory(), &name, b"hint").unwrap();
    let directory = run.0.join(DIRECTORY);
    let lease =
        trust_file_lock::try_exclusive_work_lock(&directory.join("import")).unwrap().unwrap();
    assert!(store.import(&run.0, &name).unwrap().is_none());
    drop(lease);
    // A process dying after reservation retains its charged capacity. A later
    // importer may use the remaining capacity, never rewind the dead charge.
    let budget =
        ImportBudget { schema: 1, files: MAX_SNAPSHOT_FILES - 1, bytes: MAX_SNAPSHOT_BYTES - 4 };
    atomic_write(&directory, "import-budget.json", &serde_json::to_vec(&budget).unwrap()).unwrap();
    let path = store.import(&run.0, &name).unwrap().unwrap();
    assert_eq!(read_bounded(&path).unwrap(), b"hint");
    let observed: ImportBudget =
        serde_json::from_slice(&read_bounded(&directory.join("import-budget.json")).unwrap())
            .unwrap();
    assert_eq!((observed.files, observed.bytes), (MAX_SNAPSHOT_FILES, MAX_SNAPSHOT_BYTES));
    assert!(
        store.import(&run.0, &name).unwrap().is_some(),
        "existing snapshot needs no extra reservation"
    );
}

#[test]
fn session_preparation_refuses_unaccounted_incoming_objects() {
    let home = Directory::new();
    let run = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let directory = run.0.join(DIRECTORY);
    private_dir(&directory).unwrap();
    private_dir(&directory.join("incoming")).unwrap();
    let name = format!("{:064x}.json", 1);
    let existing = directory.join("incoming").join(&name);
    fs::write(&existing, b"unaccounted old snapshot").unwrap();
    assert!(store.prepare_session(&run.0).is_err());
    assert!(!directory.join("pool.json").exists());
    assert!(!directory.join("import-budget.json").exists());
    assert_eq!(fs::read(&existing).unwrap(), b"unaccounted old snapshot");

    // A freshly completed producer can attach its outgoing-only directory;
    // persisted proof publication remains available before pool association.
    let producer = Directory::new();
    assert!(certify_vc_with_artifacts(&obligation(), &producer.0).is_some());
    store.prepare_session(&producer.0).unwrap();
    assert_eq!(store.publish_session(&producer.0).unwrap(), 1);
}

// The compiler fixture `v1_bridge_replays_before_ay_dispatch` rooted its
// session under macOS `temp_dir()` (`/var` is an alias of `/private/var`), and
// every warm replay silently missed: the lazy import's work lock refuses a
// token parent that is not canonical. Production session roots are canonical
// (targo's `VerificationSession::create`). An aliased spelling of a session
// is an ordinary miss: nothing imported, no other object, no escaping error.
#[cfg(unix)]
#[test]
fn lazy_import_requires_the_canonical_session_root_spelling() {
    let home = Directory::new();
    let store = ProofArtifactStore::open(&home.0).unwrap();
    let source = home.0.join("source");
    let run = home.0.join("run");
    private_dir(&source).unwrap();
    private_dir(&run).unwrap();
    let vc = obligation();
    assert!(certify_vc_with_artifacts(&vc, &source).is_some());
    assert_eq!(store.publish_session(&source).unwrap(), 1);
    store.prepare_session(&run).unwrap();
    let alias = home.0.with_extension("alias");
    std::os::unix::fs::symlink(&home.0, &alias).unwrap();
    let aliased = replay_vc_with_artifacts_reporting_stop_until(&vc, &alias.join("run"), None);
    let _ = fs::remove_file(&alias);
    assert_eq!(aliased, (None, None), "an aliased session root is a miss");
    let incoming = run.join(DIRECTORY).join("incoming");
    assert!(proof_files(&incoming).unwrap().is_empty(), "the aliased miss imported nothing");
    assert!(
        replay_vc_with_artifacts_reporting_stop_until(&vc, &run, None).0.is_some(),
        "the canonical spelling of the same session replays the published proof"
    );
    assert_eq!(proof_files(&incoming).unwrap().len(), 1);
}
