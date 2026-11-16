//! Real proof-artifact replay at the native primary scheduling boundary.

use std::fs;
use std::path::{Path, PathBuf};

use trust_certify::proof_artifacts::{ProofArtifactStore, ReplayKind};
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

use super::*;

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let root = std::env::current_dir().unwrap().join(format!(
            ".router-kernel-replay-{}-{}",
            std::process::id(),
            NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&root).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        }
        Self(root)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained failed native kernel replay fixture: {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn vc() -> VerificationCondition {
    let x = || Formula::Var("x".into(), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion { message: "native early kernel replay".into() },
        function: "demo::f".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

fn produce(root: &Path) -> PathBuf {
    produce_vcs(root, &[vc()])
}

fn produce_vcs(root: &Path, vcs: &[VerificationCondition]) -> PathBuf {
    let store = ProofArtifactStore::open(root).unwrap();
    let produced = root.join("produced");
    fs::create_dir(&produced).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&produced, fs::Permissions::from_mode(0o700)).unwrap();
    }
    for current in vcs {
        assert!(
            trust_certify::proof_artifacts::certify_vc_with_artifacts(current, &produced).is_some()
        );
    }
    assert_eq!(store.publish_session(&produced).unwrap(), vcs.len());
    let imported = root.join("imported");
    fs::create_dir(&imported).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&imported, fs::Permissions::from_mode(0o700)).unwrap();
    }
    store.prepare_session(&imported).unwrap();
    imported
}

struct Primary {
    manifest: EngineManifest,
    requests: Arc<Mutex<Vec<Vec<String>>>>,
    supported: bool,
}

impl VerificationEngine for Primary {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        if self.supported && obligation.kind == ObligationKind::Assertion {
            SupportLevel::Preferred
        } else {
            SupportLevel::Unsupported { reason: "test primary refuses this current row".into() }
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        self.requests.lock().unwrap().push(
            request
                .obligations()
                .iter()
                .map(|obligation| obligation.obligation_id.clone())
                .collect(),
        );
        // This control observes dispatch, not proof acceptance. Every ordinary
        // attempted row deliberately remains Unknown, with no fake proof data.
        request
            .obligations()
            .iter()
            .map(|obligation| ObligationEvidence {
                evidence_id: format!("primary-attempt:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: self.manifest.clone(),
                status: EvidenceStatus::Unknown,
                decline: None,
                proof_strength: None,
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: vec!["actual primary control was called".into()],
            })
            .collect()
    }
}

fn engine(requests: Arc<Mutex<Vec<Vec<String>>>>, supported: bool) -> FullVerificationEngine {
    let mut manifest =
        EngineManifest::new("trust-mc", "early-replay-control", EngineKind::Reachability);
    manifest.capabilities.push(EngineCapability {
        obligation_kind: ObligationKind::Assertion,
        support: SupportLevel::Preferred,
    });
    FullVerificationEngine::new(
        vec![Box::new(Primary { manifest, requests, supported })],
        route_only_policy(),
    )
}

fn bundle() -> TrustContractBundle {
    bundle_with_obligation(ObligationKind::Assertion, "current-assertion", None, None)
}

fn dispatch(
    engine: &FullVerificationEngine,
    bundle: &TrustContractBundle,
    context: &VerifierExecutionContext,
) -> (VerificationRunResult, Vec<CurrentKernelProofReplay>) {
    let mut run = engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        bundle,
        &bundle.obligations,
        None,
        None,
        context,
    );
    let proofs = run.take_current_kernel_proof_replays();
    assert!(
        run.take_current_kernel_proof_replays().is_empty(),
        "one dispatch exported its proof twice"
    );
    let (result, _) = run.into_parts();
    (result, proofs)
}

fn run_fresh_replay_actor(
    home: &Path,
    imported: &Path,
    selector: &str,
    marker: &str,
) -> std::process::Output {
    use std::io::{Read as _, Seek as _};
    use std::process::{Child, Stdio};

    fn capture(path: &Path) -> fs::File {
        let mut options = fs::OpenOptions::new();
        options.read(true).write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.mode(0o600);
        }
        options.open(path).unwrap()
    }
    struct Actor {
        child: Child,
        stdout: fs::File,
        stderr: fs::File,
    }
    impl Drop for Actor {
        fn drop(&mut self) {
            // Only this original child; a panic/watchdog never leaves its
            // readers or process alive. Regular captures preserve its prefix.
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
    let stdout = capture(&home.join("child.stdout"));
    let stderr = capture(&home.join("child.stderr"));
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "full_verification::tests::kernel_replay_tests::fresh_process_kernel_replay_actor",
            "--ignored",
            "--nocapture",
        ])
        .env_remove("TRUST_ROUTER_KERNEL_REPLAY_CHILD")
        .env_remove("TRUST_ROUTER_CONCURRENT_KERNEL_REPLAY_CHILD")
        .env(selector, imported)
        .env("TRUST_AY_SMT_TRACE", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::from(stdout.try_clone().unwrap()))
        .stderr(Stdio::from(stderr.try_clone().unwrap()))
        .spawn()
        .unwrap();
    let mut actor = Actor { child, stdout, stderr };
    // This is a hang detector, never a renewed kernel/context budget.
    let watchdog = Instant::now() + std::time::Duration::from_secs(60);
    let status = loop {
        if let Some(status) = actor.child.try_wait().unwrap() {
            break status;
        }
        assert!(Instant::now() < watchdog, "fresh replay actor watchdog expired");
        std::thread::sleep(std::time::Duration::from_millis(5));
    };
    fn read(file: &mut fs::File) -> Vec<u8> {
        file.rewind().unwrap();
        let mut bytes = Vec::new();
        file.take(1024 * 1024 + 1).read_to_end(&mut bytes).unwrap();
        assert!(bytes.len() <= 1024 * 1024, "fresh actor output exceeds observation bound");
        bytes
    }
    let output = std::process::Output {
        status,
        stdout: read(&mut actor.stdout),
        stderr: read(&mut actor.stderr),
    };
    assert!(output.status.success(), "actual fresh actor: {output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("running 1 test") && stdout.contains("1 passed; 0 failed"));
    assert_eq!(stdout.matches(marker).count(), 1, "missing post-assertion actor canary");
    output
}

#[test]
fn fresh_process_replay_checks_kernel_before_any_primary_request() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let output = run_fresh_replay_actor(
        &home.0,
        &imported,
        "TRUST_ROUTER_KERNEL_REPLAY_CHILD",
        "FRESH_CURRENT_KERNEL_REPLAY_COMPLETE",
    );
    let ay_searches = String::from_utf8_lossy(&output.stderr)
        .matches("[aysmt] ---- program handed to ay ----")
        .count();
    assert_eq!(ay_searches, 0, "actual fresh replay dispatched AY: {output:?}");
    print!("{}", String::from_utf8_lossy(&output.stdout));
}

#[test]
#[ignore = "owned actor run only by fresh_process_replay_checks_kernel_before_any_primary_request"]
fn fresh_process_kernel_replay_actor() {
    if let Some(root) = std::env::var_os("TRUST_ROUTER_CONCURRENT_KERNEL_REPLAY_CHILD") {
        concurrent_subset_actor(Path::new(&root));
        return;
    }
    let root = std::env::var_os("TRUST_ROUTER_KERNEL_REPLAY_CHILD").expect("actual prepared run");
    // Independently regenerate both current public request and current VC in
    // this fresh process, which owns no producer kernel certificate.
    let bundle = bundle();
    let current = vc();
    let context = VerifierExecutionContext::new("fresh-native-kernel-replay");
    let requests = Arc::new(Mutex::new(Vec::new()));
    let engine = engine(requests.clone(), true).with_kernel_proof_replay_candidates(
        &bundle,
        vec![(bundle.obligations[0].clone(), current.clone())],
        root.into(),
        &context,
    );
    let (result, proofs) = dispatch(&engine, &bundle, &context);
    assert!(requests.lock().unwrap().is_empty(), "eligible primary request was dispatched");
    assert_eq!(result.requested_obligations, bundle.obligations);
    assert_eq!(result.evidence.len(), 1);
    assert_eq!(result.summary.proved, 0, "pending public row became authority");
    assert_ne!(result.evidence[0].status, EvidenceStatus::Proved);
    let mut proofs = proofs;
    assert_eq!(proofs.len(), 1);
    let checked = proofs.pop().unwrap();
    assert!(checked.matches(&bundle, &bundle.obligations[0], &current, &context));
    let (proof, audit) =
        checked.into_parts_for(&bundle, &bundle.obligations[0], &current, &context).unwrap();
    assert_eq!(audit.kind(), ReplayKind::CurrentKernelRecheck);
    assert!(audit.matches(&current, &proof));
    assert!(trust_certify::reference_certificate_for(&proof).is_some());
    assert!(proofs.is_empty(), "proof moved twice");
    println!(
        "fresh complete native inventory=1; primary requests=0; actual replay={}",
        serde_json::to_string(&audit).unwrap()
    );
    println!("FRESH_CURRENT_KERNEL_REPLAY_COMPLETE");
}

#[test]
fn partial_replay_keeps_unresolved_siblings_in_their_original_batch() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let mut bundle = bundle();
    let mut sibling = bundle.obligations[0].clone();
    sibling.obligation_id = "unresolved-sibling".into();
    bundle.obligations.push(sibling.clone());
    let context = VerifierExecutionContext::new("partial-native-kernel-replay");
    let requests = Arc::new(Mutex::new(Vec::new()));
    let engine = engine(requests.clone(), true).with_kernel_proof_replay_candidates(
        &bundle,
        vec![(bundle.obligations[0].clone(), vc())],
        imported,
        &context,
    );
    let (result, proofs) = dispatch(&engine, &bundle, &context);
    assert_eq!(*requests.lock().unwrap(), vec![vec![sibling.obligation_id]]);
    assert_eq!(result.requested_obligations, bundle.obligations);
    assert_eq!(result.evidence.len(), 2);
    assert_eq!(result.summary.proved, 0);
    assert_eq!(proofs.len(), 1);
}

#[test]
fn changed_formula_or_public_binding_takes_the_ordinary_primary_path() {
    for changed_binding in [false, true] {
        let home = Directory::new();
        let imported = produce(&home.0);
        let bundle = bundle();
        let mut claim = bundle.obligations[0].clone();
        let mut current = vc();
        if changed_binding {
            claim.description.push_str(" changed after frozen association");
        } else {
            current.formula = Formula::Bool(true);
        }
        let context = VerifierExecutionContext::new("ordinary-miss");
        let requests = Arc::new(Mutex::new(Vec::new()));
        let engine = engine(requests.clone(), true).with_kernel_proof_replay_candidates(
            &bundle,
            vec![(claim, current)],
            imported,
            &context,
        );
        let (result, proofs) = dispatch(&engine, &bundle, &context);
        assert_eq!(
            *requests.lock().unwrap(),
            vec![vec![bundle.obligations[0].obligation_id.clone()]]
        );
        assert_eq!(result.requested_obligations, bundle.obligations);
        assert!(proofs.is_empty());
    }
}

#[test]
fn changed_premise_or_corrupt_term_does_not_suppress_primary_search() {
    for corrupt in [false, true] {
        let home = Directory::new();
        let imported = produce(&home.0);
        let bundle = bundle();
        let mut current = vc();
        if corrupt {
            let objects = home.0.join("trust/results/v1/kernel-proof-artifacts-v2/objects");
            let paths = fs::read_dir(objects)
                .unwrap()
                .map(Result::unwrap)
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
                .collect::<Vec<_>>();
            assert_eq!(paths.len(), 1);
            let mut saved: serde_json::Value =
                serde_json::from_slice(&fs::read(&paths[0]).unwrap()).unwrap();
            let term = saved["term"].as_array_mut().expect("actual encoded proof term");
            let byte = term[0].as_u64().unwrap();
            term[0] = serde_json::Value::from(byte ^ 0xff);
            fs::write(&paths[0], serde_json::to_vec(&saved).unwrap()).unwrap();
        } else {
            current.formula = Formula::And(vec![
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Bool(true),
            ]);
        }
        let context = VerifierExecutionContext::new("invalid-mathematics");
        let requests = Arc::new(Mutex::new(Vec::new()));
        let engine = engine(requests.clone(), true).with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), current)],
            imported,
            &context,
        );
        let (result, proofs) = dispatch(&engine, &bundle, &context);
        assert_eq!(
            *requests.lock().unwrap(),
            vec![vec![bundle.obligations[0].obligation_id.clone()]]
        );
        assert_eq!(result.requested_obligations, bundle.obligations);
        assert!(proofs.is_empty());
    }
}

#[test]
fn required_engine_policy_is_checked_before_replay() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let bundle = bundle();
    let context = VerifierExecutionContext::new("required-native-policy");
    let engine = FullVerificationEngine::new(Vec::new(), FullVerificationPolicy::default())
        .with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), vc())],
            imported,
            &context,
        );
    let (result, proofs) = dispatch(&engine, &bundle, &context);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(proofs.is_empty());
}

#[test]
#[cfg(all(feature = "trust-build", feature = "trust-vc-native"))]
fn genuine_required_native_engines_keep_missing_native_input_refusal() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let bundle = bundle();
    let context = VerifierExecutionContext::new("actual-native-replay-boundary");
    let engine = FullVerificationEngine::with_required_native_engines()
        .with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), vc())],
            imported,
            &context,
        );
    let (result, proofs) = dispatch(&engine, &bundle, &context);
    assert_eq!(result.requested_obligations, bundle.obligations);
    assert_eq!(result.evidence.len(), 1);
    assert_eq!(result.summary.proved, 0);
    assert!(proofs.is_empty());
}

#[cfg(feature = "trust-build")]
fn live_native_fixture()
-> (TrustContractBundle, NativeVerificationBundle, trust_ir::SourceGenerationAuthority) {
    // This constructs a new typed program with ModuleBuilder. The existing
    // conspicuous unit-only issuer models the compiler seam; saved input bytes
    // are not promoted to live source authority. This is a component control,
    // not qualification of the real compiler's source lowering.
    let mut native = native_trust_mc_safe_trust_ir_bundle();
    let mut bundle = TrustContractBundle::empty(
        "early-replay-live-native-fixture",
        BundleSubject::Function {
            crate_name: "demo".into(),
            path: "demo::router_native_checked_branch".into(),
        },
    );
    bundle.obligations.push(native_trust_ir_obligation(
        "trust-mc",
        7,
        0,
        ObligationKind::Assertion,
        None,
    ));
    bundle.obligations[0].source = router_native_source_location(18);
    bind_native_obligation_to_public_claim(&mut native, trust_ir::ProofId::new(0), &bundle, 0);
    let authority = whole_function_fixture_source_authority(&mut native);
    (bundle, native, authority)
}

#[test]
#[cfg(feature = "trust-build")]
fn live_typed_native_preflight_then_replay_omits_primary_batch() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let (bundle, native, authority) = live_native_fixture();
    let context = VerifierExecutionContext::new("live-native-kernel-replay-component");
    let engine = FullVerificationEngine::with_required_native_engines()
        .with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), vc())],
            imported,
            &context,
        );
    let mut run = engine
        .verify_obligations_with_native_trust_ir_bundle_and_source_authority_and_live_receipts(
            &bundle,
            &bundle.obligations,
            &native,
            &authority,
            &context,
        );
    assert_eq!(run.result().requested_obligations, bundle.obligations);
    assert_eq!(run.result().summary.proved, 0, "pending native status is not authority");
    assert!(
        !run.result()
            .diagnostics
            .iter()
            .any(|line| line.starts_with("full-verification engine batch:")),
        "native search was dispatched: {:?}",
        run.result()
    );
    assert_eq!(run.take_current_kernel_proof_replays().len(), 1);
    assert!(run.take_current_kernel_proof_replays().is_empty());
}

#[test]
#[cfg(feature = "trust-build")]
fn native_public_binding_and_source_authority_refusals_remain_ordinary() {
    for mutation in ["public-claim", "native-request", "missing-source"] {
        let home = Directory::new();
        let imported = produce(&home.0);
        let (mut bundle, mut native, authority) = live_native_fixture();
        match mutation {
            "public-claim" => bundle.obligations[0].description.push_str(" changed"),
            "native-request" => {
                let NativeVerificationRequest::TrustMc(request) = &mut native.requests[0] else {
                    panic!("native MC")
                };
                request.obligations.clear();
            }
            _ => {}
        }
        let context = VerifierExecutionContext::new("native-refusal-preserved");
        let engine = FullVerificationEngine::with_required_native_engines()
            .with_kernel_proof_replay_candidates(
                &bundle,
                vec![(bundle.obligations[0].clone(), vc())],
                imported,
                &context,
            );
        let mut run = if mutation == "missing-source" {
            engine.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
                &bundle,
                &bundle.obligations,
                Some(&native),
                None,
                &context,
            )
        } else {
            engine.verify_obligations_with_native_trust_ir_bundle_and_source_authority_and_live_receipts(
                &bundle, &bundle.obligations, &native, &authority, &context,
            )
        };
        assert_eq!(run.result().requested_obligations, bundle.obligations);
        assert!(run.take_current_kernel_proof_replays().is_empty(), "refusal bypassed: {mutation}");
    }
}

#[test]
fn native_cutoff_is_not_the_later_function_deadline() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let bundle = bundle();
    let mut context = VerifierExecutionContext::new("native-share-expired");
    context.deadline = Some(Instant::now() + Duration::from_secs(30));
    context.native_solve_cutoff = Some(Instant::now());
    assert!(!context.budget_exceeded(), "function still has its reserved later-lane time");
    let engine = engine(Arc::new(Mutex::new(Vec::new())), true)
        .with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), vc())],
            imported,
            &context,
        );
    let (result, proofs) = dispatch(&engine, &bundle, &context);
    assert_eq!(result.requested_obligations, bundle.obligations);
    assert_eq!(result.summary.proved, 0);
    assert!(proofs.is_empty(), "replay spent reserved later-lane time");
}

#[test]
fn refused_later_dispatch_cannot_export_an_earlier_dispatch_proof() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let bundle = bundle();
    let context = VerifierExecutionContext::new("per-dispatch-proof-custody");
    let engine = engine(Arc::new(Mutex::new(Vec::new())), true)
        .with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), vc())],
            imported,
            &context,
        );
    let mut first = engine
        .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
            &bundle,
            &bundle.obligations,
            None,
            None,
            &context,
        );
    let mut changed = bundle.obligations[0].clone();
    changed.description.push_str(" not the canonical claim");
    let mut second = engine
        .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
            &bundle,
            &[changed],
            None,
            None,
            &context,
        );
    assert!(second.take_current_kernel_proof_replays().is_empty());
    assert_eq!(first.take_current_kernel_proof_replays().len(), 1);
    assert!(first.take_current_kernel_proof_replays().is_empty());
}

fn concurrent_subset_fixture() -> (TrustContractBundle, [VerificationCondition; 2]) {
    let mut bundle = bundle();
    let mut sibling = bundle.obligations[0].clone();
    sibling.obligation_id = "independent-current-row".into();
    bundle.obligations.push(sibling);
    let mut second = vc();
    let y = || Formula::Var("y".into(), Sort::Int);
    second.formula = Formula::And(vec![
        Formula::Lt(Box::new(y()), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(Formula::Int(0)), Box::new(y())),
    ]);
    second.location.line_start = 2;
    second.location.line_end = 2;
    (bundle, [vc(), second])
}

fn concurrent_subset_actor(imported: &Path) {
    let (bundle, vcs) = concurrent_subset_fixture();
    let context = VerifierExecutionContext::new("overlapping-subsets");
    let requests = Arc::new(Mutex::new(Vec::new()));
    let engine = engine(requests.clone(), true).with_kernel_proof_replay_candidates(
        &bundle,
        bundle.obligations.iter().cloned().zip(vcs.clone()).collect(),
        imported.to_owned(),
        &context,
    );
    let rendezvous = std::sync::Barrier::new(2);
    let audits = std::thread::scope(|threads| {
        let handles = [0, 1].map(|index| {
            let bundle = &bundle;
            let context = &context;
            let engine = &engine;
            let rendezvous = &rendezvous;
            let vcs = &vcs;
            threads.spawn(move || {
                rendezvous.wait();
                let mut run = engine
                    .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
                        bundle,
                        std::slice::from_ref(&bundle.obligations[index]),
                        None,
                        None,
                        context,
                    );
                assert_eq!(
                    run.result().requested_obligations,
                    vec![bundle.obligations[index].clone()]
                );
                assert_eq!(run.result().summary.proved, 0);
                assert_eq!(run.result().evidence.len(), 1);
                assert_ne!(run.result().evidence[0].status, EvidenceStatus::Proved);
                let mut proofs = run.take_current_kernel_proof_replays();
                assert_eq!(
                    proofs.len(),
                    1,
                    "subset={index}; evidence={:?}; diagnostics={:?}",
                    run.result().evidence,
                    run.result().diagnostics,
                );
                assert!(run.take_current_kernel_proof_replays().is_empty());
                let checked = proofs.pop().unwrap();
                assert_eq!(checked.obligation(), &bundle.obligations[index]);
                assert!(checked.matches(bundle, &bundle.obligations[index], &vcs[index], context));
                assert!(!checked.matches(
                    bundle,
                    &bundle.obligations[1 - index],
                    &vcs[1 - index],
                    context,
                ));
                let (proof, audit) = checked
                    .into_parts_for(bundle, &bundle.obligations[index], &vcs[index], context)
                    .unwrap();
                assert_eq!(audit.kind(), ReplayKind::CurrentKernelRecheck);
                assert!(audit.matches(&vcs[index], &proof));
                assert!(trust_certify::reference_certificate_for(&proof).is_some());
                serde_json::to_value(audit).unwrap()
            })
        });
        handles.map(|handle| handle.join().unwrap())
    });
    assert!(requests.lock().unwrap().is_empty(), "concurrent replay dispatched a primary request");
    println!(
        "CONCURRENT_CURRENT_KERNEL_REPLAY_COMPLETE rows=2 proofs=2 primary_requests=0 audits={}",
        serde_json::to_string(&audits).unwrap(),
    );
}

#[test]
fn simultaneous_subsets_keep_only_their_own_checked_proofs() {
    let home = Directory::new();
    let (_, vcs) = concurrent_subset_fixture();
    let imported = produce_vcs(&home.0, &vcs);
    // Prestage through the real bounded/accounted import path. Cold import
    // contention is an optional miss, separately controlled below. The exec'd
    // actor receives bytes, never this parent's actual reference certificates.
    for current in &vcs {
        let (proof, stop) =
            trust_certify::proof_artifacts::replay_vc_with_artifacts_reporting_stop_and_audit_until(
                current, &imported, None,
            );
        assert_eq!(stop, None);
        assert!(proof.is_some(), "actual producer hint did not enter the bounded snapshot");
    }
    let budget: serde_json::Value = serde_json::from_slice(
        &fs::read(imported.join("kernel-proof-artifacts-v2/import-budget.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(budget["files"], 2);
    assert!(budget["bytes"].as_u64().is_some_and(|bytes| bytes > 0));
    let output = run_fresh_replay_actor(
        &home.0,
        &imported,
        "TRUST_ROUTER_CONCURRENT_KERNEL_REPLAY_CHILD",
        "CONCURRENT_CURRENT_KERNEL_REPLAY_COMPLETE",
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        String::from_utf8_lossy(&output.stderr)
            .matches("[aysmt] ---- program handed to ay ----")
            .count(),
        0,
        "concurrent fresh replay dispatched AY: {output:?}",
    );
    print!("{stdout}");
}

#[test]
fn concurrent_cold_import_contention_keeps_each_original_primary_fallback() {
    let home = Directory::new();
    let (bundle, vcs) = concurrent_subset_fixture();
    let imported = produce_vcs(&home.0, &vcs);
    let import = trust_file_lock::try_exclusive_work_lock(
        &imported.join("kernel-proof-artifacts-v2/import"),
    )
    .unwrap()
    .expect("actual original import work lock");
    let context = VerifierExecutionContext::new("cold-import-contention");
    let requests = Arc::new(Mutex::new(Vec::new()));
    let engine = engine(requests.clone(), true).with_kernel_proof_replay_candidates(
        &bundle,
        bundle.obligations.iter().cloned().zip(vcs).collect(),
        imported.clone(),
        &context,
    );
    let rendezvous = std::sync::Barrier::new(2);
    std::thread::scope(|threads| {
        let handles = [0, 1].map(|index| {
            let bundle = &bundle;
            let context = &context;
            let engine = &engine;
            let rendezvous = &rendezvous;
            threads.spawn(move || {
                rendezvous.wait();
                let mut run = engine
                    .verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
                        bundle,
                        std::slice::from_ref(&bundle.obligations[index]),
                        None,
                        None,
                        context,
                    );
                assert_eq!(
                    run.result().requested_obligations,
                    vec![bundle.obligations[index].clone()]
                );
                assert_eq!(run.result().summary.proved, 0);
                assert_eq!(run.result().evidence.len(), 1);
                assert_eq!(run.result().evidence[0].status, EvidenceStatus::Unknown);
                assert!(run.take_current_kernel_proof_replays().is_empty());
            })
        });
        for handle in handles {
            handle.join().unwrap();
        }
    });
    import.validate().unwrap();
    let mut actual = requests.lock().unwrap().clone();
    actual.sort();
    let mut expected =
        bundle.obligations.iter().map(|row| vec![row.obligation_id.clone()]).collect::<Vec<_>>();
    expected.sort();
    assert_eq!(actual, expected, "a cold miss lost or donated a current request");
    assert_eq!(
        fs::read_dir(imported.join("kernel-proof-artifacts-v2/incoming")).unwrap().count(),
        0,
    );
    let budget: serde_json::Value = serde_json::from_slice(
        &fs::read(imported.join("kernel-proof-artifacts-v2/import-budget.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(budget["files"], 0);
    assert_eq!(budget["bytes"], 0);
}

#[test]
fn unsupported_primary_cannot_be_bypassed_by_a_matching_kernel_hint() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let bundle = bundle();
    let context = VerifierExecutionContext::new("unsupported-replay");
    let requests = Arc::new(Mutex::new(Vec::new()));
    let engine = engine(requests.clone(), false).with_kernel_proof_replay_candidates(
        &bundle,
        vec![(bundle.obligations[0].clone(), vc())],
        imported,
        &context,
    );
    let (result, proofs) = dispatch(&engine, &bundle, &context);
    assert!(requests.lock().unwrap().is_empty());
    assert_eq!(result.evidence[0].status, EvidenceStatus::Unsupported);
    assert!(proofs.is_empty());
}

#[test]
fn replay_proof_rejects_changed_rows_contexts_and_late_consumption() {
    let home = Directory::new();
    let imported = produce(&home.0);
    let bundle = bundle();
    let current = vc();
    let context = VerifierExecutionContext::new("exact-consumption");
    let engine = engine(Arc::new(Mutex::new(Vec::new())), true)
        .with_kernel_proof_replay_candidates(
            &bundle,
            vec![(bundle.obligations[0].clone(), current.clone())],
            imported,
            &context,
        );
    let (_, mut proofs) = dispatch(&engine, &bundle, &context);
    let checked = proofs.pop().unwrap();
    let mut changed_vc = current.clone();
    changed_vc.location.line_start += 1;
    assert!(!checked.matches(&bundle, &bundle.obligations[0], &changed_vc, &context));
    let mut changed_bundle = bundle.clone();
    changed_bundle.obligations[0].description.push_str(" changed");
    assert!(!checked.matches(&changed_bundle, &changed_bundle.obligations[0], &current, &context));
    let other_context = VerifierExecutionContext::new("other-run");
    assert!(!checked.matches(&bundle, &bundle.obligations[0], &current, &other_context));
    context.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
    assert!(checked.into_parts_for(&bundle, &bundle.obligations[0], &current, &context).is_none());
}

#[test]
fn expired_or_cancelled_context_never_exports_replay_proof() {
    for cancelled in [false, true] {
        let home = Directory::new();
        let imported = produce(&home.0);
        let bundle = bundle();
        let mut context = VerifierExecutionContext::new("stopped-replay");
        if cancelled {
            context.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
        } else {
            context.deadline = Some(Instant::now());
        }
        let engine = engine(Arc::new(Mutex::new(Vec::new())), true)
            .with_kernel_proof_replay_candidates(
                &bundle,
                vec![(bundle.obligations[0].clone(), vc())],
                imported,
                &context,
            );
        let (result, proofs) = dispatch(&engine, &bundle, &context);
        assert_eq!(result.summary.proved, 0);
        assert!(proofs.is_empty());
    }
}
