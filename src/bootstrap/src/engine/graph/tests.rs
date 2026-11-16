use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;
use std::{fs, io};

use build_helper::trust_output_lock::OutputLock;
use build_helper::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};
use jobserver_utils::Jobserver;

use super::*;
use crate::core::build_steps::frontend_runtime::{BuildOwnership, CommandOwnership};
use crate::engine::{Plan, Preparation, TaskError};

// Trust: real finite namespace custody enters these SAME original native tasks.
// The file sits under tests/, as tidy's `unit_tests` check requires, and the
// module keeps its `tree_tests` path.
#[path = "tests/tree_tests.rs"]
mod tree_tests;

fn isolated(name: &str) -> bool {
    const ROLE: &str = "TRUST_ENGINE_NATIVE_GRAPH_ACTOR";
    if std::env::var(ROLE).as_deref() == Ok(name) {
        return false;
    }
    let result = crate::test_entry::uncaptured_actor(std::process::Command::new(
        std::env::current_exe().unwrap(),
    ))
    .args(["--exact", name, "--nocapture"])
    .env(ROLE, name)
    .output()
    .unwrap();
    assert!(result.status.success(), "actual native graph actor failed: {result:?}");
    assert!(String::from_utf8(result.stdout).unwrap().contains("native-graph-checked"));
    true
}

fn outcome(root: &Path, output: &Path, deadline: Instant, install: bool) -> Outcome {
    let lease = match Manager::open(root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual native selected-input comparison".into(),
            contract: "same command/output custody; no Host or SDK completion".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    let original = Arc::new(CommandOwnership::new(lease));
    let mut scope = Preparation::new(
        Plan {
            source: root.to_owned(),
            output: output.to_owned(),
            jobs: 1,
            llvm_link_jobs: Some(1),
            frontend_threads: Some(1),
            dry_run: false,
            native_object_leaf: false,
        },
        Some(&original),
    )
    .protect(deadline)
    .unwrap();
    let output = Arc::new(OutputLock::try_acquire(output).unwrap().unwrap());
    scope
        .retain_build_ownership(Arc::new(
            BuildOwnership::new(output, Arc::clone(&original)).unwrap(),
        ))
        .unwrap();
    if install {
        scope.install(Some(&original)).unwrap();
    }
    // Actual acquired owners, with NO fabricated CompletedRuntime or Host closure.
    Outcome::in_scope(None, scope)
}

fn root() -> (tempfile::TempDir, PathBuf) {
    let directory = tempfile::tempdir().unwrap();
    let physical = fs::canonicalize(directory.path()).unwrap();
    (directory, physical)
}

#[test]
fn actual_comparison_and_changed_input_keep_the_same_open_custody() {
    if isolated(
        "engine::graph::native::tests::actual_comparison_and_changed_input_keep_the_same_open_custody",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    let deadline = Instant::now() + Duration::from_secs(30);
    let bytes = b"pub fn successor(x: u32) -> u32 { x + 1 }\n";
    fs::write(source.join("baseline.rs"), bytes).unwrap();
    fs::write(source.join("candidate.rs"), bytes).unwrap();
    let server = Jobserver::new(3).unwrap();
    let held = server.client().acquire().unwrap();
    let descriptors = server.pipe_descriptors().unwrap();
    let flags = descriptors
        .iter()
        .map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) })
        .collect::<Vec<_>>();
    crate::utils::metadata_scheduler::install_test_original(server.clone()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let left = [PathBuf::from("baseline.rs")];
    let right = [PathBuf::from("candidate.rs")];
    let compared = original.compare_source_inputs(&left, &right, deadline).unwrap();
    assert_eq!(compared.pairs.len(), 1);
    assert!(compared.all_digests_match && compared.pairs[0].same_digest);
    assert_eq!(compared.pairs[0].left.bytes, bytes.len() as u64);
    assert!(!original.has_completed_runtime());
    let graph = original.open_native_graph().unwrap();
    let baseline = graph.capture_inputs(&left, deadline).unwrap();
    let candidate = graph.capture_inputs(&right, deadline).unwrap();
    assert!(Arc::ptr_eq(&baseline.native.root, &candidate.native.root));
    assert!(Arc::ptr_eq(
        &baseline.native.root,
        original.protected.as_ref().unwrap().native_graph_owner().unwrap().source_root()
    ));
    assert_eq!(
        baseline.native.root.directory().unwrap().as_raw_fd(),
        candidate.native.root.directory().unwrap().as_raw_fd(),
        "captures must use the SAME original Manager directory description"
    );
    let raw = baseline.native.entries[0].file.as_raw_fd();
    assert_eq!(unsafe { libc::lseek(raw, 3, libc::SEEK_SET) }, 3);
    fs::write(source.join("candidate.rs"), b"pub fn successor(x: u32) -> u32 { x + 2 }\n").unwrap();
    assert!(matches!(
        graph.compare_inputs(&baseline, &candidate, deadline),
        Err(GraphError::InputChanged(_))
    ));
    // Restoring bytes cannot revive a snapshot that already failed revalidation.
    fs::write(source.join("candidate.rs"), bytes).unwrap();
    assert!(matches!(graph.revalidate(&candidate, deadline), Err(GraphError::InputChanged(_))));
    fs::write(source.join("candidate.rs"), b"pub fn successor(x: u32) -> u32 { x + 2 }\n").unwrap();
    let current = graph.capture_inputs(&right, deadline).unwrap();
    let different = graph.compare_inputs(&baseline, &current, deadline).unwrap();
    assert!(!different.all_digests_match && !different.pairs[0].same_digest);
    graph.revalidate(&baseline, deadline).unwrap();
    assert_eq!(
        unsafe { libc::lseek(raw, 0, libc::SEEK_CUR) },
        3,
        "positional observation must not move original cursor"
    );
    assert_eq!(server.client().available().unwrap(), 2);
    assert_eq!(
        flags,
        descriptors
            .iter()
            .map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) })
            .collect::<Vec<_>>()
    );
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    drop((baseline, candidate, current, graph));
    let local = original.seal_graph().expect("actual native workers must be joined");
    drop(local);
    assert!(
        OutputLock::try_acquire(&output).unwrap().is_none(),
        "local join cannot release original output custody"
    );
    assert!(
        !Manager::open(&source).unwrap().status().unwrap().is_free(),
        "local join cannot release durable WITHHELD exclusion"
    );
    drop(held);
    assert_eq!(server.client().available().unwrap(), 3);
    println!("native-graph-checked");
}

#[test]
fn malformed_selection_and_foreign_owner_cannot_reinterpret_original_inputs() {
    if isolated(
        "engine::graph::native::tests::malformed_selection_and_foreign_owner_cannot_reinterpret_original_inputs",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    let deadline = Instant::now() + Duration::from_secs(30);
    fs::write(source.join("input.rs"), b"pub fn fixed() -> u8 { 7 }\n").unwrap();
    std::os::unix::fs::symlink("input.rs", source.join("alias.rs")).unwrap();
    let fifo = std::ffi::CString::new(source.join("pipe").as_os_str().as_encoded_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(0).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    assert!(matches!(graph.capture_inputs(&[], deadline), Err(GraphError::InvalidReadSet(_))));
    for paths in [
        vec![PathBuf::from("../input.rs")],
        vec![PathBuf::from("/input.rs")],
        vec![PathBuf::from("input.rs"), PathBuf::from("input.rs")],
    ] {
        assert!(matches!(
            graph.capture_inputs(&paths, deadline),
            Err(GraphError::InvalidReadSet(_))
        ));
    }
    assert!(graph.capture_inputs(&[PathBuf::from("alias.rs")], deadline).is_err());
    assert!(
        graph.capture_inputs(&[PathBuf::from("pipe")], deadline).is_err(),
        "nonregular open must not block on FIFO"
    );
    let snapshot = graph.capture_inputs(&[PathBuf::from("input.rs")], deadline).unwrap();
    let (_foreign, foreign) = root();
    let (_foreign_out, foreign_out) = root();
    let second = outcome(&foreign, &foreign_out, deadline, false);
    let other = second.open_native_graph().unwrap();
    assert!(matches!(other.revalidate(&snapshot, deadline), Err(GraphError::WrongOwner)));
    assert!(
        other.capture_inputs(&[PathBuf::from("absent.rs")], deadline).is_err(),
        "uninstalled second owner cannot dispatch"
    );
    assert!(
        original
            .protected
            .as_ref()
            .unwrap()
            .native_graph_owner()
            .unwrap()
            .same_original_directory(&fs::File::open(&source).unwrap())
            .unwrap()
    );
    assert!(
        !original
            .protected
            .as_ref()
            .unwrap()
            .native_graph_owner()
            .unwrap()
            .same_original_directory(&fs::File::open(&foreign).unwrap())
            .unwrap()
    );
    let old = source.join("input.rs");
    fs::rename(&old, source.join("retired.rs")).unwrap();
    fs::write(&old, b"pub fn fixed() -> u8 { 7 }\n").unwrap();
    assert!(
        matches!(graph.revalidate(&snapshot, deadline), Err(GraphError::InputChanged(_))),
        "same-byte inode replacement must fail"
    );
    println!("native-graph-checked");
}

#[test]
fn expired_operation_refuses_without_returning_or_replacing_original_execution() {
    if isolated(
        "engine::graph::native::tests::expired_operation_refuses_without_returning_or_replacing_original_execution",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::write(source.join("input.rs"), b"pub fn fixed() -> bool { true }\n").unwrap();
    let server = Jobserver::new(1).unwrap();
    crate::utils::metadata_scheduler::install_test_original(server.clone()).unwrap();
    let original = outcome(&source, &output, Instant::now() + Duration::from_secs(20), true);
    assert!(
        matches!(original.open_native_graph().unwrap().capture_inputs(&[PathBuf::from("input.rs")], Instant::now()), Err(GraphError::Io(error)) if error.kind() == io::ErrorKind::TimedOut)
    );
    assert_eq!(server.client().available().unwrap(), 1);
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    original.check_execution_scope().unwrap();
    // A stricter expired caller budget never extends/replaces the real original deadline.
    original
        .compare_source_inputs(
            &[PathBuf::from("input.rs")],
            &[PathBuf::from("input.rs")],
            Instant::now() + Duration::from_secs(5),
        )
        .unwrap();
    println!("native-graph-checked");
}

#[test]
fn original_deadline_crossing_still_joins_the_actual_native_worker_and_retains_custody() {
    if isolated(
        "engine::graph::native::tests::original_deadline_crossing_still_joins_the_actual_native_worker_and_retains_custody",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    let server = Jobserver::new(2).unwrap();
    crate::utils::metadata_scheduler::install_test_original(server.clone()).unwrap();
    let original_deadline = Instant::now() + Duration::from_secs(2);
    let original = outcome(&source, &output, original_deadline, true);
    let owner = original.protected.as_ref().unwrap().native_graph_owner().unwrap();
    let finished = std::sync::atomic::AtomicBool::new(false);
    let actual = crate::utils::metadata_scheduler::run_native_worker(
        owner.identity(),
        original_deadline + Duration::from_secs(30),
        |effective| {
            assert_eq!(
                effective, original_deadline,
                "a later request cannot extend original containment"
            );
            std::thread::sleep(
                effective.saturating_duration_since(Instant::now()) + Duration::from_millis(30),
            );
            finished.store(true, std::sync::atomic::Ordering::Release);
        },
    );
    assert!(actual.is_err(), "late completion cannot publish a positive native result");
    assert!(
        finished.load(std::sync::atomic::Ordering::Acquire),
        "lexical owner must join the actual late worker before returning"
    );
    let dispatched = std::sync::atomic::AtomicBool::new(false);
    assert!(
        crate::utils::metadata_scheduler::run_native_worker(
            owner.identity(),
            original_deadline + Duration::from_secs(30),
            |_| dispatched.store(true, std::sync::atomic::Ordering::Release)
        )
        .is_err()
    );
    assert!(!dispatched.load(std::sync::atomic::Ordering::Acquire));
    assert_eq!(server.client().available().unwrap(), 2);
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    drop(original);
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    assert!(!Manager::open(&source).unwrap().status().unwrap().is_free());
    println!("native-graph-checked");
}

#[test]
fn actual_source_producer_validator_and_test_share_original_dependency_owners() {
    if isolated(
        "engine::graph::native::tests::actual_source_producer_validator_and_test_share_original_dependency_owners",
    ) {
        return;
    }
    use std::sync::atomic::{AtomicUsize, Ordering};
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::write(source.join("input.txt"), b"17\n").unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    let server = Jobserver::new(2).unwrap();
    crate::utils::metadata_scheduler::install_test_original(server.clone()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    let selected = [PathBuf::from("input.txt")];
    let callbacks = AtomicUsize::new(0);
    let input = graph.capture_inputs(&selected, deadline).unwrap();
    let raw = input.native.entries[0].file.as_raw_fd();
    assert_eq!(unsafe { libc::lseek(raw, 1, libc::SEEK_SET) }, 1);
    let flags = unsafe { libc::fcntl(raw, libc::F_GETFD) };
    let producer = graph
        .run_source_task(input, &[], deadline, |actual| {
            callbacks.fetch_add(1, Ordering::SeqCst);
            let bytes = actual.read(0)?;
            assert!(actual.read(1).is_err(), "no undeclared input access");
            let number = std::str::from_utf8(&bytes).unwrap().trim().parse::<u32>().unwrap();
            Ok::<_, GraphError>(number.checked_mul(3).unwrap())
        })
        .unwrap();
    assert_eq!(*producer.value(), 51);
    assert_eq!(unsafe { libc::lseek(raw, 0, libc::SEEK_CUR) }, 1);
    assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFD) }, flags);
    let validator = graph
        .run_source_task(
            graph.capture_inputs(&selected, deadline).unwrap(),
            &[producer.completion()],
            deadline,
            |actual| {
                callbacks.fetch_add(1, Ordering::SeqCst);
                let input = actual.read(0)?;
                assert_eq!(input, b"17\n");
                assert_eq!(*producer.value() / 3, 17);
                Ok::<_, GraphError>(*producer.value())
            },
        )
        .unwrap();
    let test = graph
        .run_source_task(
            graph.capture_inputs(&selected, deadline).unwrap(),
            &[validator.completion()],
            deadline,
            |actual| {
                callbacks.fetch_add(1, Ordering::SeqCst);
                assert_eq!(actual.read(0)?, b"17\n");
                Ok::<_, GraphError>(*validator.value() == 51)
            },
        )
        .unwrap();
    assert!(*test.value());
    assert_eq!(callbacks.load(Ordering::SeqCst), 3, "callbacks must really execute");
    assert_eq!(server.client().available().unwrap(), 2, "native work creates no GNU credits");
    assert!(!original.has_completed_runtime());
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    drop((test, validator, producer, graph));
    drop(original.seal_graph().expect("actual source workers must join"));
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    assert!(!Manager::open(&source).unwrap().status().unwrap().is_free());
    println!("native-graph-checked");
}

#[test]
fn source_task_errors_mutation_and_invalid_dependencies_never_publish_completion() {
    if isolated(
        "engine::graph::native::tests::source_task_errors_mutation_and_invalid_dependencies_never_publish_completion",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::write(source.join("first.txt"), b"original").unwrap();
    fs::write(source.join("second.txt"), b"unchanged").unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(1).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    let selected = [PathBuf::from("first.txt")];
    let producer = graph
        .run_source_task(
            graph.capture_inputs(&selected, deadline).unwrap(),
            &[],
            deadline,
            |actual| actual.read(0),
        )
        .unwrap();
    let ran = std::sync::atomic::AtomicBool::new(false);
    let duplicates = graph.run_source_task(
        graph.capture_inputs(&selected, deadline).unwrap(),
        &[producer.completion(), producer.completion()],
        deadline,
        |_| {
            ran.store(true, std::sync::atomic::Ordering::SeqCst);
            Ok::<_, GraphError>(())
        },
    );
    assert!(
        matches!(duplicates, Err(ref e) if matches!(e.error(), TaskError::Graph(GraphError::InvalidDependencies(_))))
    );
    assert!(!ran.load(std::sync::atomic::Ordering::SeqCst));
    let failed = graph.run_source_task(
        graph.capture_inputs(&selected, deadline).unwrap(),
        &[producer.completion()],
        deadline,
        |_| Err::<(), _>("actual validator rejected"),
    );
    assert!(
        matches!(failed, Err(ref e) if matches!(e.error(), TaskError::Work("actual validator rejected")))
    );
    let changed = graph.run_source_task(
        graph.capture_inputs(&selected, deadline).unwrap(),
        &[producer.completion()],
        deadline,
        |_| {
            fs::write(source.join("first.txt"), b"changed during work").unwrap();
            Ok::<_, GraphError>(47)
        },
    );
    assert!(
        matches!(changed, Err(ref e) if matches!(e.error(), TaskError::Graph(GraphError::InputChanged(_))))
    );
    assert_eq!(
        changed.as_ref().err().unwrap().returned_value(),
        Some(&47),
        "actual callback output survives a rejected input bookend as data only"
    );
    let remaining = graph.capture_inputs(&[PathBuf::from("second.txt")], deadline).unwrap();
    let descendant = graph.run_source_task(remaining, &[producer.completion()], deadline, |_| {
        ran.store(true, std::sync::atomic::Ordering::SeqCst);
        Ok::<_, GraphError>(())
    });
    assert!(descendant.is_err(), "changed predecessor must prevent dependent execution");
    assert!(!ran.load(std::sync::atomic::Ordering::SeqCst));
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}

#[test]
fn source_task_rejects_foreign_dependencies_before_work() {
    if isolated(
        "engine::graph::native::tests::source_task_rejects_foreign_dependencies_before_work",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::write(source.join("input.txt"), b"original").unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(1).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    let selected = [PathBuf::from("input.txt")];
    let producer = graph
        .run_source_task(
            graph.capture_inputs(&selected, deadline).unwrap(),
            &[],
            deadline,
            |actual| actual.read(0),
        )
        .unwrap();
    let (_foreign, foreign) = root();
    let (_foreign_out, foreign_out) = root();
    let foreign_owner = outcome(&foreign, &foreign_out, deadline, false);
    let other = foreign_owner.open_native_graph().unwrap();
    // Both the capture and completion are real owners from the original graph.
    // The foreign graph must reject the predecessor before attempting any work.
    let foreign_inputs = graph.capture_inputs(&selected, deadline).unwrap();
    let ran = std::sync::atomic::AtomicBool::new(false);
    let refused = other.run_source_task(foreign_inputs, &[producer.completion()], deadline, |_| {
        ran.store(true, std::sync::atomic::Ordering::SeqCst);
        Ok::<_, GraphError>(())
    });
    assert!(
        matches!(refused, Err(ref e) if matches!(e.error(), TaskError::Graph(GraphError::WrongDependencyOwner)))
    );
    assert!(!ran.load(std::sync::atomic::Ordering::SeqCst));
    println!("native-graph-checked");
}

#[test]
fn held_input_parent_replacement_and_restore_permanently_refuses_native_work() {
    if isolated(
        "engine::graph::native::tests::held_input_parent_replacement_and_restore_permanently_refuses_native_work",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::create_dir_all(source.join("package/src")).unwrap();
    let path = source.join("package/src/input.txt");
    fs::write(&path, b"original").unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(1).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    let selected = [PathBuf::from("package/src/input.txt")];
    let captured = graph.capture_inputs(&selected, deadline).unwrap();
    let file_stamp = Stamp::of(&captured.native.entries[0].file.metadata().unwrap());
    fs::rename(source.join("package/src"), source.join("package/retired")).unwrap();
    fs::create_dir(source.join("package/src")).unwrap();
    fs::write(&path, b"same visible bytes").unwrap();
    fs::remove_file(&path).unwrap();
    fs::remove_dir(source.join("package/src")).unwrap();
    fs::rename(source.join("package/retired"), source.join("package/src")).unwrap();
    assert!(
        file_stamp == Stamp::of(&captured.native.entries[0].file.metadata().unwrap()),
        "the held file itself was untouched"
    );
    assert!(
        graph.revalidate(&captured, deadline).is_err(),
        "actual original parent clock must detect ABA"
    );
    let ran = std::sync::atomic::AtomicBool::new(false);
    let refused = graph.run_source_task(captured, &[], deadline, |_| {
        ran.store(true, std::sync::atomic::Ordering::SeqCst);
        Ok::<_, GraphError>(())
    });
    assert!(refused.is_err());
    assert!(!ran.load(std::sync::atomic::Ordering::SeqCst));
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}

#[test]
fn original_source_root_clock_detects_top_level_parent_aba_without_new_directory_owner() {
    if isolated(
        "engine::graph::native::tests::original_source_root_clock_detects_top_level_parent_aba_without_new_directory_owner",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::create_dir(source.join("package")).unwrap();
    fs::write(source.join("package/input.txt"), b"original").unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(1).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    let captured = graph.capture_inputs(&[PathBuf::from("package/input.txt")], deadline).unwrap();
    let raw = captured.native.root.directory().unwrap().as_raw_fd();
    let root_stamp = Stamp::of(&captured.native.root.metadata().unwrap());
    let file_stamp = Stamp::of(&captured.native.entries[0].file.metadata().unwrap());
    fs::rename(source.join("package"), source.join("retired")).unwrap();
    fs::create_dir(source.join("package")).unwrap();
    fs::remove_dir(source.join("package")).unwrap();
    fs::rename(source.join("retired"), source.join("package")).unwrap();
    assert!(root_stamp != Stamp::of(&captured.native.root.metadata().unwrap()));
    assert!(file_stamp == Stamp::of(&captured.native.entries[0].file.metadata().unwrap()));
    assert_eq!(raw, captured.native.root.directory().unwrap().as_raw_fd());
    let refused = graph.revalidate(&captured, deadline);
    assert!(matches!(refused, Err(GraphError::InputChanged(ref path)) if *path == source));
    assert!(graph.revalidate(&captured, deadline).is_err());
    println!("native-graph-checked");
}

#[test]
fn callback_rejection_and_final_input_failure_both_survive_in_the_structured_failure() {
    if isolated(
        "engine::graph::native::tests::callback_rejection_and_final_input_failure_both_survive_in_the_structured_failure",
    ) {
        return;
    }
    let (_directory, source) = root();
    let (_out, output) = root();
    fs::write(source.join("input.txt"), b"original").unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    crate::utils::metadata_scheduler::install_test_original(Jobserver::new(1).unwrap()).unwrap();
    let original = outcome(&source, &output, deadline, true);
    let graph = original.open_native_graph().unwrap();
    let captured = graph.capture_inputs(&[PathBuf::from("input.txt")], deadline).unwrap();
    let refused = graph.run_source_task(captured, &[], deadline, |actual| {
        assert_eq!(actual.read(0).unwrap(), b"original");
        fs::write(source.join("input.txt"), b"changed").unwrap();
        Err::<(), _>("actual test rejected")
    });
    let failure = refused.err().unwrap();
    assert!(matches!(
        failure.error(),
        TaskError::WorkAndGraph {
            work: "actual test rejected",
            graph: GraphError::InputChanged(_)
        }
    ));
    assert!(failure.returned_value().is_none());
    assert_eq!(failure.observations()[0].bytes, 8);
    assert!(OutputLock::try_acquire(&output).unwrap().is_none());
    println!("native-graph-checked");
}
