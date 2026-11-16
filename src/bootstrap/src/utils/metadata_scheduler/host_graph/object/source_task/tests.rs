//! Real source/Manager/output/native-worker controls. These construct no Host,
//! SDK, CompletedObjectCompile, published artifact or source-finalization owner.
use std::time::Duration;

use build_helper::trust_output_lock::OutputLock;
use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
};
use jobserver_utils::Jobserver;

use super::*;

fn isolated(name: &str) -> bool {
    const ROLE: &str = "TRUST_OBJECT_SOURCE_TASK_ACTOR";
    if std::env::var(ROLE).as_deref() == Ok(name) {
        return false;
    }
    let output = crate::test_entry::uncaptured_actor(std::process::Command::new(
        std::env::current_exe().unwrap(),
    ))
    .args(["--exact", name, "--nocapture"])
    .env(ROLE, name)
    .output()
    .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("original-source-task-checked"));
    true
}
struct World {
    scope: ProtectedWorkScope,
    source: Arc<OriginalSourceRoot>,
    output: Arc<BuildOwnership>,
    command: Arc<CommandOwnership>,
    source_path: PathBuf,
    output_path: PathBuf,
    deadline: Instant,
    _source: tempfile::TempDir,
    _output: tempfile::TempDir,
}
fn world() -> World {
    let source_dir = tempfile::tempdir().unwrap();
    let output_dir = tempfile::tempdir().unwrap();
    let root = std::fs::canonicalize(source_dir.path()).unwrap();
    let output_path = std::fs::canonicalize(output_dir.path()).unwrap();
    std::fs::create_dir_all(root.join("src/bootstrap")).unwrap();
    let source_path = root.join("src/bootstrap/native_object.rs");
    std::fs::write(&source_path, object::SOURCE_BYTES).unwrap();
    let lease = match Manager::open(&root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "actual source-task predecessor control".into(),
            contract: "original local source/output work only; no Host/SDK/return".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("private source unexpectedly busy"),
    };
    let command = Arc::new(CommandOwnership::new(lease));
    let deadline = Instant::now() + Duration::from_secs(20);
    let scope = ProtectedWorkScope::new(command.withhold_original().unwrap(), deadline).unwrap();
    let source = Arc::new(scope.original_source(&root).unwrap());
    let output = Arc::new(
        BuildOwnership::new(
            Arc::new(OutputLock::try_acquire(&output_path).unwrap().unwrap()),
            Arc::clone(&command),
        )
        .unwrap(),
    );
    World {
        scope,
        source,
        output,
        command,
        source_path,
        output_path,
        deadline,
        _source: source_dir,
        _output: output_dir,
    }
}
fn install(world: &World) -> Jobserver {
    let server = Jobserver::new(2).unwrap();
    crate::utils::metadata_scheduler::install_test_original(server.clone()).unwrap();
    crate::utils::exec::install_protected_scope(world.scope.dispatcher()).unwrap();
    server
}
fn capture(world: &World) -> Arc<Attempt> {
    Attempt::capture(
        Arc::clone(&world.source),
        Arc::clone(&world.output),
        Arc::clone(&world.command),
        world.scope.dispatcher(),
        world.deadline,
    )
    .unwrap()
}

#[test]
fn actual_source_task_binds_only_its_joined_original_record_and_preserves_descriptors() {
    if isolated(
        "utils::metadata_scheduler::host_graph::object::source_task::tests::actual_source_task_binds_only_its_joined_original_record_and_preserves_descriptors",
    ) {
        return;
    }
    let world = world();
    let server = install(&world);
    let first = Attempt::capture(
        Arc::clone(&world.source),
        Arc::clone(&world.output),
        Arc::clone(&world.command),
        world.scope.dispatcher(),
        world.deadline + Duration::from_secs(60),
    )
    .unwrap();
    assert_eq!(first.inputs.deadline, world.deadline, "actual scope narrows the entire node");
    let fd = first.inputs.file.as_raw_fd();
    assert_eq!(unsafe { libc::lseek(fd, 7, libc::SEEK_SET) }, 7);
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    let first_predecessor = first.run().unwrap();
    let second = capture(&world);
    let mut active = true;
    let second_predecessor = second.run().unwrap().finish_activity(&mut active, false).unwrap();
    assert!(!active);
    // Identical file DATA is not membership in another actual task census.
    assert!(
        first_predecessor
            .bind(&[Arc::clone(&second)], &world.source, &world.output, &world.command)
            .is_err()
    );
    let alias = Predecessor(Arc::clone(&second_predecessor.0));
    let bound = second_predecessor
        .bind(&[Arc::clone(&second)], &world.source, &world.output, &world.command)
        .unwrap();
    assert_eq!(bound.observation().sha256, object::SOURCE_SHA256);
    assert_eq!(bound.observation().bytes, object::SOURCE_BYTES.len() as u64);
    assert!(Arc::ptr_eq(&bound.0.inputs, &second.inputs));
    assert!(
        alias.bind(&[Arc::clone(&second)], &world.source, &world.output, &world.command).is_err()
    );
    assert!(first.run().is_err(), "completed tasks cannot issue another predecessor");
    assert_eq!(unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) }, 7);
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFD) }, flags);
    assert_eq!(server.client().available().unwrap(), 2);
    assert!(OutputLock::try_acquire(&world.output_path).unwrap().is_none());
    assert!(!Manager::open(world.source.path()).unwrap().status().unwrap().is_free());
    println!("original-source-task-checked");
}

#[test]
fn successful_source_read_is_retained_when_original_namespace_bookends_fail() {
    if isolated(
        "utils::metadata_scheduler::host_graph::object::source_task::tests::successful_source_read_is_retained_when_original_namespace_bookends_fail",
    ) {
        return;
    }
    let world = world();
    let _server = install(&world);
    let attempt = capture(&world);
    let fd = attempt.inputs.file.as_raw_fd();
    let result = attempt.run_with(|input, deadline| {
        let observed = input.read(deadline)?;
        let saved = world.source_path.with_extension("original");
        std::fs::rename(&world.source_path, &saved)?;
        std::fs::write(&world.source_path, b"different compiler input")?;
        std::fs::remove_file(&world.source_path)?;
        std::fs::rename(&saved, &world.source_path)?;
        Ok(observed)
    });
    assert!(result.is_err());
    let state = attempt.state.lock().unwrap();
    let State::Failed(failure) = &*state else {
        panic!("no failed original task");
    };
    assert_eq!(failure.returned.as_ref().unwrap().sha256, object::SOURCE_SHA256);
    assert!(failure.inner_bookend.is_some() && failure.outer_bookend.is_some());
    assert_eq!(attempt.inputs.file.as_raw_fd(), fd);
    assert_eq!(std::fs::read(&world.source_path).unwrap(), object::SOURCE_BYTES);
    drop(state);
    assert!(attempt.run().is_err(), "restoring A cannot recover the failed original capture");
    assert!(OutputLock::try_acquire(&world.output_path).unwrap().is_none());
    println!("original-source-task-checked");
}

#[test]
fn source_work_error_and_both_closing_errors_survive_without_a_predecessor() {
    if isolated(
        "utils::metadata_scheduler::host_graph::object::source_task::tests::source_work_error_and_both_closing_errors_survive_without_a_predecessor",
    ) {
        return;
    }
    let world = world();
    let _server = install(&world);
    let attempt = capture(&world);
    let result = attempt.run_with(|_, _| {
        std::fs::write(&world.source_path, b"changed actual source")?;
        Err(io::Error::from_raw_os_error(libc::EPERM))
    });
    assert_eq!(result.err().unwrap().kind(), io::ErrorKind::PermissionDenied);
    let state = attempt.state.lock().unwrap();
    let State::Failed(failure) = &*state else {
        panic!("missing failed task custody");
    };
    assert_eq!(failure.work.as_ref().unwrap().raw_os_error(), Some(libc::EPERM));
    assert!(failure.returned.is_none());
    assert!(failure.inner_bookend.is_some() && failure.outer_bookend.is_some());
    drop(state);
    assert!(attempt.run().is_err());
    println!("original-source-task-checked");
}

#[test]
fn panicking_source_worker_keeps_original_inputs_and_permanently_refuses_replay() {
    if isolated(
        "utils::metadata_scheduler::host_graph::object::source_task::tests::panicking_source_worker_keeps_original_inputs_and_permanently_refuses_replay",
    ) {
        return;
    }
    let world = world();
    let _server = install(&world);
    let attempt = capture(&world);
    let fd = attempt.inputs.file.as_raw_fd();
    assert!(attempt.run_with(|_, _| panic!("actual source worker unwind")).is_err());
    let state = attempt.state.lock().unwrap();
    let State::Failed(failure) = &*state else {
        panic!("missing unresolved native task");
    };
    assert!(failure.native.is_some());
    assert!(failure.returned.is_none());
    assert!(failure.outer_bookend.is_some());
    assert_eq!(attempt.inputs.file.as_raw_fd(), fd);
    assert!(attempt.inputs.file.metadata().unwrap().is_file());
    drop(state);
    assert!(attempt.run().is_err());
    assert!(OutputLock::try_acquire(&world.output_path).unwrap().is_none());
    println!("original-source-task-checked");
}

#[test]
fn poisoned_source_census_keeps_actual_returned_read_without_completion() {
    if isolated(
        "utils::metadata_scheduler::host_graph::object::source_task::tests::poisoned_source_census_keeps_actual_returned_read_without_completion",
    ) {
        return;
    }
    let world = world();
    let _server = install(&world);
    let attempt = capture(&world);
    let result = attempt.run_with(|input, deadline| {
        let observed = input.read(deadline)?;
        let poisoned = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = attempt.state.lock().unwrap();
            panic!("actual source census unwind");
        }));
        assert!(poisoned.is_err());
        Ok(observed)
    });
    assert!(result.is_err());
    let state = match attempt.state.lock() {
        Err(poisoned) => poisoned.into_inner(),
        Ok(_) => panic!("the native control must actually poison its census"),
    };
    let State::Failed(failure) = &*state else {
        panic!("poison must only retain failed custody");
    };
    assert_eq!(failure.returned.as_ref().unwrap().sha256, object::SOURCE_SHA256);
    assert!(failure.census.is_some());
    assert!(failure.native.is_none());
    assert!(failure.inner_bookend.is_none() && failure.outer_bookend.is_none());
    assert!(attempt.inputs.file.metadata().unwrap().is_file());
    drop(state);
    assert!(attempt.run().is_err());
    assert!(OutputLock::try_acquire(&world.output_path).unwrap().is_none());
    println!("original-source-task-checked");
}

#[test]
fn terminal_refusal_during_actual_source_work_survives_its_successful_join() {
    if isolated(
        "utils::metadata_scheduler::host_graph::object::source_task::tests::terminal_refusal_during_actual_source_work_survives_its_successful_join",
    ) {
        return;
    }
    let world = world();
    let _server = install(&world);
    let attempt = capture(&world);
    // Only the local in-progress/terminal restriction is represented here;
    // no Host, accepted graph or output-completion owner is fabricated.
    let restrictions = Mutex::new((true, false));
    let predecessor = attempt
        .run_with(|input, deadline| {
            let observed = input.read(deadline)?;
            restrictions.lock().unwrap().1 = true;
            Ok(observed)
        })
        .unwrap();
    let mut restrictions = restrictions.lock().unwrap();
    let terminal_failed = restrictions.1;
    assert!(predecessor.finish_activity(&mut restrictions.0, terminal_failed).is_err());
    assert!(restrictions.0 && restrictions.1, "a real read/join cannot erase a terminal veto");
    let state = attempt.state.lock().unwrap();
    let State::Complete(record) = &*state else {
        panic!("the actual local source work must have completed");
    };
    assert_eq!(record.observed.sha256, object::SOURCE_SHA256);
    assert!(!record.claimed.load(Ordering::Acquire), "no object consumed the vetoed task");
    assert!(attempt.inputs.file.metadata().unwrap().is_file());
    drop(state);
    assert!(attempt.run().is_err());
    assert!(OutputLock::try_acquire(&world.output_path).unwrap().is_none());
    println!("original-source-task-checked");
}
