use super::*;
use std::sync::Arc;

#[test]
fn absent_transport_lends_zero_extras_without_mutating_unit_process() {
    let owner = QueryOwner(Mutex::new(None));
    let mut command = ProcessBuilder::new("/bin/sh");
    command.args(&[
        "-c",
        "printf '%s' \"$CARGO_MAKEFLAGS\"; printf stderr >&2; exit 7",
    ]);
    assert!(!command.has_jobserver());
    let output = owner.output(&command, None).unwrap();
    assert_eq!(output.status.code(), Some(7));
    assert_eq!(output.stderr, b"stderr");
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("--jobserver-auth=")
    );
    assert!(!command.has_jobserver());
    assert_eq!(
        owner
            .0
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .client()
            .available()
            .unwrap(),
        0
    );
}

#[test]
fn real_inherited_pool_is_not_replaced_or_replenished() {
    let original = Jobserver::new(2).unwrap();
    let held = original.client().acquire().unwrap();
    let owner = QueryOwner(Mutex::new(None));
    let mut command = ProcessBuilder::new("/bin/sh");
    command.args(&["-c", "exit 0"]);
    assert!(
        owner
            .output(&command, Some(&original))
            .unwrap()
            .status
            .success()
    );
    assert!(owner.0.lock().unwrap().is_none());
    assert_eq!(original.client().available().unwrap(), 1);
    command.inherit_jobserver(&original);
    assert!(owner.output(&command, None).unwrap().status.success());
    assert!(owner.0.lock().unwrap().is_none());
    assert_eq!(original.client().available().unwrap(), 1);
    drop(held);
    assert_eq!(original.client().available().unwrap(), 2);
}

#[test]
fn parallel_queries_share_one_implicit_borrower_until_terminal() {
    let directory = tempfile::tempdir().unwrap();
    let active = directory.path().join("active");
    let owner = Arc::new(QueryOwner(Mutex::new(None)));
    let barrier = Arc::new(std::sync::Barrier::new(2));
    let threads: Vec<_> = (0..2)
        .map(|_| {
            let owner = Arc::clone(&owner);
            let barrier = Arc::clone(&barrier);
            let active = active.clone();
            std::thread::spawn(move || {
                let mut command = ProcessBuilder::new("/bin/sh");
                command
                    .args(&[
                        "-c",
                        "mkdir \"$1\" || exit 9; sleep 0.1; rmdir \"$1\"",
                        "sh",
                    ])
                    .arg(active);
                barrier.wait();
                owner.output(&command, None).unwrap()
            })
        })
        .collect();
    for thread in threads {
        assert!(thread.join().unwrap().status.success());
    }
    assert!(!active.exists());
}

#[test]
fn spawn_failure_preserves_exclusive_owner_for_next_query() {
    let owner = QueryOwner(Mutex::new(None));
    assert!(
        owner
            .output(&ProcessBuilder::new("/no/such/compiler-query"), None)
            .is_err()
    );
    assert!(
        owner
            .output(&ProcessBuilder::new("/usr/bin/true"), None)
            .unwrap()
            .status
            .success()
    );
}

#[test]
fn poisoned_owner_cannot_lend_another_implicit_execution() {
    let owner = Arc::new(QueryOwner(Mutex::new(None)));
    let other = Arc::clone(&owner);
    assert!(
        std::thread::spawn(move || {
            let _guard = other.0.lock().unwrap();
            panic!("unwind borrower");
        })
        .join()
        .is_err()
    );
    assert!(
        owner
            .output(&ProcessBuilder::new("/usr/bin/true"), None)
            .is_err()
    );
}

#[test]
fn fresh_owned_query_defaults_preserve_explicit_inputs_and_actual_gnu_owner() {
    // This fixture only configures real ProcessBuilders and GNU guards. Its
    // executor cannot create a native owner or execute a compiler.
    struct NoExecute;
    impl ProcessExecutor for NoExecute {
        fn output(&self, _: &ProcessBuilder) -> std::io::Result<Output> {
            panic!("configuration must not execute")
        }
        fn status(&self, _: &ProcessBuilder) -> std::io::Result<std::process::ExitStatus> {
            panic!("configuration must not execute")
        }
        fn streaming(
            &self,
            _: &ProcessBuilder,
            _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
            _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
            _: bool,
            _: Option<cargo_util::StreamingOutputLimits>,
            _: bool,
        ) -> (cargo_util::ExecStats, anyhow::Result<Output>) {
            panic!("configuration must not execute")
        }
    }
    let original = Jobserver::new(1).unwrap();
    let foreign = Jobserver::new(1).unwrap();
    let baseline = EnvironmentInputs::from_variables([("LANG".into(), "baseline".into())]).unwrap();
    let ordinary = Scoped::new(
        baseline,
        original.clone(),
        Arc::new(NoExecute),
        "/original-source".into(),
    );
    let fresh = ordinary.clone().preserve_explicit_inputs();
    let mut defaults = ProcessBuilder::new("/selected-compiler");
    fresh.configure(&mut defaults);
    assert_eq!(
        defaults.get_cwd(),
        Some(std::path::Path::new("/original-source"))
    );
    assert_eq!(
        defaults
            .get_effective_envs()
            .unwrap()
            .get(std::ffi::OsStr::new("LANG")),
        Some(&std::ffi::OsString::from("baseline"))
    );
    let original_guard = original.client().acquire().unwrap();
    assert!(original_guard.belongs_to(defaults.get_jobserver().unwrap().client()));
    drop(original_guard);

    let mut explicit = ProcessBuilder::new("/selected-compiler");
    explicit
        .cwd("/explicit-source")
        .environment_snapshot(
            EnvironmentInputs::from_variables([("LANG".into(), "explicit".into())]).unwrap(),
        )
        .inherit_jobserver(&foreign);
    fresh.configure(&mut explicit);
    assert_eq!(
        explicit.get_cwd(),
        Some(std::path::Path::new("/explicit-source"))
    );
    assert_eq!(
        explicit
            .get_effective_envs()
            .unwrap()
            .get(std::ffi::OsStr::new("LANG")),
        Some(&std::ffi::OsString::from("explicit"))
    );
    let foreign_guard = foreign.client().acquire().unwrap();
    assert!(foreign_guard.belongs_to(explicit.get_jobserver().unwrap().client()));
    assert!(!foreign_guard.belongs_to(original.client()));
    drop(foreign_guard);

    // The existing ordinary coordinator retains its established defaults.
    ordinary.configure(&mut explicit);
    assert_eq!(
        explicit.get_cwd(),
        Some(std::path::Path::new("/original-source"))
    );
    assert_eq!(
        explicit
            .get_effective_envs()
            .unwrap()
            .get(std::ffi::OsStr::new("LANG")),
        Some(&std::ffi::OsString::from("baseline"))
    );
    let original_guard = original.client().acquire().unwrap();
    assert!(original_guard.belongs_to(explicit.get_jobserver().unwrap().client()));
}
