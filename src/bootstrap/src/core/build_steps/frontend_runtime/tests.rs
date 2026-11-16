use super::*;
use crate::core::build_steps::compile;
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

#[test]
fn parsed_preflight_refuses_unsupported_routes_without_session_or_ownership() {
    for (stage, args, omit_hash) in [
        (2, vec![], false),
        (1, vec!["--keep-stage", "1"], false),
        (1, vec!["--skip", "compiler/rustc"], false),
        (1, vec!["--host", "i686-unknown-haiku"], false),
        (1, vec![], true),
    ] {
        let context = TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", &format!("rust.omit-git-hash={omit_hash}")])
            .args(&args)
            .path("frontend-runtime-owner")
            .create_config();
        assert!(validate_config(&config).is_err(), "unsupported parsed route: {args:?}");
    }
    let context = TestCtx::new();
    let mut config = context
        .config("build")
        .stage(1)
        .args(&["--set", "rust.omit-git-hash=false"])
        .path("frontend-runtime-owner")
        .create_config();
    assert!(validate_config(&config).is_ok());
    // A raw configured commit must refuse without initializing the effectful
    // download accessor. No declared commit is fetched to decide eligibility.
    config.download_rustc_commit = Some("0".repeat(40));
    assert!(validate_config(&config).is_err());
}

#[test]
fn completed_runtime_plans_all_original_producers_but_dry_run_never_constructs_owner() {
    let context = TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "build.extended=true", "--set", "rust.omit-git-hash=false"])
        .path("frontend-runtime-owner")
        .create_config();
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(!FrontendRuntime::is_default_step(&builder));
    builder.execute_cli();
    let cache = builder.step_cache();
    assert!(cache.contains::<compile::Rustc>());
    assert!(cache.contains::<compile::Std>());
    assert!(cache.contains::<tool::Rustdoc>());
    assert!(cache.contains::<tool::Cargo>());
    assert!(cache.contains::<tool::TCargoTrust>());
    assert!(cache.contains::<tool::Trustd>());
    assert!(!cache.contains::<tool::TCargoTrustBuildTool>());
    assert_eq!(
        cache.inspect_all_steps_of_type::<FrontendRuntime, _>(|_, owner| owner.is_none()),
        vec![true]
    );
}

#[test]
fn completed_runtime_refuses_kept_skipped_and_unbound_routes_before_normal_producers() {
    for args in [
        vec!["--set", "rust.omit-git-hash=false", "--keep-stage", "1"],
        vec!["--set", "rust.omit-git-hash=false", "--skip", "compiler/rustc"],
        vec!["--set", "rust.omit-git-hash=true"],
    ] {
        let context = TestCtx::new();
        let config = context
            .config("build")
            .stage(1)
            .args(&args)
            .path("frontend-runtime-owner")
            .create_config();
        let session = Session::new(config);
        let builder = Builder::new(&session);
        assert!(validate_request(&builder, builder.host_target).is_err());
        assert!(!builder.step_cache().contains::<compile::Rustc>());
    }
}

#[test]
fn completed_runtime_refuses_foreign_and_later_stage_before_building() {
    for stage in [1, 2] {
        let context = TestCtx::new();
        let config = context
            .config("build")
            .stage(stage)
            .args(&["--set", "rust.omit-git-hash=false"])
            .path("frontend-runtime-owner")
            .create_config();
        let session = Session::new(config);
        let builder = Builder::new(&session);
        assert_eq!(validate_request(&builder, builder.host_target).is_ok(), stage == 1);
        let foreign = if builder.host_target.triple == "i686-unknown-haiku" {
            "i686-unknown-hurd-gnu"
        } else {
            "i686-unknown-haiku"
        };
        assert!(validate_request(&builder, TargetSelection::from_user(foreign)).is_err());
        assert!(!builder.step_cache().contains::<compile::Rustc>());
    }
}

#[test]
fn completed_runtime_cli_refuses_foreign_and_mixed_hosts_before_producers() {
    for hosts in [
        vec!["i686-unknown-haiku"],
        vec!["x86_64-unknown-linux-gnu", "i686-unknown-haiku"],
        vec!["i686-unknown-haiku", "x86_64-unknown-linux-gnu"],
    ] {
        let context = TestCtx::new();
        let config = context
            .config("build")
            .stage(1)
            .args(&["--build", "x86_64-unknown-linux-gnu", "--set", "rust.omit-git-hash=false"])
            .hosts(&hosts)
            .path("frontend-runtime-owner")
            .create_config();
        let session = Session::new(config);
        let builder = Builder::new(&session);
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            builder.execute_cli();
        }));
        assert!(refused.is_err(), "host selection unexpectedly accepted: {hosts:?}");
        assert!(!builder.step_cache().contains::<compile::Rustc>());
        assert!(!builder.step_cache().contains::<compile::Std>());
        assert!(session.completed_runtime.borrow().is_none());
    }
}

#[test]
fn completed_runtime_host_restriction_preserves_separate_std_targets() {
    let context = TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "rust.omit-git-hash=false"])
        .targets(&["i686-unknown-haiku"])
        .path("frontend-runtime-owner")
        .create_config();
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(validate_request(&builder, builder.host_target).is_ok());
}

#[test]
fn completed_runtime_refuses_mixed_selections_before_any_cached_producer_can_be_used() {
    let context = TestCtx::new();
    let config = context
        .config("build")
        .stage(1)
        .args(&["--set", "rust.omit-git-hash=false"])
        .path("frontend-runtime-owner")
        .path("compiler/rustc")
        .create_config();
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(validate_request(&builder, builder.host_target).is_err());
    assert!(!builder.step_cache().contains::<compile::Rustc>());
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn completed_runtime_retains_same_original_output_and_command_guards() {
    use build_helper::trust_output_lock::OutputLock;
    use build_helper::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};
    const PROBE: &str = "TRUST_TEST_COMPLETED_RUNTIME_LOCK_ROOT";
    const EXPECT: &str = "TRUST_TEST_COMPLETED_RUNTIME_EXPECT_FREE";
    const NAME: &str = "core::build_steps::frontend_runtime::tests::completed_runtime_retains_same_original_output_and_command_guards";
    if let Some(path) = std::env::var_os(PROBE) {
        let acquired = OutputLock::try_acquire_existing(std::path::Path::new(&path)).unwrap();
        assert_eq!(acquired.is_some(), std::env::var(EXPECT).unwrap() == "1");
        return;
    }
    // Trust: it releases the output lock and has a child take it at once, which a
    // child another test thread forks could share (crate::utils::tests::isolated;
    // LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)).
    crate::utils::tests::isolated(|| {
        let root = tempfile::tempdir().unwrap();
        let out_dir = tempfile::tempdir().unwrap();
        let output = Arc::new(OutputLock::try_acquire(out_dir.path()).unwrap().unwrap());
        let request = Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "completed runtime ownership control".into(),
            contract: "actual original output and command owners".into(),
            wait: std::time::Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        };
        let command = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
            LeaseAcquisition::Granted(lease) => Arc::new(CommandOwnership::new(lease)),
            _ => panic!("owned native fixture unexpectedly busy"),
        };
        let retained_output = Arc::downgrade(&output);
        let retained_command = Arc::downgrade(&command);
        let original = BuildOwnership::new(Arc::clone(&output), Arc::clone(&command)).unwrap();
        drop(output);
        drop(command);
        original.check().unwrap();
        assert!(retained_output.upgrade().is_some());
        assert!(retained_command.upgrade().is_some());
        assert!(!Manager::open(root.path()).unwrap().status().unwrap().is_free());
        let probe = |free| {
            let observed = crate::test_entry::uncaptured_actor(std::process::Command::new(
                std::env::current_exe().unwrap(),
            ))
            .args(["--exact", NAME, "--nocapture"])
            .env(PROBE, out_dir.path())
            .env(EXPECT, if free { "1" } else { "0" })
            .output()
            .unwrap();
            assert!(
                observed.status.success(),
                "actual child lock observation failed: {:?}\n{}\n{}",
                observed.status,
                String::from_utf8_lossy(&observed.stdout),
                String::from_utf8_lossy(&observed.stderr)
            );
        };
        probe(false);
        drop(original);
        assert!(retained_output.upgrade().is_none());
        assert!(retained_command.upgrade().is_none());
        assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
        probe(true);
    });
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn graph_output_borrow_requires_actual_same_withheld_command_and_output_root() {
    use build_helper::trust_output_lock::OutputLock;
    use build_helper::trust_repo_lock::management::{
        Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
    };
    let root = tempfile::tempdir().unwrap();
    let foreign_root = tempfile::tempdir().unwrap();
    let output_root = tempfile::tempdir().unwrap();
    let foreign_output = tempfile::tempdir().unwrap();
    let acquire = |root: &std::path::Path| {
        let request = Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "original graph output borrow control".into(),
            contract: "actual guards only; no Host or Steps".into(),
            wait: std::time::Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        };
        match Manager::open(root).unwrap().acquire_lease(&request).unwrap() {
            LeaseAcquisition::Granted(lease) => Arc::new(CommandOwnership::new(lease)),
            _ => panic!("private original command unexpectedly busy"),
        }
    };
    let command = acquire(root.path());
    let foreign = acquire(foreign_root.path());
    let output = Arc::new(OutputLock::try_acquire(output_root.path()).unwrap().unwrap());
    let owned = BuildOwnership::new(Arc::clone(&output), Arc::clone(&command)).unwrap();
    // SAFETY: negative preflight only; no recipient or descriptor export.
    assert!(unsafe { owned.original_output(&command, output_root.path()) }.is_err());
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    let protected =
        ProtectedWorkScope::new(command.withhold_original().unwrap(), deadline).unwrap();
    protected.check_current().unwrap();
    {
        let _busy_original = command.lease.lock().unwrap();
        // SAFETY: negative preflight only. A busy actual state is refused
        // immediately rather than waiting on our own already held mutex.
        assert!(unsafe { owned.original_output(&command, output_root.path()) }.is_err());
    }
    // SAFETY: all borrowed descriptors stay local, close-only and unchanged;
    // these tests send no rights and retain the actual scope/guard throughout.
    unsafe {
        assert!(owned.original_output(&foreign, output_root.path()).is_err());
        assert!(owned.original_output(&command, foreign_output.path()).is_err());
        let original = owned.original_output(&command, output_root.path()).unwrap();
        assert_eq!(original.root(), std::fs::canonicalize(output_root.path()).unwrap());
        use std::os::fd::AsRawFd as _;
        assert_ne!(original.directory().as_raw_fd(), original.lock().as_raw_fd());
    }
    protected.check_current().unwrap();
    owned.check().unwrap();
    assert!(Manager::open(root.path()).unwrap().status().unwrap().holder.unwrap().is_withheld());
}
