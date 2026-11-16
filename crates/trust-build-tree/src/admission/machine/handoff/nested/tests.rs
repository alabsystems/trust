use std::os::fd::AsRawFd;

use super::*;

const TEST: &str = "admission::resources::machine::handoff::tests::nested_tests::actual_nested_child_keeps_original_group_claim_and_gnu_without_second_admission";
const MODE: &str = "TRUST_NESTED_FIXED_ACTOR";

fn imported(prepared: &PreparedFixedCommand, root: &Path) -> InheritedFixedClaim {
    read(prepared, &root.join("legacy")).unwrap()
}

fn original_gnu() -> jobserver_utils::Jobserver {
    let server = jobserver_utils::Jobserver::new(2).unwrap();
    // Consume the one actual implicit credit before lending that SAME serial
    // continuation. Neither preparation nor nested launch creates a credit.
    server.client().acquire_raw().unwrap();
    server
}

fn fd_identity(fd: i32) -> (u64, u64) {
    let mut s = std::mem::MaybeUninit::<libc::stat>::uninit();
    assert_eq!(unsafe { libc::fstat(fd, s.as_mut_ptr()) }, 0);
    let s = unsafe { s.assume_init() };
    (s.st_dev as u64, s.st_ino)
}

#[test]
fn actual_nested_child_keeps_original_group_claim_and_gnu_without_second_admission() {
    if std::env::var_os(MODE).is_none() {
        // Cargo's test harness adds a loader search override even for this
        // system-only test image. Isolate the fixture in its actual child;
        // production must continue to refuse every such ambient override.
        let mut command = Command::new(std::env::current_exe().unwrap());
        command.args(["--exact", TEST, "--nocapture"]).env(MODE, "owner");
        for (name, _) in std::env::vars_os() {
            if name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_") {
                command.env_remove(name);
            }
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output
                .stdout
                .windows(b"native-nested-owner-complete".len())
                .any(|part| part == b"native-nested-owner-complete")
        );
        return;
    }
    if std::env::var_os(MODE).as_deref() == Some(OsStr::new("receiver")) {
        // First descriptor import in this actual actor, before opening any
        // output/fixture files. This is the actual native GNU importer.
        let server = unsafe { jobserver_utils::Jobserver::from_env() }.unwrap().unwrap();
        assert_eq!(std::env::var("CARGO_BUILD_JOBS").unwrap(), "1");
        let flags = std::env::var_os("CARGO_MAKEFLAGS").unwrap();
        assert_eq!(std::env::var_os("MAKEFLAGS").unwrap(), flags);
        assert_eq!(std::env::var_os("MFLAGS").unwrap(), flags);
        let expected: Vec<(u64, u64)> =
            serde_json::from_str(&std::env::var("TRUST_NESTED_GNU_IDENTITIES").unwrap()).unwrap();
        let actual =
            server.pipe_descriptors().unwrap().each_ref().map(|fd| fd_identity(fd.as_raw_fd()));
        assert_eq!(actual.as_slice(), expected);
        assert_eq!(
            unsafe { libc::getpgrp() }.to_string(),
            std::env::var("TRUST_NESTED_PARENT_GROUP").unwrap()
        );
        assert_eq!(
            unsafe { libc::getsid(0) }.to_string(),
            std::env::var("TRUST_NESTED_PARENT_SESSION").unwrap()
        );
        assert_eq!(std::env::var_os(FIXED_HANDOFF_ENV).unwrap(), "requires-live-ancestor-v1");
        let (packet, originals) = jobserver_utils::recover_fixed_claim(
            &std::env::var_os(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV).unwrap(),
        )
        .unwrap();
        let root = PathBuf::from(std::env::var_os("TRUST_NESTED_PRIVATE_ROOT").unwrap());
        // This private-domain control uses the same complete native reader;
        // production always selects the canonical domain independently.
        let inherited = InheritedFixedClaim::read_file(
            packet.into(),
            &root.join("legacy"),
            width(2),
            Some(originals),
        )
        .unwrap();
        inherited.check_nested(width(1), Some(&root.join("worktree.lock")), false).unwrap();
        // Observe the SAME real fixed originals recovered over the live
        // ancestor courier. Policy data neither creates another reservation
        // nor widens the actual fixed/GNU continuation.
        let mut request =
            crate::admission::budget::Request::new(crate::admission::budget::Workload::FastLane);
        request.maximum_jobs = Some(
            inherited.limited_budget(std::env::var_os("CARGO_BUILD_JOBS").as_deref()).unwrap(),
        );
        let budget = crate::admission::budget::current(&request, Some(&inherited)).unwrap();
        assert_eq!(
            budget.cpu_scope,
            crate::admission::budget::CpuScope::OriginalFixed { ceiling: 2 }
        );
        assert!(budget.plan.jobs <= 1);
        assert_eq!(
            budget.overlap,
            Some(crate::admission::budget::Overlap::OriginalFixedRequiresSerial)
        );
        fs::write(root.join("actor-ran"), b"actual-nested-originals").unwrap();
        if std::env::var_os("TRUST_NESTED_WAIT_FOR_CANCEL").is_some() {
            loop {
                std::thread::sleep(Duration::from_secs(1));
            }
        }
        return;
    }
    for cancel in [false, true] {
        let (root, claim) = fixture_with_budget(2);
        let prepared = claim.prepare_command(Command::new("unused")).unwrap();
        let original = imported(&prepared, root.path());
        let server = original_gnu();
        let before = server.client().available().unwrap();
        let fds = server.pipe_descriptors().unwrap();
        let identities = fds.each_ref().map(|fd| fd_identity(fd.as_raw_fd()));
        let flags = fds.each_ref().map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) });
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", TEST, "--nocapture"])
            .env(MODE, "receiver")
            .env("TRUST_NESTED_PRIVATE_ROOT", root.path())
            .env("TRUST_NESTED_GNU_IDENTITIES", serde_json::to_string(&identities).unwrap())
            .env("TRUST_NESTED_PARENT_GROUP", unsafe { libc::getpgrp() }.to_string())
            .env("TRUST_NESTED_PARENT_SESSION", unsafe { libc::getsid(0) }.to_string());
        if cancel {
            command.env("TRUST_NESTED_WAIT_FOR_CANCEL", "1");
        }
        let record = original.record.clone();
        // SAFETY: the private native fixture owns this original fixed claim
        // and the one original GNU pool, lends its implicit continuation
        // serially, and retains the actual parent owner through both waits.
        let prepared_child = unsafe {
            original.prepare_nested_command(
                command,
                server.clone(),
                width(1),
                Some(&root.path().join("worktree.lock")),
                false,
                Instant::now() + Duration::from_secs(30),
            )
        }
        .unwrap();
        let mut child = prepared_child.spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        while !root.path().join("actor-ran").is_file() {
            assert!(Instant::now() < deadline, "actual child did not reach its canary");
            std::thread::sleep(Duration::from_millis(1));
        }
        if cancel {
            use std::os::unix::process::ExitStatusExt as _;
            assert_eq!(child.cancel().unwrap().signal(), Some(libc::SIGKILL));
        } else {
            assert!(child.wait().unwrap().success());
        }
        assert_eq!(before, server.client().available().unwrap());
        assert_eq!(
            flags,
            fds.each_ref().map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) })
        );
        assert_eq!(prepared.claim.record, record);
        assert!(!crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
        assert!(!crate::admission::resources::tests::released(&root.path().join("worktree.lock")));
        drop(child);
        prepared.claim.check_current().unwrap();
    }
    println!("native-nested-owner-complete");
}

#[test]
fn nested_preparation_refuses_expired_budget_and_transport_overrides_before_birth() {
    for mode in ["expired", "handoff", "loader"] {
        let (root, claim) = fixture_with_budget(2);
        let prepared = claim.prepare_command(Command::new("unused")).unwrap();
        let original = imported(&prepared, root.path());
        let mut command = Command::new(std::env::current_exe().unwrap());
        for (name, _) in std::env::vars_os() {
            if name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_") {
                command.env_remove(name);
            }
        }
        match mode {
            "handoff" => {
                command.env(FIXED_HANDOFF_ENV, "caller-data");
            }
            "loader" => {
                command.env("DYLD_INSERT_LIBRARIES", "unobserved");
            }
            _ => {}
        }
        let deadline = if mode == "expired" {
            Instant::now()
        } else {
            Instant::now() + Duration::from_secs(30)
        };
        // SAFETY: same original private fixture/serial GNU ownership; all
        // these controls must refuse before any child can be born.
        let error = unsafe {
            original.prepare_nested_command(
                command,
                original_gnu(),
                width(1),
                Some(&root.path().join("worktree.lock")),
                false,
                deadline,
            )
        }
        .err()
        .unwrap();
        if mode == "expired" {
            assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        } else {
            assert!(
                error.to_string().contains(if mode == "loader" {
                    "loader overrides"
                } else {
                    "overrides its original fixed handoff"
                }),
                "{mode}: {error}"
            );
        }
        prepared.claim.check_current().unwrap();
    }
}
