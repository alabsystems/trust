// Native policy regression bodies shared by the leaf and Bootstrap harnesses.
#[test]
fn native_policy_and_guard_contend_and_repeat_on_one_persistent_inode() {
    let fixture = Fixture::new();
    {
        let namespace = NamespaceGuard::acquire(&fixture.root).unwrap();
        let inode = fs::metadata(fixture.root.join(GUARD_NAME)).unwrap().ino();
        let mut administrative = OwnedChild::spawn(&mut fixture.acquire());
        std::thread::sleep(Duration::from_millis(150));
        administrative.pending();
        assert!(!fixture.root.join(".trust-build-lock").exists());
        drop(namespace);
        let output = administrative.finish();
        assert!(output.status.success(), "{output:?}");
        let token = String::from_utf8(output.stdout).unwrap();
        assert!(BuildLease::acquire(&fixture.root).is_err());
        let release = OwnedChild::spawn(&mut fixture.command(&["release", token.trim()])).finish();
        assert!(release.status.success(), "{release:?}");
        for _ in 0..3 {
            let native = BuildLease::acquire(&fixture.root).unwrap();
            let refusal = OwnedChild::spawn(&mut fixture.acquire()).finish();
            assert_eq!(refusal.status.code(), Some(3), "{refusal:?}");
            drop(native);
            assert!(!fixture.root.join(".trust-build-lock").exists());
            assert_eq!(fs::metadata(fixture.root.join(GUARD_NAME)).unwrap().ino(), inode);
        }
    }
}

#[test]
fn release_empty_directory_window_excludes_two_new_acquirers() {
    let fixture = Fixture::new();
    {
        let native = BuildLease::acquire(&fixture.root).unwrap();
        let namespace = NamespaceGuard::acquire(&fixture.root).unwrap();
        // This is the formerly unsafe final unlink -> rmdir window.
        fs::remove_file(fixture.root.join(".trust-build-lock/info")).unwrap();
        let mut first = OwnedChild::spawn(&mut fixture.acquire());
        let mut second = OwnedChild::spawn(&mut fixture.acquire());
        std::thread::sleep(Duration::from_millis(150));
        first.pending();
        second.pending();
        assert!(fixture.root.join(".trust-build-lock").is_dir());
        fs::remove_dir(fixture.root.join(".trust-build-lock")).unwrap();
        drop(namespace);
        let outputs = [first.finish(), second.finish()];
        assert_eq!(outputs.iter().filter(|o| o.status.success()).count(), 1, "{outputs:?}");
        assert_eq!(outputs.iter().filter(|o| o.status.code() == Some(3)).count(), 1, "{outputs:?}");
        let token =
            String::from_utf8_lossy(&outputs.iter().find(|o| o.status.success()).unwrap().stdout)
                .trim()
                .to_owned();
        let bytes = fs::read(fixture.root.join(".trust-build-lock/info")).unwrap();
        drop(native); // The old exact holder must preserve the new winner.
        assert_eq!(fs::read(fixture.root.join(".trust-build-lock/info")).unwrap(), bytes);
        assert!(
            OwnedChild::spawn(&mut fixture.command(&["release", &token])).finish().status.success()
        );
    }
}

#[test]
fn stale_recovery_is_serialized_and_exact_token_still_required() {
    let fixture = Fixture::new();
    {
        let namespace = NamespaceGuard::acquire(&fixture.root).unwrap();
        // A holder as `create_holder_directory` makes one and its info 0600, as a
        // persisted temporary file, whatever the umask: management refuses a
        // group-writable holder. Std calls with explicit modes, because
        // Bootstrap's harness includes these cases and has no `owner_only`.
        {
            use std::os::unix::fs::{DirBuilderExt as _, OpenOptionsExt as _};
            fs::DirBuilder::new()
                .mode(0o755)
                .create(fixture.root.join(".trust-build-lock"))
                .unwrap();
            fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(fixture.root.join(".trust-build-lock/info"))
                .unwrap()
                .write_all(b"token=stale\nkind=build\npid=2147483647\npstart=gone\n")
                .unwrap();
        }
        drop(namespace);
        let first = OwnedChild::spawn(&mut fixture.acquire());
        let second = OwnedChild::spawn(&mut fixture.acquire());
        let outputs = [first.finish(), second.finish()];
        assert_eq!(outputs.iter().filter(|o| o.status.success()).count(), 1, "{outputs:?}");
        assert_eq!(outputs.iter().filter(|o| o.status.code() == Some(3)).count(), 1, "{outputs:?}");
        let info = fixture.root.join(".trust-build-lock/info");
        let before = fs::read(&info).unwrap();
        assert_eq!(
            OwnedChild::spawn(&mut fixture.command(&["release", "stale"])).finish().status.code(),
            Some(4)
        );
        assert_eq!(fs::read(&info).unwrap(), before);
        let audit = fs::read_to_string(fixture.root.join(".trust-build-lock.breaks")).unwrap();
        assert!(audit.contains("STALE-TAKEOVER") && audit.contains("stale"), "{audit}");
    }
}

#[test]
fn inherited_flock_survives_helper_exit_until_last_description_closes() {
    let fixture = Fixture::new();
    {
        drop(NamespaceGuard::acquire(&fixture.root).unwrap());
        let ready = fixture.root.join("helper-exited");
        let mut controller = native_actor::actor(&fixture.root, "guard-controller");
        controller.stdin(Stdio::piped());
        let mut child = OwnedChild::spawn(&mut controller);
        let deadline = Instant::now() + Duration::from_secs(5);
        while !ready.exists() {
            child.pending();
            assert!(Instant::now() < deadline, "helper did not execute");
            std::thread::sleep(Duration::from_millis(10));
        }
        let challenger = File::open(fixture.root.join(GUARD_NAME)).unwrap();
        assert!(matches!(challenger.try_lock(), Err(fs::TryLockError::WouldBlock)));
        child.0.as_mut().unwrap().stdin.take().unwrap().write_all(b"done\n").unwrap();
        assert!(child.finish().status.success());
        assert!(challenger.try_lock().is_ok());
    }
}

#[test]
fn native_policy_preserves_original_descriptors_including_nine() {
    descriptor_case(false);
}

#[test]
fn native_policy_preserves_occupied_descriptor_range_without_legacy_slot_limit() {
    descriptor_case(true);
}

fn descriptor_case(all: bool) {
    let fixture = Fixture::new();
    let mut command = native_actor::actor(&fixture.root, "descriptors");
    command
        .arg(if all { "all" } else { "jobserver" })
        .env("TRUST_REPO", &fixture.root)
        .env_remove("TRUST_BUILD_LOCK_TOKEN")
        .env_remove("TRUST_BUILD_LOCK_WAIT");
    let output = OwnedChild::spawn(&mut command).finish();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        fs::read(fixture.root.join("resources")).unwrap(),
        vec![b'x'; if all { 7 } else { 2 }]
    );
    // The native policy has no shell's 3..9 allocator. Its real token is still
    // delivered exactly once, and an independent native release consumes it.
    let token = String::from_utf8(output.stdout).unwrap();
    assert_eq!(token.lines().count(), 1);
    assert!(
        OwnedChild::spawn(&mut fixture.command(&["release", token.trim()]))
            .finish()
            .status
            .success()
    );
}

#[test]
fn exited_actual_native_handoff_holder_requires_outer_cleanup_or_explicit_break() {
    const ROOT: &str = "TRUST_NATIVE_REPO_RETAINED_CONTROL_ROOT";
    const NAME: &str = concat!(
        module_path!(),
        "::exited_actual_native_handoff_holder_requires_outer_cleanup_or_explicit_break"
    );
    if let Some(root) = std::env::var_os(ROOT) {
        let root = Path::new(&root);
        let _held = BuildLease::acquire(root).unwrap();
        fs::write(root.join("executed-retained-control"), b"executed").unwrap();
        // The real producer exits without Rust Drop, exactly as production
        // bootstrap failure does. Its record was acknowledged to this
        // actual direct parent, not hand-authored by the test controller.
        std::process::exit(7);
    }
    let fixture = Fixture::new();
    {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", NAME.split_once("::").unwrap().1, "--nocapture", "--test-threads=1"])
            .env(ROOT, &fixture.root)
            .env("TRUST_NATIVE_REPO_PARENT_PID", std::process::id().to_string())
            .env("TRUST_NATIVE_REPO_PARENT_START", process_start(&std::process::id().to_string()))
            .env("TRUST_NATIVE_REPO_PARENT_TOKEN", "trust-native-repo-owner-retained-control");
        let output = OwnedChild::spawn(&mut command).finish();
        assert_eq!(output.status.code(), Some(7), "{output:?}");
        assert_eq!(fs::read(fixture.root.join("executed-retained-control")).unwrap(), b"executed");
        let info = fixture.root.join(".trust-build-lock/info");
        let original = fs::read(&info).unwrap();
        let text = std::str::from_utf8(&original).unwrap();
        let token = text.lines().find_map(|line| line.strip_prefix("token=")).unwrap();
        assert!(text.contains("release_token=trust-native-repo-owner-retained-control\n"));
        assert!(BuildLease::acquire(&fixture.root).is_err());
        assert_eq!(OwnedChild::spawn(&mut fixture.acquire()).finish().status.code(), Some(3));
        assert_eq!(
            OwnedChild::spawn(&mut fixture.command(&["release", token])).finish().status.code(),
            Some(4)
        );
        let mut borrowed = fixture.acquire();
        borrowed.env("TRUST_BUILD_LOCK_TOKEN", token);
        assert_eq!(OwnedChild::spawn(&mut borrowed).finish().status.code(), Some(3));
        assert_eq!(fs::read(&info).unwrap(), original);
        let broken = OwnedChild::spawn(&mut fixture.command(&[
            "break",
            "--reason",
            "bounded own exited control recovery",
        ]))
        .finish();
        assert!(broken.status.success(), "{broken:?}");
        assert!(!fixture.root.join(".trust-build-lock").exists());
        assert!(
            fs::read_to_string(fixture.root.join(".trust-build-lock.breaks"))
                .unwrap()
                .contains("bounded own exited control recovery")
        );
        drop(BuildLease::acquire(&fixture.root).unwrap());
    }
}

// Trust: this test observation is not a public process or lease-adoption API.
fn process_start(pid: &str) -> String {
    let output = Command::new("ps").args(["-o", "lstart=", "-p", pid]).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

#[test]
fn native_acquisition_waits_for_actual_seed_lease_without_explicit_wait() {
    let fixture = Fixture::new();
    assert_seed_wait(&fixture.root);
}

pub(crate) fn assert_seed_wait(root: &Path) {
    let lease = BuildLease::acquire_independent(
        root,
        "stage-1 seed source (another worktree clones this build tree)",
        "bootstrap stage-1 seed",
    )
    .unwrap();
    let pid = std::process::id().to_string();
    let mut acquisition =
        command(root, &["acquire", "--kind", "build", "--purpose", "donor x.py", "--pid", &pid]);
    let mut waiting = OwnedChild::spawn(&mut acquisition);
    std::thread::sleep(Duration::from_millis(150));
    waiting.pending();
    drop(lease);
    let output = waiting.finish();
    assert!(output.status.success(), "{output:?}");
    let token = String::from_utf8(output.stdout).unwrap();
    assert_eq!(token.lines().count(), 1);
    assert!(!token.trim().is_empty());
    let released = OwnedChild::spawn(&mut command(root, &["release", token.trim()])).finish();
    assert!(released.status.success(), "{released:?}");
    assert!(!root.join(".trust-build-lock").exists());
}

#[test]
fn native_frontdoor_excludes_both_build_and_measurement_with_exact_token() {
    for (held_kind, blocked_kind) in [("build", "measurement"), ("measurement", "build")] {
        let fixture = Fixture::new();
        let pid = std::process::id().to_string();
        let held = OwnedChild::spawn(&mut fixture.command(&[
            "acquire",
            "--kind",
            held_kind,
            "--purpose",
            "symmetric native exclusion",
            "--pid",
            &pid,
        ]))
        .finish();
        assert!(held.status.success(), "{held:?}");
        let token = String::from_utf8(held.stdout).unwrap();
        assert_eq!(token.lines().count(), 1);
        let info = fixture.root.join(".trust-build-lock/info");
        let before = fs::read(&info).unwrap();
        let blocked = OwnedChild::spawn(&mut fixture.command(&[
            "acquire",
            "--kind",
            blocked_kind,
            "--pid",
            &pid,
        ]))
        .finish();
        assert_eq!(blocked.status.code(), Some(3), "{blocked:?}");
        assert!(blocked.stdout.is_empty());
        let diagnostic = String::from_utf8_lossy(&blocked.stderr);
        assert!(
            diagnostic.contains(held_kind)
                && diagnostic.contains(&pid)
                && diagnostic.contains("symmetric native exclusion"),
            "{blocked:?}"
        );
        let wrong = OwnedChild::spawn(&mut fixture.command(&["release", "foreign-token"])).finish();
        assert_eq!(wrong.status.code(), Some(4), "{wrong:?}");
        assert_eq!(fs::read(&info).unwrap(), before);
        let released = OwnedChild::spawn(&mut fixture.command(&["release", token.trim()])).finish();
        assert!(released.status.success(), "{released:?}");
        assert!(!fixture.root.join(".trust-build-lock").exists());
    }
}
