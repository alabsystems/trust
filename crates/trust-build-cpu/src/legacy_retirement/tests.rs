use super::*;

struct Fixture {
    _root: tempfile::TempDir,
    old: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let root = crate::tests::private_tempdir();
        let old = root.path().join("old");
        fs::create_dir(&old).unwrap();
        fs::set_permissions(&old, Permissions::from_mode(0o700)).unwrap();
        for name in ["admission.lock", "slot-0", "slot-1", "slot-9"] {
            drop(open_file(&old.join(name), true).unwrap());
        }
        Self { _root: root, old }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        // Restore only this test's private fixtures after all users exited.
        let _ = fs::set_permissions(&self.old, Permissions::from_mode(0o700));
        if let Ok(entries) = fs::read_dir(&self.old) {
            for entry in entries.flatten() {
                let _ = fs::set_permissions(entry.path(), Permissions::from_mode(0o600));
            }
        }
    }
}

fn root() -> bool {
    // SAFETY: geteuid only reads the current identity.
    unsafe { libc::geteuid() == 0 }
}

#[test]
fn busy_epoch_is_not_changed() {
    let fixture = Fixture::new();
    let lock = exclusive(open_file(&fixture.old.join("admission.lock"), false).unwrap()).unwrap();
    let error = LegacyRetirement::retire(&fixture.old, 2).unwrap_err();
    if root() {
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    } else {
        assert_eq!(error.kind(), io::ErrorKind::WouldBlock);
    }
    assert_eq!(fs::metadata(&fixture.old).unwrap().mode() & 0o777, 0o700);
    assert!(open_file(&fixture.old.join("slot-0"), false).is_ok());
    drop(lock);
}

#[test]
fn retirement_survives_every_owner_and_blocks_a_preopened_waiter() {
    let fixture = Fixture::new();
    if root() {
        assert!(LegacyRetirement::retire(&fixture.old, 2).is_err());
        return;
    }
    let waiting_admission = open_file(&fixture.old.join("admission.lock"), false).unwrap();
    let retired = LegacyRetirement::retire(&fixture.old, 2).unwrap();
    retired.validate().unwrap();
    assert_eq!(retired.ensure_prior_boot().unwrap_err().kind(), io::ErrorKind::WouldBlock);
    assert_eq!(retired.retired_boot_id(), boot::current().unwrap());
    drop(retired);
    // A legacy launcher may have opened its admission description before the
    // migration. It still cannot open an existing slot or create a larger one.
    let waiter = exclusive(waiting_admission).unwrap();
    assert_eq!(
        open_file(&fixture.old.join("slot-0"), false).unwrap_err().kind(),
        io::ErrorKind::PermissionDenied
    );
    assert_eq!(
        open_file(&fixture.old.join("slot-42"), true).unwrap_err().kind(),
        io::ErrorKind::PermissionDenied
    );
    drop(waiter);
    LegacyRetirement::open(&fixture.old).unwrap().validate().unwrap();
}

#[test]
fn a_prepared_crash_can_resume_but_cannot_authorize_work() {
    let fixture = Fixture::new();
    if root() {
        return;
    }
    let retired = LegacyRetirement::retire(&fixture.old, 2).unwrap();
    let mut prepared = retired.record.clone();
    prepared.committed = false;
    let first = if prepared.retired_boot.starts_with('0') { "1" } else { "0" };
    prepared.retired_boot.replace_range(0..1, first);
    write_record(&retired.anchor, &open_parent(&retired.anchor).unwrap(), &prepared).unwrap();
    fs::set_permissions(fixture.old.join("slot-1"), Permissions::from_mode(0o600)).unwrap();
    assert!(LegacyRetirement::open(&fixture.old).is_err());
    assert!(retired.validate().is_err());
    let resumed = LegacyRetirement::retire(&fixture.old, 2).unwrap();
    resumed.validate().unwrap();
    assert_eq!(resumed.retired_boot_id(), boot::current().unwrap());
    assert_eq!(resumed.ensure_prior_boot().unwrap_err().kind(), io::ErrorKind::WouldBlock);
}

#[test]
fn changed_permissions_and_inode_revoke_readiness() {
    let fixture = Fixture::new();
    if root() {
        return;
    }
    let retired = LegacyRetirement::retire(&fixture.old, 2).unwrap();
    fs::set_permissions(fixture.old.join("slot-0"), Permissions::from_mode(0o600)).unwrap();
    assert!(retired.validate().is_err());
    fs::set_permissions(fixture.old.join("slot-0"), Permissions::from_mode(0o000)).unwrap();
    retired.validate().unwrap();
    fs::set_permissions(&fixture.old, Permissions::from_mode(0o700)).unwrap();
    fs::remove_file(fixture.old.join("slot-9")).unwrap();
    drop(open_file(&fixture.old.join("slot-9"), true).unwrap());
    fs::set_permissions(&fixture.old, Permissions::from_mode(0o500)).unwrap();
    assert!(retired.validate().is_err());
}

#[test]
fn malformed_or_incomplete_record_never_means_ready() {
    for value in [
        String::new(),
        format!("{VERSION} committed 2 1 2 abcdef01-2345-6789-abcd-0123456789ab\n"),
        format!(
            "{VERSION} nope 1 1 2 abcdef01-2345-6789-abcd-0123456789ab\nadmission.lock 3 4\nslot-0 5 6\n"
        ),
        "trust-legacy-retirement-v1 committed 1 1 2\n".to_owned(),
    ] {
        assert!(Record::parse(&value).is_err());
    }
}

#[cfg(target_os = "macos")]
#[test]
fn acl_grants_cannot_hide_behind_retired_mode_bits() {
    if root() {
        return;
    }
    // Each id and chmod child holds a copy of every descriptor of this
    // process, other tests' leases included, until its exec.
    let _fixture = crate::tests::kernel_fixture();
    let fixture = Fixture::new();
    let retired = LegacyRetirement::retire(&fixture.old, 2).unwrap();
    let user = std::process::Command::new("/usr/bin/id").arg("-un").output().unwrap();
    assert!(user.status.success());
    let user = String::from_utf8(user.stdout).unwrap();
    let user = user.trim();
    let file = fixture.old.join("slot-0");
    let grant = format!("user:{user} allow read,write");
    assert!(
        std::process::Command::new("/bin/chmod")
            .args(["+a", &grant])
            .arg(&file)
            .status()
            .unwrap()
            .success()
    );
    assert_eq!(fs::metadata(&file).unwrap().mode() & 0o777, 0);
    assert!(open_file(&file, false).is_ok());
    assert!(retired.validate().is_err());
    assert!(
        std::process::Command::new("/bin/chmod").arg("-N").arg(&file).status().unwrap().success()
    );
    retired.validate().unwrap();
    let grant = format!("user:{user} allow add_file,delete_child");
    assert!(
        std::process::Command::new("/bin/chmod")
            .args(["+a", &grant])
            .arg(&fixture.old)
            .status()
            .unwrap()
            .success()
    );
    assert_eq!(fs::metadata(&fixture.old).unwrap().mode() & 0o777, 0o500);
    assert!(retired.validate().is_err());
    assert!(!fixture.old.join("slot-4294967295").exists());
}

#[test]
fn canonical_authority_rejects_a_callers_isolated_namespace() {
    let path = crate::unix::account_home().unwrap().join(".cache/build-slot");
    assert!(require_default_namespace(&path, None).is_ok());
    assert!(require_default_namespace(&path, Some(path.as_os_str())).is_ok());
    assert!(
        require_default_namespace(&path, Some(std::ffi::OsStr::new("/tmp/isolated-capacity")))
            .is_err()
    );
}

#[test]
fn canonical_width_comes_from_the_existing_host_pool_not_a_callers_quota() {
    assert!(nominal_width(None).is_err());
    for (physical, expected) in [(1, 1), (18, 3)] {
        let root = crate::tests::private_tempdir();
        let pool = crate::Pool::open_in(root.path(), std::num::NonZeroU32::new(physical).unwrap())
            .unwrap();
        assert_eq!(nominal_width(Some(&pool)).unwrap(), expected);
    }
}

#[test]
fn created_capacity_parent_is_owner_only_under_a_group_writable_umask() {
    const TEST: &str = "legacy_retirement::tests::created_capacity_parent_is_owner_only_under_a_group_writable_umask";
    const ACTOR: &str = "TRUST_LEGACY_RETIREMENT_UMASK_ACTOR";
    if std::env::var_os(ACTOR).is_none() {
        // The umask is process-wide, so the check runs alone in a fresh process.
        // The child holds a copy of every descriptor of this process, other
        // tests' leases included, until its exec.
        let _fixture = crate::tests::kernel_fixture();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", TEST, "--test-threads=1"])
            .env(ACTOR, "1")
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let report = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
        assert!(output.status.success(), "{TEST}, run alone, failed:\n{report}");
        assert!(
            stdout.contains("test result: ok. 1 passed;"),
            "{TEST} did not run alone:\n{report}"
        );
        return;
    }
    // SAFETY: umask(2) only replaces this process's file creation mask, and this
    // process runs this one test and nothing else.
    unsafe { libc::umask(0o002) };
    let root = tempfile::tempdir().unwrap();
    let probe = root.path().join("std-create-dir");
    fs::create_dir(&probe).unwrap();
    assert_eq!(
        fs::metadata(&probe).unwrap().mode() & 0o777,
        0o775,
        "a std-created directory is group writable under this umask"
    );
    // A missing home and its .cache, as retire_canonical can find them.
    let home = root.path().join("home");
    let parent = home.join(".cache");
    let opened = open_created_parent(&parent).unwrap();
    assert!(opened.metadata().unwrap().is_dir());
    for directory in [&home, &parent] {
        assert_eq!(fs::metadata(directory).unwrap().mode() & 0o777, 0o700);
    }
    // An existing parent is opened as it is.
    drop(open_created_parent(&parent).unwrap());
}
