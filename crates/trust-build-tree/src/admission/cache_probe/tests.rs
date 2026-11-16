//! Native confinement/death and actual no-launch custody controls. These are
//! component fixtures, not SDK/compiler-health or canonical CPU-budget grants.

use std::fs;
use std::os::fd::FromRawFd as _;
use std::os::unix::fs::PermissionsExt as _;
use std::process::{Command, Stdio};

use super::*;
use crate::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager, Release};

const ACTOR: &str = "admission::cache_probe::tests::native_actor";
const MODE: &str = "TRUST_CACHE_NATIVE_ACTOR";
const ROOT: &str = "TRUST_CACHE_NATIVE_ROOT";
const CONTROL: &str = "TRUST_CACHE_NATIVE_CONTROL";
const EXCLUSION: &str = "TRUST_CACHE_NATIVE_EXCLUSION";

fn original(root: &Path) -> Lease {
    let LeaseAcquisition::Granted(lease) = Manager::open(root)
        .unwrap()
        .acquire_lease(&Acquire {
            kind: Kind::Build,
            owner_pid: std::process::id(),
            purpose: "native cache maintenance control".into(),
            contract: "actual independent source guard; no SDK or CPU result".into(),
            wait: Duration::ZERO,
            inherited_token: None,
            break_reason: None,
        })
        .unwrap()
    else {
        panic!("private source root unexpectedly held")
    };
    lease
}
fn args(command: &mut Command, mode: &str) {
    command
        .args(["--exact", ACTOR, "--ignored", "--test-threads=1", "--nocapture"])
        .env(MODE, mode);
}
fn bounded(child: &mut std::process::Child) {
    let until = Instant::now() + Duration::from_secs(60);
    loop {
        if child.try_wait().unwrap().is_some() {
            return;
        }
        if Instant::now() >= until {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("native cache actor timed out");
        }
        std::thread::sleep(POLL);
    }
}
fn isolated(body: impl FnOnce()) {
    const KEY: &str = "TRUST_CACHE_NATIVE_CASE";
    let name = std::thread::current().name().unwrap().to_owned();
    if std::env::var_os(KEY).as_deref() == Some(OsStr::new(&name)) {
        body();
        eprintln!("CACHE-NATIVE-ASSERTIONS-COMPLETE:{name}");
        return;
    }
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", &name, "--test-threads=1", "--nocapture"])
        .env(KEY, &name)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    bounded(&mut child);
    let output = child.wait_with_output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}{stderr}");
    assert!(stdout.contains("test result: ok. 1 passed;"), "{stdout}{stderr}");
    assert!(
        stderr.contains(&format!("CACHE-NATIVE-ASSERTIONS-COMPLETE:{name}")),
        "{stdout}{stderr}"
    );
}
fn read(channel: &mut UnixStream, bytes: &mut [u8]) {
    channel.set_read_timeout(Some(Duration::from_secs(60))).unwrap();
    channel.read_exact(bytes).unwrap();
}

#[test]
#[ignore = "private native actor; selected explicitly by bounded parent controls"]
fn native_actor() {
    let mode = std::env::var(MODE).expect("actual actor role");
    let fd: i32 = std::env::var(CONTROL).unwrap().parse().unwrap();
    let mut channel = unsafe { UnixStream::from_raw_fd(fd) };
    if mode == "kernel" || mode == "hold" {
        prelude::install().unwrap();
        let identity = process::read_identity(std::process::id()).unwrap();
        prelude::no_escape(identity).unwrap();
        assert_eq!(unsafe { libc::setsid() }, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        assert_eq!(unsafe { libc::setpgid(0, libc::getpgid(libc::getppid())) }, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        let fork = unsafe { libc::fork() };
        if fork == 0 {
            unsafe { libc::_exit(101) };
        }
        if fork > 0 {
            unsafe {
                libc::kill(fork, libc::SIGKILL);
                libc::waitpid(fork, std::ptr::null_mut(), 0);
            }
            panic!("actual fork escaped no-fork policy");
        }
        assert_eq!(fork, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        prelude::no_escape(process::read_identity(std::process::id()).unwrap()).unwrap();
        if mode == "hold" {
            // The actual originals were inherited via addinherit_np, not a
            // pathname reopen. Observe each target before any fixture opens.
            let originals: Vec<i32> =
                std::env::var(EXCLUSION).unwrap().split(',').map(|s| s.parse().unwrap()).collect();
            for original in originals {
                let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
                assert_eq!(unsafe { libc::fstat(original, metadata.as_mut_ptr()) }, 0);
            }
        }
        channel.write_all(b"k").unwrap();
        let mut bytes = [0];
        assert_eq!(channel.read(&mut bytes).unwrap(), 0, "parent closes actual retained control");
        return;
    }
    assert_eq!(mode, "owner");
    let root = PathBuf::from(std::env::var_os(ROOT).unwrap());
    let output = OutputLock::try_acquire(&root.join("build")).unwrap().unwrap();
    let lease = MaintenanceLease::begin(original(&root)).unwrap();
    let exclusion = File::open(root.join("actual-exclusion")).unwrap();
    exclusion.try_lock().unwrap();
    let originals = unsafe { output.original_descriptions() }.unwrap();
    let mut command = Command::new(std::env::current_exe().unwrap());
    args(&mut command, "hold");
    command.env(CONTROL, fd.to_string());
    command.env(
        EXCLUSION,
        format!(
            "{},{},{}",
            originals.directory().as_raw_fd(),
            originals.lock().as_raw_fd(),
            exclusion.as_raw_fd()
        ),
    );
    let scheduler = Jobserver::new(1).unwrap(); // component transport, never a CPU grant
    let mut child = match native::Child::spawn_version_prelude(
        &command,
        &scheduler,
        channel.as_fd(),
        &[originals.directory(), originals.lock(), exclusion.as_fd()],
        deadline().unwrap(),
    ) {
        Ok(child) => child,
        Err(_) => panic!("native actor creation failed"),
    };
    let identity = child.stopped_identity(deadline().unwrap()).unwrap();
    // PID framing precedes target GO, so its later marker cannot interleave.
    channel.write_all(&child.id().to_be_bytes()).unwrap();
    child.resume(identity, deadline().unwrap()).unwrap();
    // Both the actor and its parent own this endpoint until actual parent death.
    // Keep the sole original native Child and durable lease on the owner's
    // stack: killing this process must not run their ordinary destructors.
    lease.check_current().unwrap();
    loop {
        std::thread::sleep(Duration::from_secs(1));
    }
}

#[test]
fn actual_failed_native_creation_restores_only_its_same_local_idle_lease() {
    isolated(|| {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().canonicalize().unwrap();
        let held = MaintenanceLease::begin(original(&root)).unwrap();
        let (parent, child) = UnixStream::pair().unwrap();
        let scheduler = Jobserver::new(1).unwrap(); // no child/CPU work is launched
        let command = Command::new(root.join("genuinely-missing-image"));
        match native::Child::spawn_version_prelude(
            &command,
            &scheduler,
            child.as_fd(),
            &[],
            deadline().unwrap(),
        ) {
            Err(native::VersionSpawnError::NotSpawned(_)) => {}
            _ => panic!("expected the actual native no-launch result"),
        }
        drop(parent);
        let proof = NativeClosed { binding: held.binding(), _status: None };
        let lease = held.restore(proof).unwrap();
        lease.check_root(&root).unwrap();
        let text = fs::read_to_string(root.join(".trust-build-lock/info")).unwrap();
        assert!(text.contains("state=WITHHELD"));
        assert_eq!(
            Manager::open(&root).unwrap().release("not-a-token").unwrap(),
            Release::ParentManaged
        );
        drop(lease);
        assert!(
            !root.join(".trust-build-lock").exists(),
            "actual same-process idle original retires on Drop"
        );
    });
}

#[test]
fn private_closure_from_another_actual_maintenance_owner_is_refused() {
    isolated(|| {
        let a = tempfile::tempdir().unwrap();
        let b = tempfile::tempdir().unwrap();
        let a = a.path().canonicalize().unwrap();
        let b = b.path().canonicalize().unwrap();
        let owner_a = MaintenanceLease::begin(original(&a)).unwrap();
        let owner_b = MaintenanceLease::begin(original(&b)).unwrap();
        let proof = NativeClosed { binding: owner_a.binding(), _status: None };
        assert!(owner_b.restore(proof).is_err());
        assert!(
            fs::read_to_string(b.join(".trust-build-lock/info"))
                .unwrap()
                .contains("state=WITHHELD")
        );
        drop(owner_a);
        assert!(a.join(".trust-build-lock").exists());
    });
}

#[test]
fn actual_session_leader_no_fork_actor_cannot_escape_or_create_a_descendant() {
    isolated(|| {
        let (mut parent, child) = UnixStream::pair().unwrap();
        let mut command = Command::new(std::env::current_exe().unwrap());
        args(&mut command, "kernel");
        command.env(CONTROL, child.as_raw_fd().to_string());
        let scheduler = Jobserver::new(1).unwrap();
        let mut child = match native::Child::spawn_version_prelude(
            &command,
            &scheduler,
            child.as_fd(),
            &[],
            deadline().unwrap(),
        ) {
            Ok(child) => child,
            Err(_) => panic!("native actor creation failed"),
        };
        let initial = child.stopped_identity(deadline().unwrap()).unwrap();
        child.resume(initial, deadline().unwrap()).unwrap();
        let mut marker = [0];
        read(&mut parent, &mut marker);
        assert_eq!(marker, [b'k']);
        prelude::no_escape(process::read_identity(child.id()).unwrap()).unwrap();
        drop(parent);
        let until = deadline().unwrap();
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            assert!(Instant::now() < until);
            std::thread::sleep(POLL);
        };
        assert!(status.success());
        assert!(child.version_group_gone().unwrap());
    });
}

#[test]
fn actual_parent_death_keeps_original_ofd_exclusions_and_durable_manager_debt() {
    isolated(|| {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().canonicalize().unwrap();
        fs::create_dir(root.join("build")).unwrap();
        fs::write(root.join("actual-exclusion"), b"same original exclusion").unwrap();
        fs::set_permissions(root.join("actual-exclusion"), fs::Permissions::from_mode(0o600))
            .unwrap();
        let (mut parent, child) = UnixStream::pair().unwrap();
        let mut command = Command::new(std::env::current_exe().unwrap());
        args(&mut command, "owner");
        command.env(ROOT, &root).env(CONTROL, child.as_raw_fd().to_string());
        let scheduler = Jobserver::new(1).unwrap();
        let mut owner = match native::Child::spawn_version_prelude(
            &command,
            &scheduler,
            child.as_fd(),
            &[],
            deadline().unwrap(),
        ) {
            Ok(child) => child,
            Err(_) => panic!("native owner creation failed"),
        };
        let identity = owner.stopped_identity(deadline().unwrap()).unwrap();
        owner.resume(identity, deadline().unwrap()).unwrap();
        // Drop our copy of the transferred endpoint before testing actual EOF.
        drop(child);
        let mut pid = [0; 4];
        read(&mut parent, &mut pid);
        let target = u32::from_be_bytes(pid);
        let mut marker = [0];
        read(&mut parent, &mut marker);
        assert_eq!(marker, [b'k']);
        prelude::no_escape(process::read_identity(target).unwrap()).unwrap();
        owner.kill().unwrap();
        let until = deadline().unwrap();
        loop {
            if owner.try_wait().unwrap().is_some() {
                break;
            }
            assert!(Instant::now() < until);
            std::thread::sleep(POLL);
        }
        let output = File::open(root.join("build/lock")).unwrap();
        let exclusion = File::open(root.join("actual-exclusion")).unwrap();
        assert!(matches!(output.try_lock(), Err(fs::TryLockError::WouldBlock)));
        assert!(matches!(exclusion.try_lock(), Err(fs::TryLockError::WouldBlock)));
        assert!(
            fs::read_to_string(root.join(".trust-build-lock/info"))
                .unwrap()
                .contains("state=WITHHELD")
        );
        // Close the real original stream. No PID/data-derived signal or reap
        // capability is constructed for the now-reparented target.
        drop(parent);
        let until = deadline().unwrap();
        loop {
            match (output.try_lock(), exclusion.try_lock()) {
                (Ok(()), Ok(())) => break,
                _ => {
                    assert!(Instant::now() < until, "actual inherited OFDs did not close");
                    std::thread::sleep(POLL);
                }
            }
        }
        assert!(
            root.join(".trust-build-lock/info").is_file(),
            "no surviving original wait owner can mint closure or retire durable debt"
        );
    });
}

#[test]
fn seed_tools_absence_is_positive_and_bound_to_the_actual_host() {
    isolated(|| {
        let temp = tempfile::tempdir().unwrap();
        let output_path = temp.path().join("build");
        let host = output_path.join("host");
        fs::create_dir_all(&host).unwrap();
        let output = OutputLock::try_acquire(&output_path).unwrap().unwrap();
        let absent = inputs::AbsentCompilers::capture(&output, OsStr::new("host")).unwrap();
        absent.check(&output).unwrap();
        for stage in ["stage1", "stage2"] {
            fs::write(host.join(stage), b"present but broken").unwrap();
            assert!(absent.check(&output).is_err());
            assert!(inputs::AbsentCompilers::capture(&output, OsStr::new("host")).is_err());
            fs::remove_file(host.join(stage)).unwrap();
            std::os::unix::fs::symlink("missing", host.join(stage)).unwrap();
            assert!(inputs::AbsentCompilers::capture(&output, OsStr::new("host")).is_err());
            fs::remove_file(host.join(stage)).unwrap();
            fs::create_dir(host.join(stage)).unwrap();
            assert!(inputs::AbsentCompilers::capture(&output, OsStr::new("host")).is_err());
            fs::remove_dir(host.join(stage)).unwrap();
        }
        fs::rename(&host, output_path.join("old-host")).unwrap();
        fs::create_dir(&host).unwrap();
        assert!(absent.check(&output).is_err());
    });
}
