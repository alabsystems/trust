use std::path::{Path, PathBuf};

use trust_resource_provenance::program::HeldSystemCommand;

use super::*;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

/// The child's exit status. A child that has not exited within 60 s is killed
/// and the test fails. One the kill has not let this test reap 10 s later aborts
/// the binary, since a panic would drop the child, and its drop waits without
/// bound. So a stalled launch cannot hang the test binary at these waits
/// (TBT-NATIVE-EXEC-LAUNCH-STALL-1).
fn exited(child: &mut Child) -> std::process::ExitStatus {
    if let Some(status) = reaped_within(child, Duration::from_secs(60)) {
        return status;
    }
    let killed = child.kill();
    if let Some(status) = reaped_within(child, Duration::from_secs(10)) {
        panic!("the child had not exited after 60 s; killed ({killed:?}): {status:?}");
    }
    // Past libtest's capture, which an abort would discard.
    use std::io::Write as _;
    let _ = writeln!(
        std::io::stderr().lock(),
        "the child had not exited after 60 s, nor been reaped 10 s after its kill ({killed:?})"
    );
    std::process::abort();
}

fn reaped_within(child: &mut Child, span: Duration) -> Option<std::process::ExitStatus> {
    let until = Instant::now() + span;
    while Instant::now() < until {
        if let Some(status) = child.try_wait().unwrap() {
            return Some(status);
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    None
}

fn image(directory: &Path, name: &str) -> PathBuf {
    let image = directory.join(name);
    std::fs::copy(std::env::current_exe().unwrap(), &image).unwrap();
    std::fs::canonicalize(image).unwrap()
}

fn action(image: &Path, canary: &Path) -> Command {
    let mut command = Command::new(image);
    command.args([
        "--exact",
        "trust_repo_lock::management::exec::native::tests::actual_entry_actor",
        "--nocapture",
    ]);
    command.env("TRUST_NATIVE_EXEC_ENTRY_CANARY", canary);
    command
}

#[test]
fn actual_entry_actor() {
    let Some(path) = std::env::var_os("TRUST_NATIVE_EXEC_ENTRY_CANARY") else { return };
    if let Ok(value) = std::env::var("TRUST_NATIVE_EXEC_EXPECT_PIPE") {
        let fds = value.split(',').map(|v| v.parse::<libc::c_int>().unwrap()).collect::<Vec<_>>();
        assert_eq!(fds.len(), 2);
        // This is a transport conservation probe, not a scheduling owner or
        // a late environment-to-Jobserver constructor. Return the exact byte
        // read from the original pipe; no new GNU credit is made.
        let mut byte = 0_u8;
        assert_eq!(
            unsafe { libc::read(fds[0], (&mut byte as *mut u8).cast(), 1) },
            1,
            "original GNU read: {}",
            io::Error::last_os_error()
        );
        assert_eq!(
            unsafe { libc::write(fds[1], (&byte as *const u8).cast(), 1) },
            1,
            "original GNU return: {}",
            io::Error::last_os_error()
        );
        let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
        assert_eq!(std::env::var("MAKEFLAGS").unwrap(), flags);
        assert_eq!(std::env::var("MFLAGS").unwrap(), flags);
    }
    let observed = format!(
        "pid={} pgid={} sid={}\n",
        std::process::id(),
        unsafe { libc::getpgrp() },
        unsafe { libc::getsid(0) },
    );
    std::fs::write(path, observed).unwrap();
}

#[test]
fn actual_loaded_child_stays_before_entry_until_the_original_image_check() {
    let images = tempfile::tempdir().unwrap();
    let output = tempfile::tempdir().unwrap();
    let program = image(images.path(), "native-original");
    let canary = output.path().join("entry");
    let held = HeldSystemCommand::open(&program, deadline()).unwrap();
    let scheduler = Jobserver::new(1).unwrap();
    let command = action(&program, &canary);
    let mut child = Child::spawn_suspended(&command, &scheduler, deadline()).unwrap();
    let identity = child.stopped_identity(deadline()).unwrap();
    assert!(!canary.exists(), "target user entry ran before image authentication");
    held.validate_loaded(identity, deadline()).unwrap();
    child.resume(identity, deadline()).unwrap();
    assert!(exited(&mut child).success());
    let observed = std::fs::read_to_string(canary).unwrap();
    assert!(observed.contains(&format!("pgid={}", unsafe { libc::getpgrp() })));
    assert!(observed.contains(&format!("sid={}", unsafe { libc::getsid(0) })));
    assert!(child.resume(identity, deadline()).is_err(), "GO is not replayable");
}

#[test]
fn a_different_loaded_inode_is_reaped_without_ever_entering_it() {
    let images = tempfile::tempdir().unwrap();
    let output = tempfile::tempdir().unwrap();
    let original = image(images.path(), "native-original");
    let replacement = image(images.path(), "native-replacement");
    let canary = output.path().join("entry");
    let held = HeldSystemCommand::open(&original, deadline()).unwrap();
    // Both genuine native images have identical bytes but different original
    // inodes. No pathname/content observation can substitute the loaded image.
    let scheduler = Jobserver::new(1).unwrap();
    let command = action(&replacement, &canary);
    let mut child = Child::spawn_suspended(&command, &scheduler, deadline()).unwrap();
    let identity = child.stopped_identity(deadline()).unwrap();
    assert!(held.validate_loaded(identity, deadline()).is_err());
    assert!(!canary.exists());
    child.kill().unwrap();
    assert_eq!(exited(&mut child).signal(), Some(libc::SIGKILL));
    assert!(!canary.exists(), "refused image reached its user entry");
}

#[test]
fn actual_path_replacement_after_the_final_pre_spawn_check_cannot_run() {
    let images = tempfile::tempdir().unwrap();
    let output = tempfile::tempdir().unwrap();
    let program = image(images.path(), "native-original");
    let replacement = image(images.path(), "native-replacement");
    let canary = output.path().join("entry");
    let held = HeldSystemCommand::open(&program, deadline()).unwrap();
    held.validate(deadline()).unwrap();
    std::fs::rename(&replacement, &program).unwrap();
    let scheduler = Jobserver::new(1).unwrap();
    let command = action(&program, &canary);
    let mut child = Child::spawn_suspended(&command, &scheduler, deadline()).unwrap();
    let identity = child.stopped_identity(deadline()).unwrap();
    assert!(held.validate_loaded(identity, deadline()).is_err());
    drop(child); // The sole original wait owner kills and reaps the stopped child.
    assert!(!canary.exists(), "post-validation replacement ran before refusal");
}

#[test]
fn an_expired_launch_never_creates_a_target_entry() {
    let output = tempfile::tempdir().unwrap();
    let canary = output.path().join("entry");
    let scheduler = Jobserver::new(1).unwrap();
    let command = action(Path::new("/not-opened/native-image"), &canary);
    assert!(matches!(
        Child::spawn_suspended(&command, &scheduler, Instant::now()),
        Err(error) if error.kind() == io::ErrorKind::TimedOut
    ));
    assert!(!canary.exists());
}

#[test]
fn native_file_actions_inherit_the_same_gnu_pipe_without_changing_parent_flags_or_credits() {
    let images = tempfile::tempdir().unwrap();
    let output = tempfile::tempdir().unwrap();
    let program = image(images.path(), "native-original");
    let canary = output.path().join("entry");
    let held = HeldSystemCommand::open(&program, deadline()).unwrap();
    let scheduler = Jobserver::new(3).unwrap();
    scheduler.client().acquire_raw().unwrap();
    let originals = scheduler.pipe_descriptors().unwrap();
    let fds = [originals[0].as_raw_fd(), originals[1].as_raw_fd()];
    let flags = fds.map(|fd| unsafe { libc::fcntl(fd, libc::F_GETFD) });
    assert!(flags.iter().all(|flags| *flags >= 0));
    let mut command = action(&program, &canary);
    scheduler.configure_make(&mut command);
    command.env("TRUST_NATIVE_EXEC_EXPECT_PIPE", format!("{},{}", fds[0], fds[1]));
    let mut child = Child::spawn_suspended(&command, &scheduler, deadline()).unwrap();
    let identity = child.stopped_identity(deadline()).unwrap();
    held.validate_loaded(identity, deadline()).unwrap();
    assert!(!canary.exists());
    assert_eq!(scheduler.client().available().unwrap(), 2);
    child.resume(identity, deadline()).unwrap();
    assert!(exited(&mut child).success());
    assert_eq!(scheduler.client().available().unwrap(), 2);
    assert_eq!(fds.map(|fd| unsafe { libc::fcntl(fd, libc::F_GETFD) }), flags);
}

#[test]
#[ignore = "private second-exec actor; selected explicitly by the bounded deadline control"]
fn actual_second_stop_actor() {
    let Some(control) = std::env::var_os("TRUST_NATIVE_EXEC_SECOND_STOP_CONTROL") else { return };
    let control: i32 = control.to_str().unwrap().parse().unwrap();
    // This same genuine native image is replaced in the SAME PID and stopped
    // before its canary entry. Test-only native SETEXEC creates no claim/grant.
    let path = cstring(std::env::current_exe().unwrap().as_os_str()).unwrap();
    let args = [
        path.clone(),
        CString::new("--exact").unwrap(),
        CString::new("trust_repo_lock::management::exec::native::tests::actual_entry_actor")
            .unwrap(),
        CString::new("--nocapture").unwrap(),
    ];
    let argv = args
        .iter()
        .map(|arg| arg.as_ptr().cast_mut())
        .chain(std::iter::once(std::ptr::null_mut()))
        .collect::<Vec<_>>();
    let environment = std::env::vars_os()
        .map(|(name, value)| {
            let mut bytes = std::os::unix::ffi::OsStrExt::as_bytes(name.as_os_str()).to_vec();
            bytes.push(b'=');
            bytes.extend_from_slice(std::os::unix::ffi::OsStrExt::as_bytes(value.as_os_str()));
            CString::new(bytes).unwrap()
        })
        .collect::<Vec<_>>();
    let envp = environment
        .iter()
        .map(|value| value.as_ptr().cast_mut())
        .chain(std::iter::once(std::ptr::null_mut()))
        .collect::<Vec<_>>();
    let mut attributes = std::mem::MaybeUninit::<libc::posix_spawnattr_t>::uninit();
    assert_eq!(unsafe { libc::posix_spawnattr_init(attributes.as_mut_ptr()) }, 0);
    let mut attributes = unsafe { attributes.assume_init() };
    assert_eq!(
        unsafe {
            libc::posix_spawnattr_setflags(
                &mut attributes,
                (libc::POSIX_SPAWN_SETEXEC | libc::POSIX_SPAWN_START_SUSPENDED) as libc::c_short,
            )
        },
        0
    );
    let marker = *b"s";
    assert_eq!(unsafe { libc::write(control, marker.as_ptr().cast(), marker.len()) }, 1);
    let mut pid = 0;
    let error = unsafe {
        libc::posix_spawn(
            &mut pid,
            path.as_ptr(),
            std::ptr::null(),
            &attributes,
            argv.as_ptr(),
            envp.as_ptr(),
        )
    };
    unsafe {
        libc::posix_spawnattr_destroy(&mut attributes);
    }
    panic!("same-PID suspended exec unexpectedly returned: {error}");
}

#[test]
fn actual_second_exec_observations_cannot_extend_original_go_deadline() {
    use std::io::Read as _;
    use std::os::fd::AsFd as _;
    use std::os::unix::net::UnixStream;
    for final_go in [false, true] {
        let images = tempfile::tempdir().unwrap();
        let output = tempfile::tempdir().unwrap();
        let program = image(images.path(), "native-second-stop");
        let canary = output.path().join("forbidden-late-entry");
        let held = HeldSystemCommand::open(&program, deadline()).unwrap();
        let (mut parent, control) = UnixStream::pair().unwrap();
        parent.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
        let mut command = Command::new(&program);
        command
            .args([
                "--exact",
                "trust_repo_lock::management::exec::native::tests::actual_second_stop_actor",
                "--ignored",
                "--test-threads=1",
                "--nocapture",
            ])
            .env("TRUST_NATIVE_EXEC_ENTRY_CANARY", &canary)
            .env("TRUST_NATIVE_EXEC_SECOND_STOP_CONTROL", control.as_raw_fd().to_string());
        let scheduler = Jobserver::new(1).unwrap();
        let mut child = match Child::spawn_version_prelude(
            &command,
            &scheduler,
            control.as_fd(),
            &[],
            deadline(),
        ) {
            Ok(child) => child,
            Err(_) => panic!("actual second-stop fixture creation failed"),
        };
        let initial = child.stopped_identity(deadline()).unwrap();
        held.validate_loaded(initial, deadline()).unwrap();
        child.resume(initial, deadline()).unwrap();
        drop(control);
        let mut marker = [0];
        parent.read_exact(&mut marker).unwrap();
        assert_eq!(marker, [b's']);
        let until = deadline();
        let target = loop {
            if let Some(target) = child.version_exec_stop(initial, until).unwrap() {
                break target;
            }
            assert!(Instant::now() < until, "actual second image never stopped");
            std::thread::sleep(Duration::from_millis(1));
        };
        held.validate_loaded(target, deadline()).unwrap();
        assert!(!canary.exists());
        VERSION_EXPIRY_REACHED.set(false);
        // Far enough ahead that the native bookends finish before it on a loaded
        // machine; the injected expiry then sleeps until it passes.
        let original_deadline = Instant::now() + Duration::from_secs(5);
        let result = if final_go {
            EXPIRE_VERSION_GO.set(true);
            let result = child.resume_version_target(initial, target, original_deadline);
            EXPIRE_VERSION_GO.set(false);
            result.map(|()| Some(target))
        } else {
            EXPIRE_VERSION_OBSERVATION.set(true);
            let result = child.version_exec_stop(initial, original_deadline);
            EXPIRE_VERSION_OBSERVATION.set(false);
            result
        };
        assert!(
            VERSION_EXPIRY_REACHED.get(),
            "expiry injection must follow ACTUAL completed native bookends"
        );
        assert!(matches!(result, Err(error) if error.kind() == io::ErrorKind::TimedOut));
        assert!(!canary.exists(), "expired target reached user entry");
        assert_eq!(
            child.version_exec_stop(initial, deadline()).unwrap(),
            Some(target),
            "target must still be actually stopped"
        );
        assert!(child.try_wait().unwrap().is_none());
        child.kill().unwrap();
        assert_eq!(exited(&mut child).signal(), Some(libc::SIGKILL));
        assert!(!canary.exists());
    }
}
