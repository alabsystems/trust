//! Trust: exercise actual output-lock contention in separate processes.

#![cfg(unix)]

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use super::OutputLock;

const ACTOR: &str = "TRUST_OUTPUT_LOCK_TEST_ACTOR";
const OUT: &str = "TRUST_OUTPUT_LOCK_TEST_OUT";
const EVENTS: &str = "TRUST_OUTPUT_LOCK_TEST_EVENTS";
const ACTOR_TEST: &str = "trust_output_lock::tests::output_lock_actor";
const HANG: Duration = Duration::from_secs(60);

#[test]
fn offered_original_output_pair_stays_locked_until_the_actual_final_close() {
    isolated("offered_original_output_pair_stays_locked_until_the_actual_final_close", || {
        use std::os::fd::AsRawFd as _;
        let temp = Temp::new();
        let out = temp.root.join("output");
        let guard = OutputLock::try_acquire(&out).unwrap().unwrap();
        // SAFETY: these original descriptions are observed/duplicated close-only;
        // no unlock, offset, flag or original descriptor mutation occurs.
        let offered = unsafe { guard.original_descriptions() }.unwrap();
        assert_eq!(offered.root(), fs::canonicalize(&out).unwrap());
        let root: File = offered.directory().try_clone_to_owned().unwrap().into();
        let held: File = offered.lock().try_clone_to_owned().unwrap().into();
        assert_eq!(root.metadata().unwrap().ino(), fs::metadata(&out).unwrap().ino());
        let lock = out.join("lock");
        assert_eq!(held.metadata().unwrap().ino(), fs::metadata(&lock).unwrap().ino());
        for (fd, expected) in [(root.as_raw_fd(), libc::O_RDONLY), (held.as_raw_fd(), libc::O_RDWR)]
        {
            assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFL) } & libc::O_ACCMODE, expected);
            assert_ne!(unsafe { libc::fcntl(fd, libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
        }
        drop(guard);
        let independent = OpenOptions::new().read(true).write(true).open(&lock).unwrap();
        assert!(matches!(independent.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
        drop(held);
        independent.try_lock().unwrap();
    });
}

#[test]
fn replaced_output_name_cannot_export_a_replacement_description() {
    isolated("replaced_output_name_cannot_export_a_replacement_description", || {
        let temp = Temp::new();
        let out = temp.root.join("output");
        let guard = OutputLock::try_acquire(&out).unwrap().unwrap();
        fs::rename(out.join("lock"), out.join("original-lock")).unwrap();
        fs::write(out.join("lock"), b"replacement").unwrap();
        assert!(guard.original_directory().is_err());
        // SAFETY: failure must return before any description can be offered.
        assert!(unsafe { guard.original_descriptions() }.is_err());
    });
}

struct Temp {
    root: PathBuf,
}

impl Temp {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..1024 {
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir()
                .join(format!("trust-output-lock-{}-{sequence}", std::process::id()));
            match fs::DirBuilder::new().mode(0o700).create(&root) {
                Ok(()) => return Self { root },
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create private fixture {}: {error}", root.display()),
            }
        }
        panic!("cannot create a private output-lock fixture");
    }
}

impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

struct Actor {
    child: Child,
    input: Option<ChildStdin>,
}

impl Actor {
    fn start(mode: &str, out: &Path, events: &Path) -> Self {
        let mut child = Command::new(std::env::current_exe().expect("current test executable"))
            .args(["--exact", ACTOR_TEST, "--nocapture", "--test-threads=1"])
            .env(ACTOR, mode)
            .env(OUT, out)
            .env(EVENTS, events)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()
            .expect("start the actual output-lock actor");
        let input = child.stdin.take();
        Self { child, input }
    }

    fn await_events(&mut self, path: &Path, expected: &str) {
        let deadline = Instant::now() + HANG;
        loop {
            match fs::read_to_string(path) {
                Ok(events) if events == expected => return,
                Ok(events) => assert!(
                    expected.starts_with(&events),
                    "unexpected actor events: {events:?}; expected {expected:?}"
                ),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => panic!("read actor events: {error}"),
            }
            assert!(self.child.try_wait().unwrap().is_none(), "actor exited before {expected:?}");
            assert!(Instant::now() < deadline, "output-lock actor did not reach {expected:?}");
            std::thread::sleep(Duration::from_millis(2));
        }
    }

    fn release(mut self) {
        self.input.take().unwrap().write_all(b"x").expect("release the actor's stdin barrier");
        let deadline = Instant::now() + HANG;
        loop {
            if let Some(status) = self.child.try_wait().expect("observe actual actor exit") {
                assert!(status.success(), "output-lock actor failed: {status}");
                return;
            }
            assert!(Instant::now() < deadline, "output-lock actor did not exit");
            std::thread::sleep(Duration::from_millis(2));
        }
    }
}

impl Drop for Actor {
    fn drop(&mut self) {
        // Only this exact owned child is stopped on a failed test; no PID/group lookup.
        if !matches!(self.child.try_wait(), Ok(Some(_))) {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

const ISOLATED: &str = "TRUST_OUTPUT_LOCK_TEST_ISOLATED";

/// Whether the calling thread runs its test alone, in the fresh process that
/// `isolated_case` started for it.
#[cfg(any(target_os = "macos", target_os = "linux"))] // Only admission's tests ask.
pub(crate) fn running_alone() -> bool {
    let thread = std::thread::current();
    let test = thread.name().map(std::ffi::OsStr::new);
    test.is_some() && std::env::var_os(ISOLATED).as_deref() == test
}

/// Runs `body` alone, in a fresh process of this test binary that runs nothing else. A
/// lock's release is seen at once only where no other thread spawns a process: a `fork`
/// or `posix_spawn` beside a close copies the closed descriptor into the child until its
/// exec, so the open file description and its `flock` outlive the close (trust-platform's
/// conformance measures it as the "posix_spawn window"). This binary's other tests spawn
/// processes, so each test here checks its releases in its own process.
fn isolated(name: &str, body: impl FnOnce()) {
    // The name must be the calling test's own, or the child would run another test.
    let test = format!("trust_output_lock::tests::{name}");
    isolated_case(&test, body)
}

pub(crate) fn isolated_case(test: &str, body: impl FnOnce()) {
    assert_eq!(std::thread::current().name(), Some(test), "isolation names its own test");
    if std::env::var_os(ISOLATED).as_deref() == Some(std::ffi::OsStr::new(test)) {
        return body();
    }
    let output = Command::new(std::env::current_exe().expect("current test executable"))
        .args(["--exact", test, "--test-threads=1"])
        .env(ISOLATED, test)
        .stdin(Stdio::null())
        .output()
        .expect("run the test alone");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let report = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success(), "{test}, run alone, failed:\n{report}");
    assert!(stdout.contains("test result: ok. 1 passed;"), "{test} did not run alone:\n{report}");
}

fn event(path: &Path, text: &str) {
    OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .unwrap()
        .write_all(text.as_bytes())
        .unwrap();
}

#[test]
fn output_lock_actor() {
    let Some(mode) = std::env::var_os(ACTOR) else {
        return;
    };
    let out = PathBuf::from(std::env::var_os(OUT).unwrap());
    let events = PathBuf::from(std::env::var_os(EVENTS).unwrap());
    let guard = if mode == "hold" {
        OutputLock::acquire(&out, |_| panic!("an uncontended lock must not report Busy"))
            .expect("actor acquires its output lock")
    } else {
        assert_eq!(mode, "wait");
        OutputLock::acquire(&out, |owner| {
            event(&events, &format!("busy:{}\n", owner.expect("actual holder PID")));
        })
        .expect("actor acquires after the original holder releases")
    };
    guard.check_current().unwrap();
    event(&events, "acquired\n");
    let mut barrier = [0];
    std::io::stdin().read_exact(&mut barrier).expect("inherited stdin barrier");
    assert_eq!(barrier, *b"x");
    guard.check_current().unwrap();
    drop(guard);
}

fn contender(lock: &Path) -> File {
    OpenOptions::new().read(true).write(true).open(lock).expect("open existing rendezvous inode")
}

fn assert_busy(file: &File) {
    assert!(matches!(file.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
}

#[test]
fn a_separate_process_holds_the_actual_inode_until_the_pipe_releases_it() {
    isolated("a_separate_process_holds_the_actual_inode_until_the_pipe_releases_it", || {
        let temp = Temp::new();
        let out = temp.root.join("missing/parent/build");
        let events = temp.root.join("events");
        let mut actor = Actor::start("hold", &out, &events);
        actor.await_events(&events, "acquired\n");
        let lock = out.join("lock");
        assert_eq!(fs::read_to_string(&lock).unwrap().trim(), actor.child.id().to_string());
        let independent = contender(&lock);
        assert_busy(&independent);
        assert!(OutputLock::try_acquire(&out).unwrap().is_none());
        // A refused contender must not truncate the live owner's PID.
        assert_eq!(fs::read_to_string(&lock).unwrap().trim(), actor.child.id().to_string());
        actor.release();
        independent.try_lock().expect("actual OS lock is released after child guard Drop");
        drop(independent);
        let guard = OutputLock::try_acquire(&out).unwrap().expect("a later owner acquires");
        assert_eq!(fs::read_to_string(lock).unwrap().trim(), std::process::id().to_string());
        guard.check_current().unwrap();
    });
}

#[test]
fn a_blocking_waiter_reports_the_holder_once_and_then_owns_the_lock() {
    isolated("a_blocking_waiter_reports_the_holder_once_and_then_owns_the_lock", || {
        let temp = Temp::new();
        let out = temp.root.join("build");
        let original = OutputLock::try_acquire(&out).unwrap().unwrap();
        let events = temp.root.join("events");
        let busy = format!("busy:{}\n", std::process::id());
        let mut actor = Actor::start("wait", &out, &events);
        actor.await_events(&events, &busy);
        assert_busy(&contender(&out.join("lock")));
        assert!(actor.child.try_wait().unwrap().is_none());
        drop(original);
        actor.await_events(&events, &format!("{busy}acquired\n"));
        assert_eq!(
            fs::read_to_string(out.join("lock")).unwrap().trim(),
            actor.child.id().to_string()
        );
        let independent = contender(&out.join("lock"));
        assert_busy(&independent);
        actor.release();
        independent.try_lock().expect("the completed waiter released the actual lock");
    });
}

#[test]
fn existing_only_acquisition_never_creates_a_missing_root_or_leaf() {
    isolated("existing_only_acquisition_never_creates_a_missing_root_or_leaf", || {
        let temp = Temp::new();
        let out = temp.root.join("missing/build");
        assert!(OutputLock::try_acquire_existing(&out).is_err());
        assert!(!temp.root.join("missing").exists(), "donor probing must not create directories");
        fs::create_dir_all(&out).unwrap();
        let marker = out.join("retained-seed");
        fs::write(&marker, b"existing seed bytes").unwrap();
        assert!(OutputLock::try_acquire_existing(&out).is_err());
        assert!(!out.join("lock").exists(), "donor probing must not create a rendezvous inode");
        assert_eq!(fs::read(marker).unwrap(), b"existing seed bytes");

        let original = OutputLock::try_acquire(&out).unwrap().unwrap();
        let before = fs::metadata(out.join("lock")).unwrap();
        assert!(OutputLock::try_acquire_existing(&out).unwrap().is_none());
        assert_eq!(
            fs::read_to_string(out.join("lock")).unwrap().trim(),
            std::process::id().to_string()
        );
        drop(original);
        let guard = OutputLock::try_acquire_existing(&out).unwrap().expect("existing donor lock");
        guard.check_current().unwrap();
        let after = fs::metadata(out.join("lock")).unwrap();
        assert_eq!((before.dev(), before.ino()), (after.dev(), after.ino()));
    });
}

#[test]
fn a_logical_symlink_root_is_supported_but_retargeting_retains_the_old_lock() {
    isolated("a_logical_symlink_root_is_supported_but_retargeting_retains_the_old_lock", || {
        let temp = Temp::new();
        let real = temp.root.join("build.noindex");
        let replacement = temp.root.join("other-build.noindex");
        fs::create_dir(&real).unwrap();
        fs::create_dir(&replacement).unwrap();
        let logical = temp.root.join("build");
        symlink(&real, &logical).unwrap();
        let guard = OutputLock::try_acquire(&logical).unwrap().expect("logical build symlink");
        guard.check_current().unwrap();
        let independent = contender(&real.join("lock"));
        fs::remove_file(&logical).unwrap();
        symlink(&replacement, &logical).unwrap();
        assert!(guard.check_current().is_err());
        assert_busy(&independent);
        assert!(!replacement.join("lock").exists());
        drop(guard);
        independent.try_lock().unwrap();
    });
}

#[test]
fn root_replacement_is_detected_without_releasing_the_original_inode() {
    isolated("root_replacement_is_detected_without_releasing_the_original_inode", || {
        let temp = Temp::new();
        let out = temp.root.join("build");
        let guard = OutputLock::try_acquire(&out).unwrap().unwrap();
        let old = temp.root.join("old-build");
        fs::rename(&out, &old).unwrap();
        fs::create_dir(&out).unwrap();
        let independent = contender(&old.join("lock"));
        assert!(guard.check_current().is_err());
        assert_busy(&independent);
        drop(guard);
        independent.try_lock().unwrap();
    });
}

#[test]
fn leaf_replacement_is_detected_without_releasing_the_original_inode() {
    isolated("leaf_replacement_is_detected_without_releasing_the_original_inode", || {
        let temp = Temp::new();
        let out = temp.root.join("build");
        let guard = OutputLock::try_acquire(&out).unwrap().unwrap();
        let lock = out.join("lock");
        let old = out.join("old-lock");
        fs::rename(&lock, &old).unwrap();
        fs::write(&lock, b"replacement must remain unchanged").unwrap();
        let independent = contender(&old);
        assert!(guard.check_current().is_err());
        assert_busy(&independent);
        assert_eq!(fs::read(&lock).unwrap(), b"replacement must remain unchanged");
        drop(guard);
        independent.try_lock().unwrap();
    });
}

#[test]
fn redirected_or_nonregular_lock_leaves_are_refused_without_mutation() {
    isolated("redirected_or_nonregular_lock_leaves_are_refused_without_mutation", || {
        for case in ["symlink", "hardlink", "fifo", "directory", "group-write"] {
            let temp = Temp::new();
            let out = temp.root.join("build");
            fs::create_dir(&out).unwrap();
            let lock = out.join("lock");
            let target = temp.root.join("preserved");
            fs::write(&target, b"keep the original bytes").unwrap();
            match case {
                "symlink" => symlink(&target, &lock).unwrap(),
                "hardlink" => fs::hard_link(&target, &lock).unwrap(),
                "fifo" => {
                    use std::os::unix::ffi::OsStrExt;
                    let path = std::ffi::CString::new(lock.as_os_str().as_bytes()).unwrap();
                    // SAFETY: a valid C pathname in this test's private directory.
                    assert_eq!(unsafe { libc::mkfifo(path.as_ptr(), 0o600) }, 0);
                }
                "directory" => fs::create_dir(&lock).unwrap(),
                "group-write" => {
                    fs::write(&lock, b"unsafe writable lock").unwrap();
                    fs::set_permissions(&lock, fs::Permissions::from_mode(0o620)).unwrap();
                }
                _ => unreachable!(),
            }
            let before = fs::symlink_metadata(&lock).unwrap();
            assert!(OutputLock::try_acquire(&out).is_err(), "accepted {case}");
            let after = fs::symlink_metadata(&lock).unwrap();
            assert_eq!(
                (before.dev(), before.ino(), before.mode()),
                (after.dev(), after.ino(), after.mode())
            );
            assert_eq!(fs::read(&target).unwrap(), b"keep the original bytes");
            if case == "group-write" {
                assert_eq!(fs::read(&lock).unwrap(), b"unsafe writable lock");
            }
        }
    });
}

#[test]
fn permissions_drift_is_refused_while_the_original_lock_remains_held() {
    isolated("permissions_drift_is_refused_while_the_original_lock_remains_held", || {
        let temp = Temp::new();
        let out = temp.root.join("build");
        let guard = OutputLock::try_acquire(&out).unwrap().unwrap();
        let lock = out.join("lock");
        let independent = contender(&lock);
        fs::set_permissions(&lock, fs::Permissions::from_mode(0o620)).unwrap();
        assert!(guard.check_current().is_err());
        assert_busy(&independent);
        drop(guard);
        independent.try_lock().unwrap();
    });
}
