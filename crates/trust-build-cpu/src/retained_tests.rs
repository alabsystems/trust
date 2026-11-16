// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::fs::OpenOptions;
use std::io::{BufRead, Read, Write};
use std::num::NonZeroU32;
use std::os::fd::AsFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, RecvTimeoutError};
use std::time::{Duration, Instant};

use crate::tests::{KernelFixture, kernel_fixture, private_dir, private_tempdir};
use crate::{DIRECTORY_NAME, Owner, Pool, RetainedPool, RetainedSlotState};

const BACKEND: &str = "build-cpu-retained-v1";
const HANG_DETECTOR: Duration = Duration::from_secs(60);

fn width(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).unwrap()
}

fn owner() -> Owner {
    Owner::current(Some(123))
}

#[test]
fn retained_identity_binds_pool_inode_and_original_debt_generation() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let pool = RetainedPool::create_private(&directory.path().join("one"), width(1)).unwrap();
    let first = pool.try_acquire(owner()).unwrap().unwrap();
    let identity = first.identity().unwrap();
    assert_eq!(identity.slot, first.slot());
    assert_eq!(identity.owner, owner());
    assert_eq!(identity, first.identity().unwrap());
    first.settle().unwrap();
    let second = pool.try_acquire(owner()).unwrap().unwrap();
    let next = second.identity().unwrap();
    assert_eq!(identity.manifest, next.manifest);
    assert_eq!(identity.file, next.file);
    assert_ne!(identity.nonce, next.nonce);
    let other = RetainedPool::create_private(&directory.path().join("two"), width(1)).unwrap();
    let foreign = other.try_acquire(owner()).unwrap().unwrap();
    assert_ne!(identity.manifest, foreign.identity().unwrap().manifest);
    drop((second, foreign));
    assert!(pool.try_acquire(owner()).unwrap().is_none(), "saved identity is not settlement");
}

fn slot(root: &Path, number: u32) -> PathBuf {
    root.join(BACKEND).join(format!("slot-{number:08x}"))
}

fn overwrite(path: &Path, bytes: &[u8]) {
    let mut file =
        OpenOptions::new().write(true).create(true).truncate(true).mode(0o600).open(path).unwrap();
    file.write_all(bytes).unwrap();
    file.sync_all().unwrap();
}

fn assert_kernel_ownership_released(root: &Path, number: u32) {
    let file = OpenOptions::new().read(true).write(true).open(slot(root, number)).unwrap();
    file.try_lock().expect("no inherited CPU descriptor may explain retained debt");
    file.unlock().unwrap();
    // Close the raw probe before asking the API for capacity: otherwise the
    // probe's own lock could produce a false passing denial.
    drop(file);
}

#[test]
fn explicit_settlement_returns_exactly_the_original_unit() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let first = RetainedPool::create_private(&root, width(2)).unwrap();
    let second = RetainedPool::open_existing(&root).unwrap().unwrap();
    let a = first.try_acquire(owner()).unwrap().unwrap();
    let b = second.try_acquire(owner()).unwrap().unwrap();
    let original = a.slot();
    assert_eq!(a.owner(), owner());
    assert_ne!(original, b.slot());
    assert!(first.try_acquire(owner()).unwrap().is_none());
    assert!(second.snapshot().unwrap().iter().all(|state| {
        matches!(state, RetainedSlotState::Held { .. } | RetainedSlotState::Retained { .. })
    }));
    a.settle().unwrap();
    let replacement = second.try_acquire(owner()).unwrap().unwrap();
    assert_eq!(replacement.slot(), original);
    assert!(first.try_acquire(owner()).unwrap().is_none());
    replacement.settle().unwrap();
    b.settle().unwrap();
    assert!(
        first
            .snapshot()
            .unwrap()
            .iter()
            .all(|state| matches!(state, RetainedSlotState::Available { .. }))
    );
}

#[test]
fn dropping_the_capability_keeps_debt_after_its_kernel_lock_is_gone() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let lease = pool.try_acquire(owner()).unwrap().unwrap();
    let number = lease.slot();
    let record = std::fs::read(slot(&root, number)).unwrap();
    drop(lease);
    assert_kernel_ownership_released(&root, number);
    let reopened = RetainedPool::open_existing(&root).unwrap().unwrap();
    assert!(reopened.try_acquire(owner()).unwrap().is_none());
    assert_eq!(
        reopened.snapshot().unwrap(),
        [RetainedSlotState::Retained { slot: number, reported_owner: owner() }]
    );
    assert_eq!(std::fs::read(slot(&root, number)).unwrap(), record);
}

#[test]
fn private_birth_physically_fences_legacy_readers_and_writers() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let fence = root.join(DIRECTORY_NAME);
    let metadata = std::fs::symlink_metadata(&fence).unwrap();
    let bytes = std::fs::read(&fence).unwrap();
    assert!(metadata.is_file());
    assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
    assert!(Pool::open_in(&root, width(1)).is_err());
    assert!(Pool::open_existing(&root).is_err());
    let after = std::fs::symlink_metadata(&fence).unwrap();
    assert_eq!((after.dev(), after.ino()), (metadata.dev(), metadata.ino()));
    assert_eq!(std::fs::read(&fence).unwrap(), bytes);
    pool.try_acquire(owner()).unwrap().unwrap().settle().unwrap();
}

#[test]
fn birth_never_adopts_or_repairs_an_existing_legacy_domain() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("legacy");
    private_dir(&root);
    let legacy = Pool::open_in(&root, width(1)).unwrap();
    let lease = legacy.try_acquire(owner()).unwrap().unwrap();
    assert!(RetainedPool::create_private(&root, width(1)).is_err());
    assert!(!root.join(BACKEND).exists());
    assert!(legacy.try_acquire(owner()).unwrap().is_none());
    drop(lease);
    // V1 retains its original final-close semantics; adding a private retained
    // domain must not retroactively turn ordinary V1 records into debt.
    assert!(legacy.try_acquire(owner()).unwrap().is_some());
}

#[test]
fn observation_and_repeated_birth_never_repair_partial_or_existing_state() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let missing = directory.path().join("missing");
    assert!(RetainedPool::open_existing(&missing).unwrap().is_none());
    assert!(!missing.exists());

    for backend_present in [false, true] {
        let root = directory.path().join(format!("partial-{backend_present}"));
        private_dir(&root);
        let fence = root.join(DIRECTORY_NAME);
        overwrite(&fence, b"interrupted unpublished retained birth\n");
        if backend_present {
            private_dir(&root.join(BACKEND));
            overwrite(&slot(&root, 0), b"incomplete retained intent");
        }
        assert!(RetainedPool::open_existing(&root).is_err());
        assert!(RetainedPool::create_private(&root, width(1)).is_err());
        assert!(Pool::open_in(&root, width(1)).is_err());
        assert_eq!(std::fs::read(&fence).unwrap(), b"interrupted unpublished retained birth\n");
        assert_eq!(root.join(BACKEND).exists(), backend_present);
        assert!(!root.join(BACKEND).join("pool").exists());
    }

    let root = directory.path().join("complete");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let lease = pool.try_acquire(owner()).unwrap().unwrap();
    let retained = std::fs::read(slot(&root, lease.slot())).unwrap();
    assert!(RetainedPool::create_private(&root, width(1)).is_err());
    assert_eq!(std::fs::read(slot(&root, lease.slot())).unwrap(), retained);
    lease.settle().unwrap();
}

#[test]
fn corrupt_or_torn_intent_never_becomes_available_or_gets_rewritten() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    for case in 0..7 {
        let root = directory.path().join(format!("corrupt-{case}"));
        let pool = RetainedPool::create_private(&root, width(1)).unwrap();
        let lease = pool.try_acquire(owner()).unwrap().unwrap();
        let path = slot(&root, lease.slot());
        let record = std::fs::read_to_string(&path).unwrap();
        drop(lease);
        let corrupt = match case {
            0 => Vec::new(),
            1 => record.as_bytes()[..record.len() / 2].to_vec(),
            2 => record.as_bytes()[..record.len() - 1].to_vec(),
            3 => vec![b'x'; 4096],
            4 => format!("{record}\n").into_bytes(),
            5 => record.replacen("slot=0", "slot=1", 1).into_bytes(),
            6 => record.replacen("retained=1", "retained=0", 1).into_bytes(),
            _ => unreachable!(),
        };
        overwrite(&path, &corrupt);
        assert_kernel_ownership_released(&root, 0);
        assert!(pool.try_acquire(owner()).is_err(), "corrupt case {case} admitted work");
        assert!(pool.snapshot().is_err(), "corrupt case {case} appeared available");
        assert!(RetainedPool::open_existing(&root).is_err(), "reopened corrupt case {case}");
        assert!(RetainedPool::create_private(&root, width(1)).is_err());
        assert_eq!(std::fs::read(&path).unwrap(), corrupt);
    }
}

#[test]
fn a_changed_canonical_nonce_cannot_authorize_the_original_capability() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let lease = pool.try_acquire(owner()).unwrap().unwrap();
    assert!(lease.identity().is_ok());
    let path = slot(&root, lease.slot());
    let mut changed = std::fs::read(&path).unwrap();
    let position = changed.windows(b"nonce=".len()).position(|part| part == b"nonce=").unwrap()
        + b"nonce=".len();
    changed[position] = if changed[position] == b'0' { b'1' } else { b'0' };
    overwrite(&path, &changed);
    assert!(lease.identity().is_err());
    assert_eq!(std::fs::read(&path).unwrap(), changed);
    assert!(lease.settle().is_err());
    assert_kernel_ownership_released(&root, 0);
    let reopened = RetainedPool::open_existing(&root).unwrap().unwrap();
    assert!(reopened.try_acquire(owner()).unwrap().is_none());
    assert_eq!(std::fs::read(&path).unwrap(), changed);
}

#[test]
fn settlement_refuses_replaced_root_backend_manifest_fence_or_slot() {
    let _fixture = kernel_fixture();
    let directory = private_tempdir();
    for component in ["root", "backend", "manifest", "fence", "slot"] {
        let root = directory.path().join(component);
        let pool = RetainedPool::create_private(&root, width(1)).unwrap();
        let lease = pool.try_acquire(owner()).unwrap().unwrap();
        let retained = std::fs::read(slot(&root, 0)).unwrap();
        let original_slot = match component {
            "root" => {
                let former = directory.path().join("former-root");
                std::fs::rename(&root, &former).unwrap();
                private_dir(&root);
                slot(&former, 0)
            }
            "backend" => {
                let former = root.join("former-backend");
                std::fs::rename(root.join(BACKEND), &former).unwrap();
                private_dir(&root.join(BACKEND));
                former.join("slot-00000000")
            }
            "manifest" | "fence" | "slot" => {
                let path = match component {
                    "manifest" => root.join(BACKEND).join("pool"),
                    "fence" => root.join(DIRECTORY_NAME),
                    "slot" => slot(&root, 0),
                    _ => unreachable!(),
                };
                let former = path.with_extension("former");
                let bytes = std::fs::read(&path).unwrap();
                std::fs::rename(&path, &former).unwrap();
                overwrite(&path, &bytes);
                if component == "slot" { former } else { slot(&root, 0) }
            }
            _ => unreachable!(),
        };
        assert!(lease.settle().is_err(), "settled across changed {component} identity");
        assert!(pool.try_acquire(owner()).is_err());
        assert!(pool.snapshot().is_err());
        assert!(RetainedPool::open_existing(&root).is_err());
        assert_eq!(std::fs::read(original_slot).unwrap(), retained);
    }
}

const ROLE: &str = "TRUST_BUILD_CPU_RETAINED_TEST_ROLE";
const ROOT: &str = "TRUST_BUILD_CPU_RETAINED_TEST_ROOT";
const OWNER_READY: &str = "TRUST_RETAINED_OWNER_READY";
const WORKER_READY: &str = "TRUST_RETAINED_WORKER_READY";
const WORKER_ALIVE: &str = "TRUST_RETAINED_WORKER_ALIVE";
const WORKER_RELEASED: &str = "TRUST_RETAINED_WORKER_RELEASED";
#[cfg(any(target_os = "macos", target_os = "linux"))]
const SETTLEMENT_FAILED: &str = "TRUST_RETAINED_SETTLEMENT_FAILED";

fn mark(kind: &str) {
    println!("\n{kind}:{}", std::process::id());
    std::io::stdout().flush().unwrap();
}

fn actor_command() -> Option<u8> {
    let deadline = Instant::now() + HANG_DETECTOR;
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero(), "actor control exceeded its hang detector");
        let mut poll = libc::pollfd { fd: 0, events: libc::POLLIN, revents: 0 };
        let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
        // SAFETY: poll points to exactly one initialized pollfd for the actor's
        // owned stdin; it reads no Rust memory beyond that array element.
        let ready = unsafe { libc::poll(&raw mut poll, 1, milliseconds) };
        if ready < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            panic!("actor control poll failed: {error}");
        }
        if ready == 0 {
            continue;
        }
        let mut byte = [0];
        return match std::io::stdin().read(&mut byte).unwrap() {
            0 => None,
            1 => Some(byte[0]),
            _ => unreachable!(),
        };
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn fail_settlement_with_file_limit(root: &Path, retry: bool) {
    let pool = RetainedPool::open_existing(root).unwrap().unwrap();
    let mut lease = Some(pool.try_acquire(Owner::current(None)).unwrap().unwrap());
    let path = slot(root, lease.as_ref().unwrap().slot());
    let retained = std::fs::read(&path).unwrap();
    assert!(retained.len() > 8);
    let mut limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    // SAFETY: this initialized rlimit is writable for getrlimit's output. The
    // fixture is a separate process, so its limits cannot affect the driver.
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_FSIZE, &raw mut limit) }, 0);
    let original_limit = limit;
    assert!(limit.rlim_max >= 8, "fixture requires an eight-byte file limit");
    limit.rlim_cur = 8;
    // SAFETY: change only this actor's file-size soft limit, preserving its hard
    // limit. It performs no further regular-file writes except settlement.
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_FSIZE, &raw const limit) }, 0);
    // SAFETY: SIG_IGN is a valid disposition; this actor must receive EFBIG
    // instead of dying before it can report the actual failed write_all.
    assert_ne!(unsafe { libc::signal(libc::SIGXFSZ, libc::SIG_IGN) }, libc::SIG_ERR);
    let error =
        if retry { lease.as_mut().unwrap().settle_held() } else { lease.take().unwrap().settle() }
            .expect_err("the real settlement write must exceed RLIMIT_FSIZE");
    assert_eq!(error.raw_os_error(), Some(libc::EFBIG));
    let damaged = std::fs::read(&path).unwrap();
    assert!(damaged.len() <= 8, "settlement must actually truncate or partially write the slot");
    assert_ne!(damaged, retained);
    mark(SETTLEMENT_FAILED);
    if retry {
        assert!(
            pool.try_acquire(Owner::current(None)).unwrap().is_none(),
            "the same original guard remains held across uncertain settlement"
        );
        // SAFETY: restore only this isolated actor's original soft/hard limit.
        assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_FSIZE, &raw const original_limit) }, 0);
        lease
            .as_mut()
            .unwrap()
            .settle_held()
            .expect("same original held capability must repair its own uncertain write");
        assert!(
            pool.try_acquire(Owner::current(None)).unwrap().is_none(),
            "Free bytes alone cannot release the still-held original kernel guard"
        );
        drop(lease.take());
        pool.try_acquire(Owner::current(None)).unwrap().unwrap().settle().unwrap();
        mark("settlement-retried");
    }
}

#[test]
fn subprocess_retained_actor() {
    let fixture = kernel_fixture();
    let Ok(role) = std::env::var(ROLE) else { return };
    match role.as_str() {
        "owner" => {
            let root = PathBuf::from(std::env::var_os(ROOT).unwrap());
            let pool = RetainedPool::open_existing(&root).unwrap().unwrap();
            let _lease = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
            mark(OWNER_READY);
            // Only stdio is inherited. In particular, the CPU descriptor stays
            // CLOEXEC: the descendant's lifetime cannot preserve its flock.
            let input = std::io::stdin().as_fd().try_clone_to_owned().unwrap();
            let mut worker = actor_process(&fixture, "worker", &root)
                .stdin(Stdio::from(input))
                .stdout(Stdio::inherit())
                .stderr(Stdio::inherit())
                .spawn()
                .unwrap();
            worker.wait().expect("owner must supervise its actual child");
            panic!("worker exited before owner was killed");
        }
        "worker" => {
            mark(WORKER_READY);
            loop {
                match actor_command() {
                    Some(b'p') => mark(WORKER_ALIVE),
                    Some(b'q') => {
                        mark(WORKER_RELEASED);
                        break;
                    }
                    None => break,
                    other => panic!("unknown actor control: {other:?}"),
                }
            }
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        "failed-settlement" => {
            fail_settlement_with_file_limit(&PathBuf::from(std::env::var_os(ROOT).unwrap()), false);
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        "retry-held-settlement" => {
            fail_settlement_with_file_limit(&PathBuf::from(std::env::var_os(ROOT).unwrap()), true);
        }
        other => panic!("unknown retained actor role {other}"),
    }
}

fn actor_process(_fixture: &KernelFixture, role: &str, root: &Path) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", "retained_tests::subprocess_retained_actor", "--nocapture"])
        .env(ROLE, role)
        .env(ROOT, root);
    command
}

enum Event {
    Line(String),
    Closed,
}

struct Actor {
    child: Child,
    control: Option<ChildStdin>,
    events: Receiver<Event>,
    reader: Option<std::thread::JoinHandle<()>>,
}

impl Actor {
    fn start(fixture: &KernelFixture, root: &Path) -> Self {
        Self::start_role(fixture, "owner", root)
    }

    fn start_role(fixture: &KernelFixture, role: &str, root: &Path) -> Self {
        let mut child = actor_process(fixture, role, root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let control = child.stdin.take();
        let output = child.stdout.take().unwrap();
        let (send, events) = std::sync::mpsc::channel();
        let reader = std::thread::spawn(move || {
            for line in std::io::BufReader::new(output).lines() {
                match line {
                    Ok(line) => {
                        if send.send(Event::Line(line)).is_err() {
                            return;
                        }
                    }
                    Err(_) => break,
                }
            }
            let _ = send.send(Event::Closed);
        });
        Self { child, control, events, reader: Some(reader) }
    }

    fn marker(&self, expected: &str) -> u32 {
        let deadline = Instant::now() + HANG_DETECTOR;
        loop {
            match self.events.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
                Ok(Event::Line(line)) => {
                    if let Some(pid) =
                        line.strip_prefix(expected).and_then(|text| text.strip_prefix(':'))
                    {
                        return pid.parse().expect("actor marker must name its actual process");
                    }
                }
                Ok(Event::Closed) => panic!("actor closed its output before {expected}"),
                Err(error) => {
                    panic!("actor did not produce {expected} within its hang detector: {error}")
                }
            }
        }
    }

    fn send(&mut self, command: u8) {
        self.control.as_mut().unwrap().write_all(&[command]).unwrap();
    }

    fn kill_owner(&mut self) {
        self.child.kill().unwrap();
        assert!(!self.wait_exit().success(), "owner must die without running destructors");
    }

    fn wait_exit(&mut self) -> std::process::ExitStatus {
        let deadline = Instant::now() + HANG_DETECTOR;
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                return status;
            }
            assert!(Instant::now() < deadline, "actor exit exceeded its hang detector");
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    fn finish_worker(&mut self, worker: u32) {
        self.send(b'q');
        assert_eq!(self.marker(WORKER_RELEASED), worker);
        self.finish_output();
    }

    fn finish_output(&mut self) {
        self.control.take();
        let deadline = Instant::now() + HANG_DETECTOR;
        loop {
            match self.events.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
                Ok(Event::Closed) => break,
                Ok(Event::Line(_)) => {}
                Err(RecvTimeoutError::Disconnected) => panic!("actor reader lost its final EOF"),
                Err(RecvTimeoutError::Timeout) => {
                    panic!("worker output exceeded its hang detector")
                }
            }
        }
        self.reader.take().unwrap().join().unwrap();
    }
}

impl Drop for Actor {
    fn drop(&mut self) {
        // EOF also releases the orphan worker on assertion failure. Never kill
        // its recorded PID: unlike our direct Child, that PID is not pinned by
        // our custody and could already have been reused.
        self.control.take();
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
        if self.reader.is_some() {
            let deadline = Instant::now() + HANG_DETECTOR;
            loop {
                match self.events.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
                    Ok(Event::Line(_)) => {}
                    Ok(Event::Closed) | Err(RecvTimeoutError::Disconnected) => {
                        let _ = self.reader.take().unwrap().join();
                        break;
                    }
                    Err(RecvTimeoutError::Timeout) => break,
                }
            }
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn failed_settlement_write_leaves_damaged_debt_instead_of_new_capacity() {
    let fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let mut actor = Actor::start_role(&fixture, "failed-settlement", &root);
    assert_eq!(actor.marker(SETTLEMENT_FAILED), actor.child.id());
    assert!(actor.wait_exit().success(), "the actor must observe EFBIG and exit successfully");
    actor.finish_output();
    let damaged = std::fs::read(slot(&root, 0)).unwrap();
    assert!(damaged.len() <= 8);
    assert_kernel_ownership_released(&root, 0);
    assert!(pool.try_acquire(owner()).is_err());
    assert!(pool.snapshot().is_err());
    assert!(RetainedPool::open_existing(&root).is_err());
    assert!(Pool::open_in(&root, width(1)).is_err());
    assert!(Pool::open_existing(&root).is_err());
    assert_eq!(std::fs::read(slot(&root, 0)).unwrap(), damaged);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn same_original_held_capability_retries_real_failed_write_without_new_admission() {
    let fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let mut actor = Actor::start_role(&fixture, "retry-held-settlement", &root);
    assert_eq!(actor.marker(SETTLEMENT_FAILED), actor.child.id());
    assert_eq!(actor.marker("settlement-retried"), actor.child.id());
    assert!(actor.wait_exit().success());
    actor.finish_output();
    assert!(matches!(pool.snapshot().unwrap().as_slice(), [RetainedSlotState::Available { .. }]));
    pool.try_acquire(owner()).unwrap().unwrap().settle().unwrap();
}

#[test]
fn killed_owner_leaves_debt_while_its_actual_grandchild_survives() {
    let fixture = kernel_fixture();
    let directory = private_tempdir();
    let root = directory.path().join("retained");
    let pool = RetainedPool::create_private(&root, width(1)).unwrap();
    let mut actor = Actor::start(&fixture, &root);
    let original_owner = actor.marker(OWNER_READY);
    assert_eq!(original_owner, actor.child.id());
    let worker = actor.marker(WORKER_READY);
    assert_ne!(worker, original_owner);
    assert_ne!(worker, std::process::id());
    assert!(pool.try_acquire(owner()).unwrap().is_none());
    let retained = std::fs::read(slot(&root, 0)).unwrap();
    actor.kill_owner();
    actor.send(b'p');
    assert_eq!(actor.marker(WORKER_ALIVE), worker);
    assert_kernel_ownership_released(&root, 0);
    let reopened = RetainedPool::open_existing(&root).unwrap().unwrap();
    assert!(reopened.try_acquire(owner()).unwrap().is_none());
    assert_eq!(
        reopened.snapshot().unwrap(),
        [RetainedSlotState::Retained {
            slot: 0,
            reported_owner: Owner { pid: original_owner, birth: None },
        }]
    );
    assert_eq!(std::fs::read(slot(&root, 0)).unwrap(), retained);
    actor.finish_worker(worker);
    // Worker closure is not an invented recovery capability. The owner lost
    // the sole settlement authority, so even conclusive fixture drain cannot
    // silently reclaim its persisted debt.
    assert!(
        RetainedPool::open_existing(&root)
            .unwrap()
            .unwrap()
            .try_acquire(owner())
            .unwrap()
            .is_none()
    );
}
