use std::io::{BufRead, BufReader};
use std::os::unix::fs::PermissionsExt;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use super::*;

struct OwnedChild {
    child: std::process::Child,
    live: bool,
}
impl OwnedChild {
    fn stop(&mut self) {
        if self.live {
            let _ = self.child.kill();
            let _ = self.child.wait();
            self.live = false;
        }
    }
}
impl Drop for OwnedChild {
    fn drop(&mut self) {
        self.stop();
    }
}
impl std::ops::Deref for OwnedChild {
    type Target = std::process::Child;
    fn deref(&self) -> &Self::Target {
        &self.child
    }
}
impl std::ops::DerefMut for OwnedChild {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.child
    }
}

fn requirements(worktree: Option<PathBuf>, exclusive: bool, memory: u64) -> Requirements {
    Requirements::new(worktree, 4, 1, exclusive, memory).unwrap()
}

trait ObserveAttempt {
    fn observed_typed<T>(
        &mut self,
        available: Option<u64>,
        worktree: impl FnMut(&Path) -> io::Result<bool>,
        slots: impl FnMut(u32, u32) -> io::Result<bool>,
        acquire: impl FnMut(&Requirements) -> io::Result<Option<T>>,
    ) -> io::Result<Attempt<T>>;
    fn observed_attempt<T>(
        &mut self,
        available: Option<u64>,
        worktree: impl FnMut(&Path) -> io::Result<bool>,
        slots: impl FnMut(u32, u32) -> io::Result<bool>,
        acquire: impl FnMut(&Requirements) -> io::Result<Option<T>>,
    ) -> io::Result<Option<T>> {
        self.observed_typed(available, worktree, slots, acquire).map(Attempt::into_claim)
    }
}
impl ObserveAttempt for Ticket {
    fn observed_typed<T>(
        &mut self,
        available: Option<u64>,
        mut worktree: impl FnMut(&Path) -> io::Result<bool>,
        mut slots: impl FnMut(u32, u32) -> io::Result<bool>,
        mut acquire: impl FnMut(&Requirements) -> io::Result<Option<T>>,
    ) -> io::Result<Attempt<T>> {
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            match Ticket::attempt(self, available, &mut worktree, &mut slots, &mut acquire)? {
                Attempt::Waiting(Waiting::RegistryBusy) => {
                    // Only this independently observed transaction contention
                    // is retried. Priority, memory and resource refusals retain
                    // their original outcome and cannot be hidden by retries.
                    if Instant::now() >= deadline {
                        return Err(io::ErrorKind::TimedOut.into());
                    }
                    std::thread::sleep(Duration::from_millis(1));
                }
                result => return Ok(result),
            }
        }
    }
}

#[test]
fn transaction_contention_and_resource_waits_have_distinct_native_outcomes() {
    let root = crate::owner_only::tempdir();
    let mut ticket = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    let registry = ticket.directory.open_file("registry.lock", true).unwrap();
    assert!(try_exclusive(&registry).unwrap());
    let result = Ticket::attempt(
        &mut ticket,
        Some(0),
        |_| panic!("registry first"),
        |_, _| panic!("registry first"),
        |_| panic!("registry first"),
    )
    .unwrap();
    assert_eq!(result, Attempt::<()>::Waiting(Waiting::RegistryBusy));
    assert!(ticket.original.is_none());
    drop(registry);
    assert_eq!(
        ticket.observed_typed(Some(0), |_| Ok(true), |_, _| Ok(true), |_| Ok(None::<()>)).unwrap(),
        Attempt::Waiting(Waiting::ResourcesBusy)
    );
    let mut later = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    assert_eq!(
        later
            .observed_typed(Some(0), |_| Ok(true), |_, _| Ok(true), |_| panic!("older priority"))
            .unwrap(),
        Attempt::<()>::Waiting(Waiting::EarlierEligible {
            ticket: ticket.original.as_ref().unwrap().0
        })
    );
    let mut needs_memory = Ticket::open(root.path(), requirements(None, false, 1)).unwrap();
    assert_eq!(
        Ticket::attempt(
            &mut needs_memory,
            None,
            |_| panic!("memory first"),
            |_, _| panic!("memory first"),
            |_| panic!("memory first")
        )
        .unwrap(),
        Attempt::<()>::Waiting(Waiting::MemoryUnavailable)
    );
}
fn register(ticket: &mut Ticket) {
    assert!(
        ticket
            .observed_attempt(Some(u64::MAX), |_| Ok(true), |_, _| Ok(true), |_| Ok(None::<()>))
            .unwrap()
            .is_none()
    );
    assert!(ticket.original.is_some());
}
fn claim(ticket: &mut Ticket) -> io::Result<Option<()>> {
    ticket.observed_attempt(Some(u64::MAX), |_| Ok(true), |_, _| Ok(true), |_| Ok(Some(())))
}

#[test]
fn original_live_ticket_orders_claims_and_retires_before_later_admission() {
    let root = crate::owner_only::tempdir();
    let mut first = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    register(&mut first);
    let mut second = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    assert!(claim(&mut second).unwrap().is_none());
    assert_eq!(claim(&mut first).unwrap(), Some(()));
    assert!(first.original.is_none());
    assert_eq!(claim(&mut second).unwrap(), Some(()));
}

#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            transaction_contention_and_resource_waits_have_distinct_native_outcomes();
            original_live_ticket_orders_claims_and_retires_before_later_admission();
        },
    );
}

#[test]
fn busy_worktree_and_current_memory_can_make_older_ticket_ineligible() {
    let root = crate::owner_only::tempdir();
    let worktree = root.path().join("older-tree.lock");
    let mut first =
        Ticket::open(root.path(), requirements(Some(worktree.clone()), false, 100)).unwrap();
    register(&mut first);
    let mut second = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    assert_eq!(
        second
            .observed_attempt(
                Some(100),
                |path| {
                    assert_eq!(path, worktree);
                    Ok(false)
                },
                |_, _| Ok(true),
                |_| Ok(Some(()))
            )
            .unwrap(),
        Some(())
    );
    assert!(first.original.is_some());
    let mut third = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    assert_eq!(
        third
            .observed_attempt(
                Some(99),
                |_| panic!("memory veto precedes probe"),
                |_, _| panic!("memory veto precedes pool"),
                |_| Ok(Some(()))
            )
            .unwrap(),
        Some(())
    );
    assert!(first.original.is_some());
}

#[test]
fn older_exclusive_reserves_priority_even_while_slot_pool_is_draining() {
    let root = crate::owner_only::tempdir();
    let mut first = Ticket::open(root.path(), requirements(None, true, 0)).unwrap();
    register(&mut first);
    let mut later = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    let outcome = later
        .observed_attempt(
            Some(0),
            |_| Ok(true),
            |_, _| panic!("exclusive priority does not require empty pool"),
            |_| panic!("older exclusive retains priority"),
        )
        .unwrap();
    assert_eq!(outcome, None::<()>);
}

#[test]
fn unknown_own_memory_never_registers_or_calls_acquisition() {
    let root = crate::owner_only::tempdir();
    let mut ticket = Ticket::open(root.path(), requirements(None, false, 1)).unwrap();
    let outcome = ticket
        .observed_attempt(
            None,
            |_| panic!("no probe"),
            |_, _| panic!("no probe"),
            |_| panic!("no acquisition without memory"),
        )
        .unwrap();
    assert_eq!(outcome, None::<()>);
    assert!(ticket.original.is_none());
}

fn held_record(root: &Path, bytes: &[u8]) -> File {
    let queue = root.join("admission");
    fs::create_dir_all(&queue).unwrap();
    fs::set_permissions(&queue, fs::Permissions::from_mode(0o700)).unwrap();
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(queue.join("wait-99"))
        .unwrap();
    // The existing launcher uses Python fcntl.flock; exercise that kernel ABI
    // independently of Rust's std::fs::File lock implementation.
    assert_eq!(unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) }, 0);
    file.write_all(bytes).unwrap();
    file
}

#[test]
fn unsupported_and_duplicate_live_records_are_barriers_never_legacy_fallbacks() {
    // The immediate post-drop claim holds only while no unrelated test in this
    // binary has started a process with `held`'s open description live: a fork's
    // copy keeps the flock until it execs or exits, and on macOS (measured there
    // only) a posix_spawn's for the spawn itself. Isolated like the two fixtures
    // of 957bfd7af3 (TRUST-BUILD-TREE-FORK-ISOLATION-2).
    crate::trust_output_lock::tests::isolated_case(
        "admission::tests::unsupported_and_duplicate_live_records_are_barriers_never_legacy_fallbacks",
        || {
            for bytes in [
                &br#"{"native_admission_version":2,"pid":1,"requires":{"worktree":null,"slots":1,"needed":1,"exclusive":false,"memory":0}}"#[..],
                &br#"{"requires":{"worktree":null,"slots":1,"slots":2,"exclusive":false,"memory":0}}"#[..],
                &br#"{"requires":{"worktree":null,"slots":1,"exclusive":false,"memory":-1}}"#[..],
            ] {
                let root=crate::owner_only::tempdir();
                let held=held_record(root.path(),bytes);
                let mut later=Ticket::open(root.path(),requirements(None,false,0)).unwrap();
                assert_eq!(later.observed_attempt(Some(0), |_|panic!("unknown is barrier"),
                    |_,_|panic!("unknown is barrier"), |_|panic!("unknown is barrier")).unwrap(),None::<()>);
                drop(held);
                assert_eq!(claim(&mut later).unwrap(),Some(()));
            }
        },
    );
}

#[test]
fn existing_legacy_ticket_keeps_its_exact_worktree_memory_and_slot_requirements() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::tests::existing_legacy_ticket_keeps_its_exact_worktree_memory_and_slot_requirements",
        || {
            let root = crate::owner_only::tempdir();
            let path = root.path().join("actual-old-tree.lock");
            let bytes =
                serde_json::to_vec(&serde_json::json!({"pid":999999,"cmd":"diagnostic only",
                "cwd":root.path(),"started":0,"requires":{"worktree":path,"slots":4,
                    "needed":2,"memory":0.5,"exclusive":false}}))
                .unwrap();
            let held = held_record(root.path(), &bytes);
            let mut later = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
            assert_eq!(
                later
                    .observed_attempt(
                        Some(1 << 30),
                        |found| {
                            assert_eq!(found, path);
                            Ok(true)
                        },
                        |slots, needed| {
                            assert_eq!((slots, needed), (4, 2));
                            Ok(true)
                        },
                        |_| panic!("real held lease, not PID, establishes priority")
                    )
                    .unwrap(),
                None::<()>
            );
            drop(held);
            assert_eq!(claim(&mut later).unwrap(), Some(()));
        },
    );
}

#[test]
fn native_non_utf8_worktree_path_is_preserved_byte_for_byte() {
    let root = crate::owner_only::tempdir();
    let mut bytes = root.path().as_os_str().as_bytes().to_vec();
    bytes.extend_from_slice(b"/tree-\xff.lock");
    let path = PathBuf::from(std::ffi::OsString::from_vec(bytes));
    let mut first = Ticket::open(root.path(), requirements(Some(path.clone()), false, 0)).unwrap();
    register(&mut first);
    let mut later = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    assert_eq!(
        later
            .observed_attempt(
                Some(0),
                |actual| {
                    assert_eq!(actual, path);
                    Ok(true)
                },
                |_, _| Ok(true),
                |_| panic!("older native ticket")
            )
            .unwrap(),
        None::<()>
    );
}

#[test]
fn repeated_scans_do_not_reuse_the_directory_end_offset() {
    let root = crate::owner_only::tempdir();
    let mut first = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    register(&mut first);
    let mut later = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    for _ in 0..3 {
        assert_eq!(claim(&mut later).unwrap(), None);
    }
    assert_eq!(claim(&mut first).unwrap(), Some(()));
    assert_eq!(claim(&mut later).unwrap(), Some(()));
}

#[test]
fn replaced_ticket_or_directory_is_retained_and_never_unlinked_as_original() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::tests::replaced_ticket_or_directory_is_retained_and_never_unlinked_as_original",
        || {
            let root = crate::owner_only::tempdir();
            let mut ticket = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
            register(&mut ticket);
            let name = ticket.original.as_ref().unwrap().1.clone();
            let queue = root.path().join("admission");
            fs::rename(queue.join(&name), queue.join("retained-original")).unwrap();
            crate::owner_only::write(&queue.join(&name), b"foreign replacement");
            assert!(ticket.close().is_err());
            drop(ticket);
            assert_eq!(fs::read(queue.join(&name)).unwrap(), b"foreign replacement");
            let mut ticket = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
            register(&mut ticket);
            fs::rename(&queue, root.path().join("original-directory")).unwrap();
            crate::owner_only::create_dir(&queue);
            let sentinel = queue.join("wait-1");
            crate::owner_only::write(&sentinel, b"foreign namespace");
            assert!(claim(&mut ticket).is_err());
            drop(ticket);
            assert_eq!(fs::read(sentinel).unwrap(), b"foreign namespace");
        },
    );
}

#[test]
fn changed_original_record_refuses_retirement() {
    // `close` retains the record, Ok(false), while another process holds the
    // registry lock; an unrelated test's fork or spawn that inherited this
    // test's registry description is one. Isolated for the same reason as above
    // (TRUST-BUILD-TREE-FORK-ISOLATION-2).
    crate::trust_output_lock::tests::isolated_case(
        "admission::tests::changed_original_record_refuses_retirement",
        || {
            let root = crate::owner_only::tempdir();
            let mut ticket = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
            register(&mut ticket);
            let path = ticket.directory.path.join(&ticket.original.as_ref().unwrap().1);
            fs::write(&path, b"changed own record").unwrap();
            assert!(ticket.close().is_err());
            assert!(path.exists());
        },
    );
}

#[test]
fn actual_child_exit_releases_priority_without_pid_liveness_guesses() {
    const ROLE: &str = "TRUST_NATIVE_ADMISSION_PRIORITY_CHILD";
    if let Some(root) = std::env::var_os(ROLE) {
        let mut ticket = Ticket::open(Path::new(&root), requirements(None, false, 0)).unwrap();
        register(&mut ticket);
        println!("native-admission-child-held");
        io::stdout().flush().unwrap();
        let mut byte = [0];
        io::stdin().read_exact(&mut byte).unwrap();
        std::process::exit(0); // no Ticket drop; only the kernel closes leases
    }
    let root = crate::owner_only::tempdir();
    let child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "admission::tests::actual_child_exit_releases_priority_without_pid_liveness_guesses",
            "--nocapture",
        ])
        .env(ROLE, root.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut child = OwnedChild { child, live: true };
    let stdout = child.stdout.take().unwrap();
    let (send, receive) = mpsc::sync_channel(1);
    let reader = std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines() {
            if line.unwrap().contains("native-admission-child-held") {
                let _ = send.send(());
            }
        }
    });
    if receive.recv_timeout(Duration::from_secs(30)).is_err() {
        child.stop();
        reader.join().unwrap();
        panic!("original child did not establish its kernel-held ticket");
    }
    let mut later = Ticket::open(root.path(), requirements(None, false, 0)).unwrap();
    assert_eq!(claim(&mut later).unwrap(), None);
    child.stdin.take().unwrap().write_all(b"x").unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            child.live = false;
            break status;
        }
        if Instant::now() >= deadline {
            child.stop();
            reader.join().unwrap();
            panic!("owned child did not exit");
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    reader.join().unwrap();
    assert!(status.success());
    assert_eq!(claim(&mut later).unwrap(), Some(()));
}
