use std::num::NonZeroU32;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use super::*;

macro_rules! isolated {
    ($name:ident, $body:block) => {
        crate::trust_output_lock::tests::isolated_case(
            concat!("admission::resources::adoption::tests::", stringify!($name)),
            || $body,
        )
    };
}

#[test]
fn repeat_observation_refuses_incomplete_exclusive_coverage_after_new_historical_slot() {
    isolated!(
        repeat_observation_refuses_incomplete_exclusive_coverage_after_new_historical_slot,
        {
            let f = Fixture::new();
            registered(&mut f.adoption(true));
            let record = f.records().pop().unwrap();
            let before = fs::read(&record).unwrap();
            crate::launcher_file::write(&f.namespace.join("slot-9"), &[]);
            assert!(
                f.adoption(true).attempt().is_err(),
                "incomplete prior coverage reported as already registered"
            );
            assert_eq!(fs::read(record).unwrap(), before);
        }
    );
}

// The adoption tests isolate themselves, so each runs by name in its own
// process, inside one whose umask is 002.
#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::existing_tests_under_umask_002(
        "admission::resources::adoption::tests::fixture_tests_pass_under_a_group_writable_umask",
        &[
            "admission::resources::adoption::tests::exclusive_registration_covers_all_actual_historical_slots",
            "admission::resources::adoption::tests::pid_working_directory_and_exited_identity_refuse_without_publication",
        ],
    );
}

#[test]
fn repeat_observation_refuses_contradictory_duplicate_exclusive_labels() {
    isolated!(repeat_observation_refuses_contradictory_duplicate_exclusive_labels, {
        let f = Fixture::new();
        registered(&mut f.adoption(false));
        let record = f.records().pop().unwrap();
        let original = String::from_utf8(fs::read(&record).unwrap()).unwrap();
        let changed =
            original.replace("\"exclusive\":false", "\"exclusive\":false,\"exclusive\":true");
        assert_ne!(changed, original);
        fs::write(&record, &changed).unwrap();
        assert!(
            f.adoption(false).attempt().is_err(),
            "contradictory labels reported as already registered"
        );
        assert_eq!(fs::read(record).unwrap(), changed.as_bytes());
    });
}

struct OwnedChild(Child);
impl Drop for OwnedChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
struct Fixture {
    child: OwnedChild,
    pool: Pool,
    root: PathBuf,
    namespace: PathBuf,
    _temporary: tempfile::TempDir,
}
impl Fixture {
    fn new() -> Self {
        Self::spawn(|root| Command::new("/bin/sleep").arg("120").current_dir(root).spawn().unwrap())
    }
    fn spawn(start: impl FnOnce(&Path) -> Child) -> Self {
        let temporary = crate::owner_only::tempdir();
        let root = fs::canonicalize(temporary.path()).unwrap();
        let namespace = root.join("legacy");
        crate::owner_only::create_dir(&namespace);
        let pool = Pool::open_in(&root.join("capacity"), NonZeroU32::new(12).unwrap()).unwrap();
        let child = OwnedChild(start(&root));
        Self { child, pool, root, namespace, _temporary: temporary }
    }
    fn adoption(&self, exclusive: bool) -> Adoption {
        self.adoption_with_worktree(exclusive, Some(self.root.join("worktree.lock")))
    }
    fn adoption_with_worktree(&self, exclusive: bool, worktree: Option<PathBuf>) -> Adoption {
        let cwd = Directory::open(&self.root).unwrap();
        let identity = identity::checked(self.child.0.id(), &cwd).unwrap();
        let required = Requirements::new(worktree, 2, 1, exclusive, 1).unwrap();
        let coordinator =
            Coordinator::open(&self.namespace, &self.namespace.join("adopted"), required).unwrap();
        Adoption {
            coordinator,
            cwd,
            identity,
            pool: self.pool.clone(),
            publication_started: false,
            poisoned: false,
        }
    }
    fn records(&self) -> Vec<PathBuf> {
        let path = self.namespace.join("adopted");
        if !path.exists() {
            return Vec::new();
        }
        let mut rows = fs::read_dir(path)
            .unwrap()
            .map(|row| row.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "json"))
            .collect::<Vec<_>>();
        rows.sort();
        rows
    }
}
struct Hook;
impl Hook {
    fn install(hook: impl FnMut(PublishStage, &Path) -> io::Result<()> + 'static) -> Self {
        PUBLISH_HOOK.with(|slot| {
            assert!(slot.borrow().is_none());
            *slot.borrow_mut() = Some(Box::new(hook));
        });
        Self
    }
}
impl Drop for Hook {
    fn drop(&mut self) {
        PUBLISH_HOOK.with(|slot| {
            slot.borrow_mut().take();
        });
    }
}
fn outcome(adoption: &mut Adoption) -> AdoptionOutcome {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        match adoption.attempt().unwrap() {
            Attempt::Admitted(outcome) => return outcome,
            Attempt::Waiting(reason) => {
                assert!(Instant::now() < deadline, "actual registration still waiting: {reason:?}");
                std::thread::sleep(Duration::from_millis(1));
            }
        }
    }
}
fn registered(adoption: &mut Adoption) -> AdoptionObservation {
    match outcome(adoption) {
        AdoptionOutcome::Registered(observation) => observation,
        other => panic!("expected registration, got {other:?}"),
    }
}
fn debt(path: &Path, registry: &Path) -> io::Result<bool> {
    let file = OpenOptions::new().read(true).write(true).open(path)?;
    if !try_exclusive(&file)? {
        return Ok(true);
    }
    super::super::super::adopted::available(registry, path).map(|available| !available)
}
fn released(path: &Path) -> bool {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        let file = File::open(path).unwrap();
        if try_exclusive(&file).unwrap() {
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}

fn wait_marker(output: &mut std::process::ChildStdout, marker: &[u8], deadline: Instant) {
    let mut prefix = Vec::new();
    loop {
        assert!(
            Instant::now() < deadline,
            "owned actor response timed out: {}",
            String::from_utf8_lossy(&prefix)
        );
        let mut poll = libc::pollfd { fd: output.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        let milliseconds =
            deadline.saturating_duration_since(Instant::now()).as_millis().min(1000) as i32;
        let ready = unsafe { libc::poll(&mut poll, 1, milliseconds) };
        if ready < 0 {
            assert_eq!(io::Error::last_os_error().kind(), io::ErrorKind::Interrupted);
            continue;
        }
        if ready == 0 {
            continue;
        }
        let mut byte = 0_u8;
        let count = unsafe { libc::read(output.as_raw_fd(), (&mut byte as *mut u8).cast(), 1) };
        assert_eq!(
            count,
            1,
            "owned actor ended before response: {}",
            String::from_utf8_lossy(&prefix)
        );
        prefix.push(byte);
        if prefix.ends_with(marker) {
            return;
        }
        assert!(prefix.len() <= 16_384, "actor response exceeds fixture bound");
    }
}

#[test]
fn late_repeat_observation_rechecks_actual_process_after_second_publisher_and_cwd_change() {
    isolated!(
        late_repeat_observation_rechecks_actual_process_after_second_publisher_and_cwd_change,
        {
            use std::io::{Read as _, Write as _};
            use std::process::Stdio;
            const ACTOR: &str = "TRUST_ADOPTION_CWD_ACTOR";
            if let Some(mode) = std::env::var_os(ACTOR) {
                assert_eq!(mode, "target");
                println!("TARGET_READY");
                io::stdout().flush().unwrap();
                let mut byte = [0];
                io::stdin().read_exact(&mut byte).unwrap();
                assert_eq!(byte, *b"c");
                std::env::set_current_dir(std::env::var_os("TRUST_ADOPTION_OTHER_CWD").unwrap())
                    .unwrap();
                println!("TARGET_CHANGED");
                io::stdout().flush().unwrap();
                let _ = io::stdin().read(&mut byte);
                return;
            }
            let mut f = Fixture::spawn(|root| {
                crate::owner_only::create_dir(&root.join("other"));
                Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "admission::resources::adoption::tests::late_repeat_observation_rechecks_actual_process_after_second_publisher_and_cwd_change", "--nocapture"])
                .env(ACTOR, "target").env("TRUST_ADOPTION_OTHER_CWD", root.join("other"))
                .current_dir(root).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap()
            });
            let deadline = Instant::now() + Duration::from_secs(60);
            let mut output = f.child.0.stdout.take().unwrap();
            let mut input = f.child.0.stdin.take().unwrap();
            wait_marker(&mut output, b"TARGET_READY\n", deadline);
            let mut original = f.adoption_with_worktree(false, None);
            let root = f.root.clone();
            let namespace = f.namespace.clone();
            let pool = f.pool.clone();
            let pid = f.child.0.id();
            let _hook = Hook::install(move |stage, _| {
                if stage != PublishStage::AfterEarlyPrior {
                    return Ok(());
                }
                let root2 = root.clone();
                let namespace2 = namespace.clone();
                let pool2 = pool.clone();
                // A distinct actual coordinator publishes first. With no worktree
                // lock, A can subsequently own the other real free slot while B's
                // live same-birth virtual debt remains on its original first slot.
                std::thread::spawn(move || {
                    let cwd = Directory::open(&root2).unwrap();
                    let identity = identity::checked(pid, &cwd).unwrap();
                    let coordinator = Coordinator::open(
                        &namespace2,
                        &namespace2.join("adopted"),
                        Requirements::new(None, 2, 1, false, 1).unwrap(),
                    )
                    .unwrap();
                    let mut second = Adoption {
                        coordinator,
                        cwd,
                        identity,
                        pool: pool2,
                        publication_started: false,
                        poisoned: false,
                    };
                    registered(&mut second);
                })
                .join()
                .unwrap();
                input.write_all(b"c").unwrap();
                input.flush().unwrap();
                wait_marker(&mut output, b"TARGET_CHANGED\n", deadline);
                assert_eq!(
                    fs::canonicalize(
                        crate::trust_repo_lock::management::process::cwd(pid).unwrap()
                    )
                    .unwrap(),
                    root.join("other")
                );
                Ok(())
            });
            let result = original.attempt();
            assert!(
                result.is_err(),
                "late prior reported an original-process observation after real cwd changed: {result:?}"
            );
            assert_eq!(f.records().len(), 1, "the actual second publisher's debt must remain");
        }
    );
}

#[test]
fn actual_registration_retains_logical_debt_after_producer_drop_without_kernel_watcher() {
    isolated!(
        actual_registration_retains_logical_debt_after_producer_drop_without_kernel_watcher,
        {
            let mut f = Fixture::new();
            let mut owner = f.adoption(false);
            let observation = registered(&mut owner);
            assert_eq!(observation.pid, f.child.0.id());
            assert_eq!(observation.lease_paths.len(), 2);
            assert!(!observation.lease_paths.contains(&f.namespace.join("admission.lock")));
            let record = f.records().pop().unwrap();
            let value: serde_json::Value =
                serde_json::from_slice(&fs::read(&record).unwrap()).unwrap();
            assert_eq!(value["cwd"], f.root.to_str().unwrap());
            assert_eq!(
                value["identity"]["executable"],
                Path::new("/bin/sleep").canonicalize().unwrap().to_str().unwrap()
            );
            drop(owner);
            for path in &observation.lease_paths {
                assert!(released(path));
                assert!(debt(path, &f.namespace.join("adopted")).unwrap());
            }
            f.child.0.kill().unwrap();
            f.child.0.wait().unwrap();
            assert!(!debt(&observation.lease_paths[0], &f.namespace.join("adopted")).unwrap());
            assert!(!record.exists());
        }
    );
}

#[test]
fn exact_full_original_worktree_and_slot_locks_are_held_at_publication() {
    isolated!(exact_full_original_worktree_and_slot_locks_are_held_at_publication, {
        let f = Fixture::new();
        let root = f.root.clone();
        let namespace = f.namespace.clone();
        let _hook = Hook::install(move |stage, _| {
            if stage == PublishStage::BeforeLink {
                for path in [
                    root.join("worktree.lock"),
                    namespace.join("slot-0"),
                    namespace.join("admission.lock"),
                ] {
                    assert!(!try_exclusive(&File::open(path).unwrap()).unwrap());
                }
            }
            Ok(())
        });
        registered(&mut f.adoption(false));
    });
}

#[test]
fn repeat_registration_preserves_one_original_record_even_with_an_older_waiter() {
    isolated!(repeat_registration_preserves_one_original_record_even_with_an_older_waiter, {
        let f = Fixture::new();
        registered(&mut f.adoption(false));
        let path = f.records().pop().unwrap();
        let bytes = fs::read(&path).unwrap();
        let inode = fs::metadata(&path).unwrap().ino();
        let mut older =
            Ticket::open(&f.namespace, Requirements::new(None, 2, 1, false, 0).unwrap()).unwrap();
        assert!(matches!(
            older.attempt(Some(0), |_| Ok(true), |_, _| Ok(true), |_| Ok(None::<()>)).unwrap(),
            Attempt::Waiting(_)
        ));
        assert!(matches!(outcome(&mut f.adoption(false)), AdoptionOutcome::AlreadyRegistered(_)));
        assert_eq!(f.records().as_slice(), std::slice::from_ref(&path));
        assert_eq!(fs::read(&path).unwrap(), bytes);
        assert_eq!(fs::metadata(path).unwrap().ino(), inode);
        assert!(f.adoption(true).attempt().is_err(), "a shared record cannot be upgraded");
    });
}

#[test]
fn shared_debt_leaves_another_real_slot_admissible_but_blocks_exclusive() {
    isolated!(shared_debt_leaves_another_real_slot_admissible_but_blocks_exclusive, {
        let f = Fixture::new();
        registered(&mut f.adoption(false));
        let mut other = Coordinator::open(
            &f.namespace,
            &f.namespace.join("adopted"),
            Requirements::new(None, 2, 1, false, 0).unwrap(),
        )
        .unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        let reservation = loop {
            match other.attempt(Some(0), 1).unwrap() {
                Attempt::Admitted(reservation) => break reservation,
                Attempt::Waiting(_) => {
                    assert!(Instant::now() < deadline);
                    std::thread::sleep(Duration::from_millis(1));
                }
            }
        };
        assert_eq!(reservation.slots[0].name, "slot-1");
        assert!(debt(&f.namespace.join("slot-0"), &f.namespace.join("adopted")).unwrap());
        assert!(!try_exclusive(&File::open(f.namespace.join("slot-1")).unwrap()).unwrap());
    });
}

#[test]
fn exclusive_registration_covers_all_actual_historical_slots() {
    isolated!(exclusive_registration_covers_all_actual_historical_slots, {
        let f = Fixture::new();
        crate::launcher_file::write(&f.namespace.join("slot-7"), &[]);
        let observation = registered(&mut f.adoption(true));
        assert_eq!(observation.lease_paths.len(), 4);
        assert!(observation.lease_paths.contains(&f.namespace.join("slot-7")));
        for path in &observation.lease_paths {
            assert!(debt(path, &f.namespace.join("adopted")).unwrap());
        }
    });
}

#[test]
fn earlier_eligible_ticket_keeps_priority_over_new_registration() {
    isolated!(earlier_eligible_ticket_keeps_priority_over_new_registration, {
        let f = Fixture::new();
        let mut older =
            Ticket::open(&f.namespace, Requirements::new(None, 2, 1, false, 0).unwrap()).unwrap();
        older.attempt(Some(0), |_| Ok(true), |_, _| Ok(true), |_| Ok(None::<()>)).unwrap();
        let mut adoption = f.adoption(false);
        assert!(matches!(
            adoption.attempt().unwrap(),
            Attempt::Waiting(super::super::super::Waiting::EarlierEligible { .. })
        ));
        assert!(f.records().is_empty());
        drop(older);
        registered(&mut adoption);
    });
}

#[test]
fn known_prepublication_failure_removes_only_its_unpublished_temporary() {
    isolated!(known_prepublication_failure_removes_only_its_unpublished_temporary, {
        let f = Fixture::new();
        let mut adoption = f.adoption(false);
        let _hook = Hook::install(|stage, _| {
            if stage == PublishStage::BeforeLink {
                Err(io::Error::from_raw_os_error(libc::ENOSPC))
            } else {
                Ok(())
            }
        });
        let error = adoption.attempt().unwrap_err();
        assert_eq!(error.publication(), Publication::NotPublished);
        assert!(f.records().is_empty());
        assert!(
            fs::read_dir(f.namespace.join("adopted")).unwrap().all(|entry| !entry
                .unwrap()
                .file_name()
                .as_bytes()
                .starts_with(b".pending-"))
        );
        assert!(released(&f.namespace.join("slot-0")));
    });
}

#[test]
fn postpublication_error_keeps_debt_and_original_attempt_permanently_poisoned() {
    isolated!(postpublication_error_keeps_debt_and_original_attempt_permanently_poisoned, {
        let f = Fixture::new();
        let mut adoption = f.adoption(false);
        let hook = Hook::install(|stage, _| {
            if stage == PublishStage::AfterPublish {
                Err(io::Error::from_raw_os_error(libc::EIO))
            } else {
                Ok(())
            }
        });
        let error = adoption.attempt().unwrap_err();
        assert_eq!(error.publication(), Publication::Unknown);
        drop(hook);
        assert_eq!(adoption.attempt().unwrap_err().publication(), Publication::Unknown);
        assert_eq!(f.records().len(), 1);
        assert!(debt(&f.namespace.join("slot-0"), &f.namespace.join("adopted")).unwrap());
        assert!(matches!(outcome(&mut f.adoption(false)), AdoptionOutcome::AlreadyRegistered(_)));
    });
}

#[test]
fn interrupted_two_link_publication_remains_unknown_without_automatic_repair() {
    isolated!(interrupted_two_link_publication_remains_unknown_without_automatic_repair, {
        let f = Fixture::new();
        let mut adoption = f.adoption(false);
        let hook = Hook::install(|stage, _| {
            if stage == PublishStage::AfterLink {
                Err(io::Error::from_raw_os_error(libc::EIO))
            } else {
                Ok(())
            }
        });
        assert_eq!(adoption.attempt().unwrap_err().publication(), Publication::Unknown);
        drop(hook);
        let path = f.records().pop().unwrap();
        assert_eq!(fs::metadata(&path).unwrap().nlink(), 2);
        assert!(released(&f.namespace.join("slot-0")));
        assert!(debt(&f.namespace.join("slot-0"), &f.namespace.join("adopted")).is_err());
        let before = fs::read(&path).unwrap();
        assert!(f.adoption(false).attempt().is_err());
        assert_eq!(fs::read(&path).unwrap(), before);
        assert_eq!(fs::metadata(&path).unwrap().nlink(), 2);
    });
}

#[test]
fn unwound_publication_cannot_resume_the_original_attempt() {
    isolated!(unwound_publication_cannot_resume_the_original_attempt, {
        let f = Fixture::new();
        let mut adoption = f.adoption(false);
        let hook = Hook::install(|stage, _| {
            assert!(stage != PublishStage::AfterLink, "actual post-link unwind control");
            Ok(())
        });
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| adoption.attempt())).is_err()
        );
        drop(hook);
        assert_eq!(adoption.attempt().unwrap_err().publication(), Publication::Unknown);
        assert_eq!(f.records().len(), 1);
    });
}

#[test]
fn pid_working_directory_and_exited_identity_refuse_without_publication() {
    isolated!(pid_working_directory_and_exited_identity_refuse_without_publication, {
        let mut f = Fixture::new();
        let cwd = Directory::open(&f.root).unwrap();
        for pid in [0, u32::MAX, 1] {
            assert!(identity::checked(pid, &cwd).is_err());
        }
        let other = f.root.join("other");
        crate::owner_only::create_dir(&other);
        assert!(identity::checked(f.child.0.id(), &Directory::open(&other).unwrap()).is_err());
        let mut adoption = f.adoption(false);
        f.child.0.kill().unwrap();
        f.child.0.wait().unwrap();
        assert_eq!(adoption.attempt().unwrap_err().publication(), Publication::NotPublished);
        assert!(f.records().is_empty());
    });
}

#[test]
fn malformed_or_future_prior_record_is_not_overwritten_by_new_publication() {
    isolated!(malformed_or_future_prior_record_is_not_overwritten_by_new_publication, {
        let f = Fixture::new();
        let mut adoption = f.adoption(false);
        let registry = Registry::open(&adoption.coordinator.directory).unwrap();
        let path = registry.directory.path.join("future.json");
        crate::owner_only::write(&path, br#"{"schema":200}"#);
        let inode = fs::metadata(&path).unwrap().ino();
        assert_eq!(adoption.attempt().unwrap_err().publication(), Publication::NotPublished);
        assert_eq!(fs::read(&path).unwrap(), br#"{"schema":200}"#);
        assert_eq!(fs::metadata(path).unwrap().ino(), inode);
    });
}

#[test]
fn actual_publication_survives_adopter_process_exit_without_destructors() {
    isolated!(actual_publication_survives_adopter_process_exit_without_destructors, {
        const ROOT: &str = "TRUST_ADOPTION_CRASH_ROOT";
        if let Some(root) = std::env::var_os(ROOT) {
            let root = fs::canonicalize(root).unwrap();
            let namespace = root.join("legacy");
            let pid = std::env::var("TRUST_ADOPTION_TARGET_PID").unwrap().parse().unwrap();
            let cwd = Directory::open(&root).unwrap();
            let identity = identity::checked(pid, &cwd).unwrap();
            let required =
                Requirements::new(Some(root.join("worktree.lock")), 2, 1, true, 1).unwrap();
            let coordinator =
                Coordinator::open(&namespace, &namespace.join("adopted"), required).unwrap();
            let pool = Pool::open_existing(&root.join("capacity")).unwrap().unwrap();
            let mut adoption = Adoption {
                coordinator,
                cwd,
                identity,
                pool,
                publication_started: false,
                poisoned: false,
            };
            let _hook = Hook::install(|stage, _| {
                if stage == PublishStage::AfterPublish {
                    std::process::exit(91);
                }
                Ok(())
            });
            outcome(&mut adoption);
            panic!("actual exit hook did not run");
        }
        let mut f = Fixture::new();
        let output = Command::new(std::env::current_exe().unwrap()).args(["--exact", "admission::resources::adoption::tests::actual_publication_survives_adopter_process_exit_without_destructors", "--nocapture"]).env(ROOT, &f.root).env("TRUST_ADOPTION_TARGET_PID", f.child.0.id().to_string()).current_dir(&f.root).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(91),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let record = f.records().pop().unwrap();
        let bytes = fs::read(&record).unwrap();
        assert_eq!(fs::metadata(&record).unwrap().nlink(), 1);
        for name in ["slot-0", "slot-1"] {
            let path = f.namespace.join(name);
            assert!(released(&path));
            assert!(debt(&path, &f.namespace.join("adopted")).unwrap());
        }
        assert_eq!(fs::read(&record).unwrap(), bytes);
        f.child.0.kill().unwrap();
        f.child.0.wait().unwrap();
        assert!(!debt(&f.namespace.join("slot-0"), &f.namespace.join("adopted")).unwrap());
        assert!(!record.exists());
    });
}
