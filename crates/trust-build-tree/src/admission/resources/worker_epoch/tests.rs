use super::*;

struct World {
    root: tempfile::TempDir,
    legacy: PathBuf,
    adopted: PathBuf,
}

impl World {
    fn new() -> Self {
        let root = crate::owner_only::tempdir();
        let legacy = root.path().join("legacy");
        let adopted = root.path().join("adopted");
        // A namespace an older scripts/build-slot made with `os.makedirs(DIR)`,
        // 0755 under the usual umask 022, which the current one never changes,
        // and the adoption registry, 0700 from either.
        crate::launcher_file::create_dir(&legacy);
        crate::owner_only::create_dir(&adopted);
        Self { root, legacy, adopted }
    }

    fn worker(&self, worktree: Option<PathBuf>) -> WorkerEpochAdmission {
        WorkerEpochAdmission::open(&self.legacy, &self.adopted, worktree, 2, 16).unwrap()
    }

    fn lock(&self, name: &str, shared: bool) -> Option<HeldLease> {
        lease(&self.legacy.join(name), shared, &self.adopted).unwrap()
    }
}

fn admitted(request: &mut WorkerEpochAdmission) -> WorkerEpoch {
    match request.attempt(Some(16)).unwrap() {
        Attempt::Admitted(epoch) => epoch,
        Attempt::Waiting(reason) => panic!("worker epoch still waiting: {reason:?}"),
    }
}

#[test]
fn world_keeps_its_stated_modes_and_admits_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::resources::worker_epoch::tests::world_keeps_its_stated_modes_and_admits_under_a_group_writable_umask",
        || {
            use std::os::unix::fs::PermissionsExt as _;
            let world = World::new();
            // A worktree lease opens its parent, the root, as an admission directory.
            for (directory, mode) in
                [(world.root.path(), 0o700), (&world.legacy, 0o755), (&world.adopted, 0o700)]
            {
                assert_eq!(fs::metadata(directory).unwrap().permissions().mode() & 0o777, mode);
            }
            let worktree = world.root.path().join("worktree");
            let epoch = admitted(&mut world.worker(Some(worktree.clone())));
            assert!(lease(&worktree, false, &world.adopted).unwrap().is_none());
            drop(epoch);
            assert!(world.lock("admission.lock", false).is_some());
        },
    );
}

// The worker epoch's worktree-lease parent as git makes it under umask 002,
// 0775, and its namespace as an older scripts/build-slot made it there with
// os.makedirs, 0775 too, which the current one never changes. Each is refused
// by its mode until the `chmod go-w` it names, pasted into a shell, also when
// the path has a space and a single quote.
#[test]
fn namespace_and_git_dir_made_under_umask_002_are_refused_by_mode_until_chmod_go_w() {
    crate::owner_only::under_umask_002(
        "admission::resources::worker_epoch::tests::namespace_and_git_dir_made_under_umask_002_are_refused_by_mode_until_chmod_go_w",
        || {
            use super::super::tests::{quoted_chmod_go_w, refused_by_mode, run_named_chmod_go_w};
            for parent in ["checkout", "it's a checkout"] {
                let needs_quotes = parent.contains('\'');
                let root = crate::owner_only::tempdir();
                let parent = root.path().join(parent);
                let legacy = parent.join("cache/build-slot");
                fs::create_dir_all(&legacy).unwrap();
                let adopted = legacy.join("adopted");
                crate::owner_only::create_dir(&adopted);
                let git = parent.join(".git");
                fs::create_dir(&git).unwrap();
                let worktree = git.join("build-slot.lock");
                let open =
                    || WorkerEpochAdmission::open(&legacy, &adopted, Some(worktree.clone()), 2, 16);
                let error = open().err().unwrap();
                refused_by_mode(&error, &legacy);
                if needs_quotes {
                    assert!(error.to_string().contains(&quoted_chmod_go_w(&legacy)), "{error}");
                }
                run_named_chmod_go_w(&error, &legacy);
                let mut worker = open().unwrap();
                let error = worker.attempt(Some(16)).err().unwrap();
                refused_by_mode(&error, &git);
                if needs_quotes {
                    assert!(error.to_string().contains(&quoted_chmod_go_w(&git)), "{error}");
                }
                run_named_chmod_go_w(&error, &git);
                let epoch = admitted(&mut worker);
                assert!(lease(&worktree, false, &adopted).unwrap().is_none());
                drop(epoch);
                assert!(lease(&legacy.join("admission.lock"), false, &adopted).unwrap().is_some());
            }
        },
    );
}

#[test]
fn compatible_workers_share_original_fence_and_exclude_historical_fixed_slots() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::worker_epoch::tests::compatible_workers_share_original_fence_and_exclude_historical_fixed_slots",
        || {
            let world = World::new();
            drop(world.lock("slot-19", false).unwrap());
            let worktree = world.root.path().join("one-worktree");
            let first = admitted(&mut world.worker(Some(worktree.clone())));
            let second = admitted(&mut world.worker(None));
            assert!(lease(&worktree, false, &world.adopted).unwrap().is_none());
            for name in ["admission.lock", "slot-0", "slot-1", "slot-19"] {
                assert!(world.lock(name, false).is_none());
            }
            drop(first);
            assert!(lease(&worktree, false, &world.adopted).unwrap().is_some());
            assert!(world.lock("slot-19", false).is_none());
            drop(second);
            assert!(world.lock("slot-19", false).is_some());
            assert!(world.lock("admission.lock", false).is_some());
        },
    );
}

#[test]
fn later_compatible_join_does_not_extend_an_epoch_past_older_fixed_work() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::worker_epoch::tests::later_compatible_join_does_not_extend_an_epoch_past_older_fixed_work",
        || {
            let world = World::new();
            let first = admitted(&mut world.worker(None));
            let mut fixed = Coordinator::open(
                &world.legacy,
                &world.adopted,
                Requirements::new(None, 2, 1, false, 1).unwrap(),
            )
            .unwrap();
            assert!(matches!(
                fixed.attempt(Some(16), 1).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            let mut later = world.worker(None);
            assert!(matches!(
                later.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::EarlierEligible { .. })
            ));
            drop(first);
            let Attempt::Admitted(fixed) = fixed.attempt(Some(16), 1).unwrap() else {
                panic!("earlier fixed request should now own actual capacity");
            };
            assert!(matches!(
                later.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            drop(fixed);
            admitted(&mut later).check_current().unwrap();
        },
    );
}

#[test]
fn dormant_legacy_arrival_retains_priority_when_its_ticket_becomes_live() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::worker_epoch::tests::dormant_legacy_arrival_retains_priority_when_its_ticket_becomes_live",
        || {
            let world = World::new();
            let mut worker = world.worker(None);
            let queue = world.legacy.join("admission");
            crate::owner_only::write(&queue.join("sequence"), b"19");
            let barrier = world.lock("admission.lock", false).unwrap();
            assert!(matches!(
                worker.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            // A legacy caller now installs the original arrival it reserved before
            // the worker arrived. Its open ticket, not sequence text, blocks work.
            let directory = Directory::open(&queue).unwrap();
            let registry = directory.open_file("registry.lock", true).unwrap();
            registry.try_lock().unwrap();
            let mut ticket = directory.create_file("wait-19", true, true).unwrap();
            ticket.try_lock().unwrap();
            ticket
            .write_all(
                br#"{"requires":{"worktree":null,"slots":2,"needed":1,"exclusive":false,"memory":0}}"#,
            )
            .unwrap();
            drop(registry);
            drop(barrier);
            assert!(matches!(
                worker.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::EarlierEligible { ticket: 19 })
            ));
            drop(ticket);
            admitted(&mut worker).check_current().unwrap();
        },
    );
}

#[test]
fn legacy_drain_downgrades_the_same_original_description() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::worker_epoch::tests::legacy_drain_downgrades_the_same_original_description",
        || {
            let world = World::new();
            // The oldest protocol can leave a slot held without admission.lock.
            let older = world.lock("slot-9", false).unwrap();
            let mut request = world.worker(None);
            assert!(matches!(
                request.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            assert!(world.lock("admission.lock", true).is_none());
            assert!(world.lock("slot-0", false).is_some());
            let same_open_description =
                request.draining.as_ref().unwrap().barrier.file.try_clone().unwrap();
            drop(older);
            let epoch = admitted(&mut request);
            assert!(world.lock("admission.lock", true).is_some());
            assert!(world.lock("admission.lock", false).is_none());
            assert!(world.lock("slot-9", false).is_none());
            drop(epoch);
            // If conversion reopened the path, the saved duplicate would still be
            // exclusive. If it unlocked instead, this probe would acquire EX.
            assert!(world.lock("admission.lock", true).is_some());
            assert!(world.lock("admission.lock", false).is_none());
            drop(same_open_description);
            assert!(world.lock("admission.lock", false).is_some());
        },
    );
}

#[test]
fn lost_memory_releases_unlaunched_barrier_and_rejoins_behind_eligible_fixed_work() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::worker_epoch::tests::lost_memory_releases_unlaunched_barrier_and_rejoins_behind_eligible_fixed_work",
        || {
            let world = World::new();
            let worktree = world.root.path().join("worktree");
            let historical = world.lock("slot-9", false).unwrap();
            let mut worker = world.worker(Some(worktree.clone()));
            assert!(matches!(
                worker.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            assert!(world.lock("admission.lock", true).is_none());
            assert!(lease(&worktree, false, &world.adopted).unwrap().is_none());
            let mut fixed = Coordinator::open(
                &world.legacy,
                &world.adopted,
                Requirements::new(None, 2, 1, false, 1).unwrap(),
            )
            .unwrap();
            assert!(matches!(
                fixed.attempt(Some(16), 1).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            assert!(matches!(
                worker.attempt(Some(15)).unwrap(),
                Attempt::Waiting(Waiting::MemoryUnavailable)
            ));
            assert!(world.lock("admission.lock", false).is_some());
            assert!(lease(&worktree, false, &world.adopted).unwrap().is_some());
            assert!(world.lock("slot-9", false).is_none());
            drop(historical);
            assert!(matches!(
                worker.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::EarlierEligible { .. })
            ));
            let Attempt::Admitted(fixed) = fixed.attempt(Some(16), 1).unwrap() else {
                panic!("earlier fixed request should now own actual capacity");
            };
            assert!(matches!(
                worker.attempt(Some(16)).unwrap(),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            drop(fixed);
            admitted(&mut worker).check_current().unwrap();
        },
    );
}

#[test]
fn new_wider_slot_view_invalidates_the_prelaunch_fence() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::worker_epoch::tests::new_wider_slot_view_invalidates_the_prelaunch_fence",
        || {
            let world = World::new();
            let epoch = admitted(&mut world.worker(None));
            epoch.check_current().unwrap();
            let wider = world.lock("slot-8", false).unwrap();
            assert_eq!(epoch.check_current().unwrap_err().kind(), io::ErrorKind::InvalidData);
            assert!(world.lock("slot-0", false).is_none());
            assert!(world.lock("slot-8", false).is_none());
            drop(epoch);
            assert!(world.lock("slot-0", false).is_some());
            assert!(world.lock("slot-8", false).is_none());
            drop(wider);
        },
    );
}
