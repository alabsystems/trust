use super::*;
use crate::admission::Waiting;

fn n(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).unwrap()
}

#[test]
fn unavailable_original_pool_refuses_before_opening_the_queue() {
    use std::os::unix::fs::{DirBuilderExt as _, PermissionsExt as _};

    let root = crate::owner_only::tempdir();
    let capacity = root.path().join("capacity");
    let namespace = root.path().join("legacy");
    let adopted = namespace.join("adopted");
    let mut private_dir = fs::DirBuilder::new();
    private_dir.mode(0o700);
    private_dir.create(&namespace).unwrap();
    private_dir.create(&adopted).unwrap();
    let open = || {
        FixedCommandAdmission::open_existing(
            &capacity,
            None,
            None,
            false,
            FixedCpuRequest::Automatic,
            NonZeroU64::new(100).unwrap(),
            |required| Coordinator::open(&namespace, &adopted, required),
        )
    };
    let missing = open().err().expect("missing pool must refuse");
    assert_eq!(missing.kind(), io::ErrorKind::NotFound);
    assert!(missing
        .to_string()
        .contains("original native CPU pool is absent"));
    assert!(missing.to_string().contains("resource status --json"));
    assert!(!capacity.exists());
    assert_eq!(fs::read_dir(&namespace).unwrap().count(), 1);

    private_dir.create(&capacity).unwrap();
    let pool_directory = capacity.join(trust_build_cpu::DIRECTORY_NAME);
    private_dir.create(&pool_directory).unwrap();
    for (mode, kind) in [
        (0o700, io::ErrorKind::NotFound),
        (0o755, io::ErrorKind::PermissionDenied),
    ] {
        fs::set_permissions(&pool_directory, fs::Permissions::from_mode(mode)).unwrap();
        let backing = Pool::open_existing(&capacity).expect_err("invalid backing must refuse");
        let error = open().err().expect("invalid pool must refuse");
        assert_eq!(backing.kind(), kind);
        assert_eq!(error.kind(), kind);
        assert_eq!(error.raw_os_error(), backing.raw_os_error());
        assert_eq!(error.to_string(), backing.to_string());
        assert_eq!(fs::read_dir(&namespace).unwrap().count(), 1);
    }
}

fn open(
    root: &Path,
    pool: Pool,
    worktree: &str,
    request: FixedCpuRequest,
    exclusive: bool,
) -> FixedCommandAdmission {
    let required = requirements(
        Some(root.join(worktree)),
        4,
        exclusive,
        request,
        NonZeroU64::new(100).unwrap(),
        pool.slots(),
    )
    .unwrap();
    let coordinator = Coordinator::open(root, &root.join("adopted"), required).unwrap();
    let cpus = pool.slots();
    FixedCommandAdmission {
        coordinator,
        pool: Some(pool),
        cpus,
        request,
        check_lifecycle: |_| Ok(()),
    }
}

fn admitted(request: &mut FixedCommandAdmission, memory: u64) -> FixedClaim {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        match request.attempt_observed(Some(memory)).unwrap() {
            Attempt::Admitted(claim) => return claim,
            Attempt::Waiting(Waiting::RegistryBusy) if std::time::Instant::now() < deadline => {
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            Attempt::Waiting(reason) => panic!("actual admission refused: {reason:?}"),
        }
    }
}

#[test]
fn command_admission_fence_lives_until_actual_exec_then_cpu_claim_stays_held() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(8)).unwrap();
    let mut request = open(root.path(), pool, "command.lock", FixedCpuRequest::Limit(n(1)), false);
    let claim = admitted(&mut request, 1000);
    let fence =
        OpenOptions::new().read(true).write(true).open(root.path().join("admission.lock")).unwrap();
    assert!(!try_exclusive(&fence).unwrap(), "later exclusive waiter entered before preparation");
    let slot = claim.reservation.slots[0].path();
    let prepared = claim.prepare_command(std::process::Command::new("/usr/bin/true")).unwrap();
    assert!(!try_exclusive(&fence).unwrap(), "later exclusive waiter entered before exec");
    let mut running = super::super::handoff::spawn_fixture(prepared).unwrap();
    assert!(try_exclusive(&fence).unwrap(), "completed exec retained prelaunch exclusion");
    assert!(
        !crate::admission::resources::tests::released(&slot),
        "exec released actual CPU ownership"
    );
    fence.unlock().unwrap();
    assert!(running.wait().unwrap().success());
}

#[test]
fn failed_command_exec_releases_unlaunched_fence_and_original_cpu_claim() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(8)).unwrap();
    let mut request = open(root.path(), pool, "failed.lock", FixedCpuRequest::Limit(n(1)), false);
    let claim = admitted(&mut request, 1000);
    let slot = claim.reservation.slots[0].path();
    let mut command = std::process::Command::new(root.path().join("absent-payload"));
    command.stdout(std::process::Stdio::null());
    let prepared = claim.prepare_command(command).unwrap();
    let error =
        super::super::handoff::spawn_fixture(prepared).err().expect("absent executable ran");
    assert_eq!(error.kind(), io::ErrorKind::NotFound);
    let fence =
        OpenOptions::new().read(true).write(true).open(root.path().join("admission.lock")).unwrap();
    assert!(try_exclusive(&fence).unwrap());
    assert!(crate::admission::resources::tests::released(&slot));
}

#[test]
fn automatic_budget_counts_only_actual_idle_leases_after_another_command_claim() {
    // The second admission and the final observation each take the pool's
    // transaction just after the one before released it, which another
    // test's spawn can still hold in the shared process.
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::machine::policy::tests::automatic_budget_counts_only_actual_idle_leases_after_another_command_claim",
        || {
            let root = crate::owner_only::tempdir();
            let native = crate::owner_only::tempdir();
            let pool = Pool::open_in(native.path(), n(8)).unwrap();
            let mut first =
                open(root.path(), pool.clone(), "first.lock", FixedCpuRequest::Limit(n(2)), false);
            let first = admitted(&mut first, 1000);
            let mut second =
                open(root.path(), pool.clone(), "second.lock", FixedCpuRequest::Automatic, false);
            let second = admitted(&mut second, 1000);
            assert_eq!(first.reservation.held_slot_count(), 1);
            assert_eq!(first.budget(), n(2));
            assert_eq!(second.reservation.held_slot_count(), 3);
            assert_eq!(second.budget(), n(6));
            assert_eq!(
                second.observe_in_pool(&pool).unwrap(),
                LegacyFixedRoom::Fits { native_held: 0, external_reserved: 8, capacity: 8 }
            );
        },
    );
}

#[test]
fn automatic_borrowing_requires_measured_memory_for_each_additional_share() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(8)).unwrap();
    let mut request = open(
        root.path(),
        pool,
        "worktree.lock",
        FixedCpuRequest::Automatic,
        false,
    );
    let claim = admitted(&mut request, 250);
    assert_eq!(claim.reservation.held_slot_count(), 2);
    assert_eq!(claim.budget(), n(4));
    let unused = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(root.path().join("slot-2"))
        .unwrap();
    assert!(try_exclusive(&unused).unwrap());
}

#[test]
fn unknown_or_insufficient_memory_keeps_the_ticket_without_a_resource_claim() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(8)).unwrap();
    let mut request = open(
        root.path(),
        pool,
        "worktree.lock",
        FixedCpuRequest::Automatic,
        false,
    );
    for memory in [None, Some(99)] {
        assert!(matches!(
            request.attempt_observed(memory).unwrap(),
            Attempt::Waiting(Waiting::MemoryUnavailable)
        ));
        assert!(!root.path().join("worktree.lock").exists());
        assert!(!root.path().join("slot-0").exists());
    }
    let claim = admitted(&mut request, 100);
    assert_eq!(claim.reservation.held_slot_count(), 1);
    assert_eq!(claim.budget(), n(2));
}

#[test]
fn explicit_limit_reserves_fractional_shares_and_does_not_borrow_idle_ones() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(10)).unwrap();
    let mut request = open(
        root.path(),
        pool,
        "worktree.lock",
        FixedCpuRequest::Limit(n(3)),
        false,
    );
    let claim = admitted(&mut request, 1000);
    assert_eq!(claim.reservation.held_slot_count(), 2);
    assert_eq!(claim.budget(), n(3));
}

#[test]
fn cpu_limit_above_the_original_pool_refuses_before_queue_creation() {
    let root = crate::owner_only::tempdir();
    let error = requirements(
        Some(root.path().join("worktree.lock")),
        4,
        false,
        FixedCpuRequest::Limit(n(9)),
        NonZeroU64::new(100).unwrap(),
        n(8),
    )
    .unwrap_err();
    assert!(error.to_string().contains("original native pool width"));
    assert_eq!(fs::read_dir(root.path()).unwrap().count(), 0);
}

fn pending(root: &Path, cpus: NonZeroU32, slots: Option<NonZeroU32>) -> FixedCommandAdmission {
    let required = requirements(
        Some(root.join("fresh.lock")),
        canonical_slot_count(slots, cpus),
        false,
        FixedCpuRequest::Automatic,
        NonZeroU64::new(100).unwrap(),
        cpus,
    )
    .unwrap();
    FixedCommandAdmission {
        coordinator: Coordinator::open(root, &root.join("adopted"), required).unwrap(),
        pool: None,
        cpus,
        request: FixedCpuRequest::Automatic,
        check_lifecycle: |_| Ok(()),
    }
}

fn admitted_fresh(request: &mut FixedCommandAdmission, capacity: &Path) -> FixedClaim {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        match request
            .attempt_observed_with(Some(1000), |width| Pool::try_open_in(capacity, width))
            .unwrap()
        {
            Attempt::Admitted(claim) => return claim,
            Attempt::Waiting(Waiting::RegistryBusy | Waiting::NativeCpu(LegacyFixedRoom::Busy))
                if std::time::Instant::now() < deadline =>
            {
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            Attempt::Waiting(reason) => panic!("fresh original admission refused: {reason:?}"),
        }
    }
}

#[test]
fn fresh_backing_is_created_only_after_actual_legacy_reservation() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let capacity = native.path().join("capacity");
    let required = Requirements::new(None, 5, 5, false, 0).unwrap();
    let mut blocking =
        Coordinator::open(root.path(), &root.path().join("adopted"), required).unwrap();
    let held = match blocking.attempt(Some(1000), 5).unwrap() {
        Attempt::Admitted(held) => held,
        Attempt::Waiting(reason) => panic!("original slot actor refused: {reason:?}"),
    };
    let mut request = pending(root.path(), n(32), None);
    for memory in [None, Some(99)] {
        assert!(matches!(
            request
                .attempt_observed_with(memory, |width| { Pool::try_open_in(&capacity, width) })
                .unwrap(),
            Attempt::Waiting(Waiting::MemoryUnavailable)
        ));
        assert!(!capacity.exists());
    }
    assert!(matches!(
        request
            .attempt_observed_with(Some(1000), |width| { Pool::try_open_in(&capacity, width) })
            .unwrap(),
        Attempt::Waiting(_)
    ));
    assert!(!capacity.exists());
    drop(held);
    let claim = admitted_fresh(&mut request, &capacity);
    assert_eq!(
        Pool::open_existing(&capacity).unwrap().unwrap().slots(),
        n(32)
    );
    assert_eq!(claim.budget(), n(32));
    claim.check_current().unwrap();
}

#[test]
fn initializer_contention_releases_partial_resources_and_keeps_priority() {
    let root = crate::owner_only::tempdir();
    let mut request = pending(root.path(), n(32), None);
    assert!(matches!(
        request
            .attempt_observed_with(Some(1000), |_| { Err(io::ErrorKind::WouldBlock.into()) })
            .unwrap(),
        Attempt::Waiting(Waiting::NativeCpu(LegacyFixedRoom::Busy))
    ));
    for name in [
        "fresh.lock",
        "admission.lock",
        "slot-0",
        "slot-1",
        "slot-2",
        "slot-3",
        "slot-4",
    ] {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(root.path().join(name))
            .unwrap();
        assert!(try_exclusive(&file).unwrap(), "{name}");
    }
    let native = crate::owner_only::tempdir();
    let mut later = pending(root.path(), n(32), None);
    assert!(matches!(
        later
            .attempt_observed_with(Some(1000), |_| {
                panic!("later ticket cannot initialize ahead of the original waiter")
            })
            .unwrap(),
        Attempt::Waiting(_)
    ));
    let claim = admitted_fresh(&mut request, native.path());
    claim.check_current().unwrap();
}

#[test]
fn newly_created_backing_cannot_borrow_actual_held_native_credits() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let mut request = pending(root.path(), n(32), None);
    let mut held = Vec::new();
    let result = request
        .attempt_observed_with(Some(1000), |width| {
            let pool = Pool::try_open_in(native.path(), width)?;
            for _ in 0..width.get() {
                held.push(
                    pool.try_acquire(trust_build_cpu::Owner::current(None))?
                        .expect("isolated native credit must be available"),
                );
            }
            Ok(pool)
        })
        .unwrap();
    assert!(matches!(result, Attempt::Waiting(Waiting::NativeCpu(_))));
    assert_eq!(held.len(), 32);
    assert!(request.pool.is_some());
    drop(held);
    admitted_fresh(&mut request, native.path())
        .check_current()
        .unwrap();
}

#[test]
fn competing_initializer_cannot_replace_its_sealed_width() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let capacity = native.path().join("capacity");
    let mut request = pending(root.path(), n(32), None);
    let original = Pool::open_in(&capacity, n(16)).unwrap();
    let error = request
        .attempt_observed_with(Some(1000), |width| Pool::try_open_in(&capacity, width))
        .err()
        .expect("different original width must refuse");
    assert!(error.to_string().contains("CPU pool capacity differs"));
    assert_eq!(original.slots(), n(16));
    assert_eq!(
        Pool::open_existing(&capacity).unwrap().unwrap().slots(),
        n(16)
    );
}

#[test]
fn smaller_slot_option_cannot_borrow_the_other_original_claims_share() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::machine::policy::tests::smaller_slot_option_cannot_borrow_the_other_original_claims_share",
        || {
            let root = crate::owner_only::tempdir();
            let native = crate::owner_only::tempdir();
            let pool = Pool::open_in(native.path(), n(32)).unwrap();
            let required = requirements(Some(root.path().join("first.lock")), 5, false,
                FixedCpuRequest::Limit(n(24)), NonZeroU64::new(100).unwrap(), n(32)).unwrap();
            let mut first = FixedCommandAdmission {
                coordinator: Coordinator::open(root.path(), &root.path().join("adopted"), required).unwrap(),
                pool: Some(pool.clone()), cpus: n(32), request: FixedCpuRequest::Limit(n(24)),
                check_lifecycle: |_| Ok(()),
            };
            let first = admitted(&mut first, 1000);
            assert_eq!(first.reservation.held_slot_count(), 4);
            let mut second = pending(root.path(), n(32), Some(n(1)));
            second.pool = Some(pool.clone());
            let second = admitted(&mut second, 1000);
            assert_eq!(second.reservation.held_slot_count(), 1);
            assert_eq!(second.budget(), n(6));
            assert_eq!(second.observe_in_pool(&pool).unwrap(),
                LegacyFixedRoom::Fits { native_held: 0, external_reserved: 30, capacity: 32 });
        },
    );
}

#[test]
fn fresh_backing_does_not_grant_execution_over_original_one_slot_whole_machine_claim() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    // A real original one-slot legacy actor, not saved JSON counts.
    let required = Requirements::new(None, 1, 1, false, 0).unwrap();
    let mut actor = Coordinator::open(root.path(), &root.path().join("adopted"), required).unwrap();
    let held = match actor.attempt(Some(1000), 1).unwrap() {
        Attempt::Admitted(held) => held,
        Attempt::Waiting(reason) => panic!("original legacy actor refused: {reason:?}"),
    };
    let original = held.publish_fixed(n(32), n(32), FixedPublication::ExistingLease).unwrap();
    let mut request = pending(root.path(), n(32), Some(n(1)));
    assert!(matches!(
        request
            .attempt_observed_with(Some(1000), |width| {
                Pool::try_open_in(native.path(), width)
            })
            .unwrap(),
        Attempt::Waiting(Waiting::NativeCpu(_))
    ));
    original.check_current().unwrap();
    assert_eq!(original.budget(), n(32));
    assert!(request.pool.is_some()); // Backing exists; no new execution claim did.
}

#[test]
fn first_use_preserves_unknown_and_out_of_view_original_slot_refusals() {
    use std::os::unix::fs::OpenOptionsExt;
    for known_legacy in [false, true] {
        let root = crate::owner_only::tempdir();
        let native = crate::owner_only::tempdir();
        let mut held = OpenOptions::new()
            .create_new(true)
            .read(true)
            .write(true)
            .mode(0o600)
            .open(root.path().join("slot-9"))
            .unwrap();
        // These are untrusted diagnostic bytes. Only the actual flock makes
        // this original out-of-view slot a live competing actor.
        if known_legacy {
            held.write_all(
                serde_json::to_string(&serde_json::json!({
                    "pid":std::process::id(), "cmd":"original legacy actor",
                    "cwd":root.path(), "started":0
                }))
                .unwrap()
                .as_bytes(),
            )
            .unwrap();
        } else {
            held.write_all(b"unknown original live record").unwrap();
        }
        held.lock().unwrap();
        let mut request = pending(root.path(), n(32), Some(n(1)));
        let result = request
            .attempt_observed_with(Some(1000), |width| Pool::try_open_in(native.path(), width))
            .unwrap();
        let expected = if known_legacy {
            LegacyFixedRoom::OverCapacity {
                native_held: 0,
                external_reserved: 64,
                capacity: 32,
            }
        } else {
            LegacyFixedRoom::UnknownExternal
        };
        assert!(matches!(result, Attempt::Waiting(Waiting::NativeCpu(room)) if room == expected));
        assert!(request.pool.is_some());
        drop(held);
        admitted_fresh(&mut request, native.path())
            .check_current()
            .unwrap();
    }
}

#[test]
fn prepared_and_retired_states_never_initialize_legacy_backing() {
    use trust_build_cpu::NativeMigrationStatus::*;
    legacy_pool_state(NotStarted).unwrap();
    for state in [Prepared, AwaitingLaterBoot, ReadyToResume, Published] {
        assert_eq!(
            legacy_pool_state(state).unwrap_err().kind(),
            io::ErrorKind::PermissionDenied
        );
    }
}

#[test]
fn migration_seen_after_backing_creation_refuses_before_fixed_publication() {
    thread_local! { static PREPARED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
    fn check(_: &Reservation) -> io::Result<()> {
        legacy_pool_state(if PREPARED.with(|value| value.get()) {
            trust_build_cpu::NativeMigrationStatus::Prepared
        } else {
            trust_build_cpu::NativeMigrationStatus::NotStarted
        })
    }
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let mut request = pending(root.path(), n(32), None);
    request.check_lifecycle = check;
    PREPARED.with(|value| value.set(false));
    let error = request
        .attempt_observed_with(Some(1000), |width| {
            let pool = Pool::try_open_in(native.path(), width)?;
            PREPARED.with(|value| value.set(true));
            Ok(pool)
        })
        .err()
        .expect("prepared intent must refuse original publication");
    PREPARED.with(|value| value.set(false));
    assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
    assert!(Pool::open_existing(native.path()).unwrap().is_some());
    for index in 0..5 {
        assert!(fs::read(root.path().join(format!("slot-{index}")))
            .unwrap()
            .is_empty());
    }
}

#[test]
fn canonical_alias_retarget_refuses_before_initialization_and_before_publication() {
    use std::os::unix::fs::symlink;
    thread_local! {
        static CANONICAL: std::cell::RefCell<Option<PathBuf>> = const {
            std::cell::RefCell::new(None)
        };
    }
    fn check(reservation: &Reservation) -> io::Result<()> {
        CANONICAL.with(|path| {
            check_canonical_namespace(path.borrow().as_ref().unwrap(), &reservation.namespace)
        })
    }
    for before_creation in [true, false] {
        let root = crate::owner_only::tempdir();
        let original = root.path().join("original");
        let replacement = root.path().join("replacement");
        crate::owner_only::create_dir(&original);
        crate::owner_only::create_dir(&replacement);
        let canonical = root.path().join("canonical");
        symlink(&original, &canonical).unwrap();
        CANONICAL.with(|path| path.replace(Some(canonical.clone())));
        // Match Locations::current: the request retains the resolved physical
        // namespace, while the account locator remains a distinct logical path.
        let mut request = pending(&fs::canonicalize(&original).unwrap(), n(32), None);
        request.check_lifecycle = check;
        let native = crate::owner_only::tempdir();
        let capacity = native.path().join("capacity");
        if before_creation {
            fs::remove_file(&canonical).unwrap();
            symlink(&replacement, &canonical).unwrap();
        }
        let mut initialized = false;
        let error = request
            .attempt_observed_with(Some(1000), |width| {
                let pool = Pool::try_open_in(&capacity, width)?;
                initialized = true;
                fs::remove_file(&canonical)?;
                symlink(&replacement, &canonical)?;
                Ok(pool)
            })
            .err()
            .expect("retargeted canonical owner must refuse");
        CANONICAL.with(|path| path.replace(None));
        assert!(error.to_string().contains("custom coordination namespace"));
        assert_eq!(initialized, !before_creation);
        assert_eq!(capacity.exists(), !before_creation);
        // The physical original is still valid: its unchanged descriptors
        // alone must not publish a claim after canonical clients moved away.
        request.coordinator.directory.check().unwrap();
        for index in 0..5 {
            assert!(fs::read(original.join(format!("slot-{index}")))
                .unwrap()
                .is_empty());
        }
        assert_eq!(fs::read_dir(&replacement).unwrap().count(), 0);
    }
}

#[test]
fn custom_namespace_refuses_before_machine_owner_selection() {
    let canonical = crate::owner_only::tempdir();
    let custom = crate::owner_only::tempdir();
    assert!(check_canonical_namespace(canonical.path(), custom.path()).is_err());
    assert_eq!(fs::read_dir(custom.path()).unwrap().count(), 0);
    assert!(online_machine_width().is_ok_and(|width| width.get() <= trust_build_cpu::MAX_SLOTS));
}

#[test]
fn exclusive_automatic_budget_uses_original_cpu_width_despite_historic_extra_slots() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(8)).unwrap();
    crate::launcher_file::write(&root.path().join("slot-9"), &[]);
    let mut request = open(
        root.path(),
        pool,
        "worktree.lock",
        FixedCpuRequest::Automatic,
        true,
    );
    let claim = admitted(&mut request, 100);
    assert!(claim.reservation.is_exclusive());
    assert_eq!(claim.reservation.held_slot_count(), 5);
    assert_eq!(claim.budget(), n(8));
    assert_eq!(claim.record_pool_slots, 10);
    assert!(!root.path().join("slot-8").exists());
}

#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::resources::machine::policy::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            explicit_limit_reserves_fractional_shares_and_does_not_borrow_idle_ones();
            exclusive_automatic_budget_uses_original_cpu_width_despite_historic_extra_slots();
        },
    );
}
