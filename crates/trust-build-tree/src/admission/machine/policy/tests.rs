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
    assert!(missing.to_string().contains("original native CPU pool is absent"));
    assert!(missing.to_string().contains("resource status --json"));
    assert!(!capacity.exists());
    assert_eq!(fs::read_dir(&namespace).unwrap().count(), 1);

    private_dir.create(&capacity).unwrap();
    let pool_directory = capacity.join(trust_build_cpu::DIRECTORY_NAME);
    private_dir.create(&pool_directory).unwrap();
    for (mode, kind) in [(0o700, io::ErrorKind::NotFound), (0o755, io::ErrorKind::PermissionDenied)]
    {
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
    FixedCommandAdmission { coordinator, pool, request }
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
    let mut request = open(root.path(), pool, "worktree.lock", FixedCpuRequest::Automatic, false);
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
    let mut request = open(root.path(), pool, "worktree.lock", FixedCpuRequest::Automatic, false);
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
    let mut request = open(root.path(), pool, "worktree.lock", FixedCpuRequest::Limit(n(3)), false);
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

#[test]
fn exclusive_automatic_budget_uses_original_cpu_width_despite_historic_extra_slots() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), n(8)).unwrap();
    crate::launcher_file::write(&root.path().join("slot-9"), &[]);
    let mut request = open(root.path(), pool, "worktree.lock", FixedCpuRequest::Automatic, true);
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
