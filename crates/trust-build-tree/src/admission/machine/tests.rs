use std::time::{Duration, Instant};

use super::*;
use crate::admission::{Coordinator, Requirements, Waiting};

fn width(n: u32) -> NonZeroU32 {
    NonZeroU32::new(n).unwrap()
}
fn reserve(root: &Path, exclusive: bool) -> Reservation {
    let mut coordinator = Coordinator::open(
        root,
        &root.join("adopted"),
        Requirements::new(Some(root.join("worktree.lock")), 4, 1, exclusive, 0).unwrap(),
    )
    .unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        match coordinator.attempt(Some(0), 1).unwrap() {
            Attempt::Admitted(reservation) => return reservation,
            Attempt::Waiting(Waiting::RegistryBusy) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(1))
            }
            Attempt::Waiting(reason) => panic!("real resource claim refused: {reason:?}"),
        }
    }
}

#[test]
fn fixed_publication_retains_slots_and_worktree_but_releases_only_shared_admission() {
    // Other parallel fixtures fork. Create these actual lock owners only in
    // an exact fresh actor so its immediate release assertions observe their
    // own complete FD lifetime, at the unchanged process limit.
    const ACTOR: &str = "TRUST_FIXED_PUBLICATION_FIXTURE_ACTOR";
    const NAME: &str = "admission::resources::machine::tests::fixed_publication_retains_slots_and_worktree_but_releases_only_shared_admission";
    const MARKER: &str = "fixed publication original-owner assertions completed";
    if std::env::var_os(ACTOR).as_deref() != Some(std::ffi::OsStr::new("1")) {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", NAME, "--nocapture"])
            .env(ACTOR, "1")
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while child.try_wait().unwrap().is_none() {
            if std::time::Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                panic!("actual fixed publication fixture actor timed out");
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stdout).contains(MARKER));
        return;
    }
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), width(8)).unwrap();
    let claim = reserve(root.path(), false).publish_fixed(width(8), width(2)).unwrap();
    claim.check_current().unwrap();
    assert_eq!(claim.budget(), width(2));
    let probe =
        OpenOptions::new().read(true).write(true).open(root.path().join("admission.lock")).unwrap();
    assert!(try_exclusive(&probe).unwrap());
    drop(probe);
    assert_eq!(
        claim.observe_in_pool(&pool).unwrap(),
        LegacyFixedRoom::Fits { native_held: 0, external_reserved: 2, capacity: 8 }
    );
    for name in ["slot-0", "worktree.lock"] {
        let file = OpenOptions::new().read(true).write(true).open(root.path().join(name)).unwrap();
        assert!(!try_exclusive(&file).unwrap());
    }
    drop(claim);
    let file = OpenOptions::new().read(true).write(true).open(root.path().join("slot-0")).unwrap();
    assert!(try_exclusive(&file).unwrap());
    println!("{MARKER}");
}

#[test]
fn fixed_budget_never_exceeds_the_actual_retained_share_or_original_manifest_width() {
    let root = crate::owner_only::tempdir();
    assert!(reserve(root.path(), false).publish_fixed(width(8), width(3)).is_err());
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), width(4)).unwrap();
    let claim = reserve(root.path(), false).publish_fixed(width(8), width(2)).unwrap();
    assert!(claim.observe_in_pool(&pool).is_err());
}

#[test]
fn exclusive_fixed_records_cover_historic_indices_without_creating_gap_slots() {
    let root = crate::owner_only::tempdir();
    let native = crate::owner_only::tempdir();
    let pool = Pool::open_in(native.path(), width(8)).unwrap();
    crate::launcher_file::write(&root.path().join("slot-9"), &[]);
    let mut reservation = reserve(root.path(), true);
    assert!(reservation.try_drain_exclusive().unwrap());
    let claim = reservation.publish_fixed(width(8), width(8)).unwrap();
    assert_eq!(claim.record_pool_slots, 10);
    assert_eq!(
        claim.observe_in_pool(&pool).unwrap(),
        LegacyFixedRoom::Fits { native_held: 0, external_reserved: 8, capacity: 8 }
    );
    assert!(!root.path().join("slot-8").exists());
    let foreign =
        OpenOptions::new().read(true).write(true).open(root.path().join("admission.lock")).unwrap();
    assert!(!try_exclusive(&foreign).unwrap());
}

#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::resources::machine::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            fixed_budget_never_exceeds_the_actual_retained_share_or_original_manifest_width();
            exclusive_fixed_records_cover_historic_indices_without_creating_gap_slots();
        },
    );
}

#[test]
fn changed_fixed_record_or_replaced_original_slot_refuses_readiness() {
    for replace in [false, true] {
        let root = crate::owner_only::tempdir();
        let native = crate::owner_only::tempdir();
        let pool = Pool::open_in(native.path(), width(8)).unwrap();
        let claim = reserve(root.path(), false).publish_fixed(width(8), width(2)).unwrap();
        let slot = root.path().join("slot-0");
        if replace {
            fs::rename(&slot, root.path().join("original-slot")).unwrap();
            crate::owner_only::write(&slot, &claim.record);
        } else {
            let mut row: serde_json::Value = serde_json::from_slice(&claim.record).unwrap();
            row["pid"] = serde_json::json!(0);
            fs::write(&slot, serde_json::to_vec(&row).unwrap()).unwrap();
        }
        assert!(claim.check_current().is_err());
        assert!(claim.observe_in_pool(&pool).is_err());
        drop(claim);
        assert!(slot.exists());
    }
}

fn fixed_coordinator(root: &Path, worktree: &str, slots: u32, exclusive: bool) -> Coordinator {
    Coordinator::open(
        root,
        &root.join("adopted"),
        Requirements::new(Some(root.join(worktree)), slots, 1, exclusive, 0).unwrap(),
    )
    .unwrap()
}

fn attempt_fixed(coordinator: &mut Coordinator, pool: &Pool) -> Attempt<FixedClaim> {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        match coordinator.attempt_fixed_in_pool(Some(0), 1, width(1), pool).unwrap() {
            Attempt::Waiting(Waiting::RegistryBusy) if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(1));
            }
            result => return result,
        }
    }
}

#[test]
fn cpu_refusal_preserves_ticket_and_releases_complete_partial_claim() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::machine::tests::cpu_refusal_preserves_ticket_and_releases_complete_partial_claim",
        || {
            let root = crate::owner_only::tempdir();
            let native = crate::owner_only::tempdir();
            let pool = Pool::open_in(native.path(), width(1)).unwrap();
            let lease = pool.try_acquire(trust_build_cpu::Owner::current(None)).unwrap().unwrap();
            let mut coordinator = fixed_coordinator(root.path(), "worktree.lock", 2, false);
            assert!(matches!(
                attempt_fixed(&mut coordinator, &pool),
                Attempt::Waiting(Waiting::NativeCpu(LegacyFixedRoom::OverCapacity {
                    native_held: 1,
                    external_reserved: 1,
                    capacity: 1,
                }))
            ));
            let original_ticket = coordinator.ticket.original.as_ref().unwrap().1.clone();
            assert!(coordinator.ticket.directory.path.join(&original_ticket).exists());
            for name in ["slot-0", "worktree.lock", "admission.lock"] {
                assert!(super::super::tests::released(&root.path().join(name)));
            }
            assert_eq!(
                pool.observe_legacy_fixed_room(root.path(), width(2), None).unwrap(),
                LegacyFixedRoom::Fits { native_held: 1, external_reserved: 0, capacity: 1 }
            );
            drop(lease);
            let claim = attempt_fixed(&mut coordinator, &pool).into_claim().unwrap();
            assert!(coordinator.ticket.original.is_none());
            assert!(!coordinator.ticket.directory.path.join(original_ticket).exists());
            claim.check_current().unwrap();
        },
    );
}

#[test]
fn excess_fixed_waiter_never_publishes_a_mutually_blocking_reservation() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::machine::tests::excess_fixed_waiter_never_publishes_a_mutually_blocking_reservation",
        || {
            let root = crate::owner_only::tempdir();
            let native = crate::owner_only::tempdir();
            let pool = Pool::open_in(native.path(), width(1)).unwrap();
            let mut first = fixed_coordinator(root.path(), "first.lock", 2, false);
            let mut second = fixed_coordinator(root.path(), "second.lock", 2, false);
            let first_claim = attempt_fixed(&mut first, &pool).into_claim().unwrap();
            assert!(matches!(
                attempt_fixed(&mut second, &pool),
                Attempt::Waiting(Waiting::NativeCpu(LegacyFixedRoom::OverCapacity {
                    native_held: 0,
                    external_reserved: 2,
                    capacity: 1,
                }))
            ));
            assert!(second.ticket.original.is_some());
            assert_eq!(
                first_claim.observe_in_pool(&pool).unwrap(),
                LegacyFixedRoom::Fits { native_held: 0, external_reserved: 1, capacity: 1 }
            );
            drop(first_claim);
            let second_claim = attempt_fixed(&mut second, &pool).into_claim().unwrap();
            second_claim.check_current().unwrap();
            assert!(second.ticket.original.is_none());
        },
    );
}

#[test]
fn native_manifest_contention_and_unknown_records_leave_no_resource_claim() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::machine::tests::native_manifest_contention_and_unknown_records_leave_no_resource_claim",
        || {
            let root = crate::owner_only::tempdir();
            let native = crate::owner_only::tempdir();
            let pool = Pool::open_in(native.path(), width(2)).unwrap();
            let mut coordinator = fixed_coordinator(root.path(), "worktree.lock", 2, false);
            let transaction = pool.try_legacy_fixed_transaction().unwrap().unwrap();
            assert!(matches!(
                attempt_fixed(&mut coordinator, &pool),
                Attempt::Waiting(Waiting::NativeCpu(LegacyFixedRoom::Busy))
            ));
            assert!(super::super::tests::released(&root.path().join("worktree.lock")));
            drop(transaction);
            use std::os::unix::fs::OpenOptionsExt as _;
            let unknown = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(root.path().join("slot-1"))
                .unwrap();
            unknown.try_lock().unwrap();
            assert!(matches!(
                attempt_fixed(&mut coordinator, &pool),
                Attempt::Waiting(Waiting::NativeCpu(LegacyFixedRoom::UnknownExternal))
            ));
            assert!(coordinator.ticket.original.is_some());
            assert!(super::super::tests::released(&root.path().join("slot-0")));
            drop(unknown);
            assert!(super::super::tests::released(&root.path().join("slot-1")));
            assert!(attempt_fixed(&mut coordinator, &pool).into_claim().is_some());
        },
    );
}

#[test]
fn exclusive_cpu_attempt_preserves_priority_without_retaining_partial_locks() {
    crate::trust_output_lock::tests::isolated_case(
        "admission::resources::machine::tests::exclusive_cpu_attempt_preserves_priority_without_retaining_partial_locks",
        || {
            let root = crate::owner_only::tempdir();
            let native = crate::owner_only::tempdir();
            let pool = Pool::open_in(native.path(), width(2)).unwrap();
            let mut exclusive = fixed_coordinator(root.path(), "exclusive.lock", 2, true);
            let mut later = fixed_coordinator(root.path(), "later.lock", 2, false);
            let old = lease(&root.path().join("slot-0"), false, &root.path().join("adopted"))
                .unwrap()
                .unwrap();
            assert!(matches!(
                attempt_fixed(&mut exclusive, &pool),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            assert!(exclusive.ticket.original.is_some());
            for name in ["exclusive.lock", "admission.lock"] {
                assert!(super::super::tests::released(&root.path().join(name)));
            }
            assert!(matches!(
                attempt_fixed(&mut later, &pool),
                Attempt::Waiting(Waiting::EarlierEligible { .. })
            ));
            drop(old);
            assert!(super::super::tests::released(&root.path().join("slot-0")));
            let claim = attempt_fixed(&mut exclusive, &pool).into_claim().unwrap();
            assert!(claim.reservation.is_exclusive());
            assert_eq!(claim.reservation.held_slot_count(), 2);
            assert!(exclusive.ticket.original.is_none());
            assert!(matches!(
                attempt_fixed(&mut later, &pool),
                Attempt::Waiting(Waiting::ResourcesBusy)
            ));
            drop(claim);
            assert!(super::super::tests::released(&root.path().join("admission.lock")));
            assert!(attempt_fixed(&mut later, &pool).into_claim().is_some());
        },
    );
}
