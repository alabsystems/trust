use std::os::unix::fs::PermissionsExt;
use std::sync::{Arc, Barrier};

use super::*;

pub(super) fn width(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).unwrap()
}
fn owner() -> Owner {
    Owner::current(Some(77))
}

pub(super) fn capacity_bank(root: &Path, debt: &ExternalDebt, name: &str) -> NativeCapacityBank {
    let store = root.join(name);
    std::fs::create_dir(&store).unwrap();
    std::fs::set_permissions(&store, std::fs::Permissions::from_mode(0o700)).unwrap();
    let mut prepared = debt
        .prepare_recoverable(owner(), width(4), [31; 32])
        .unwrap()
        .persist(&store.canonicalize().unwrap(), "original")
        .unwrap();
    debt.try_acquire_all_recoverable(&mut prepared).unwrap().unwrap().into_capacity_bank().unwrap()
}

#[test]
fn original_capacity_bank_loans_actual_units_without_discounting_shadow_records() {
    let Some((root, native, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank");
    assert_eq!(bank.width(), 4);
    let loans: Vec<_> = (0..4).map(|_| bank.try_loan().unwrap().unwrap()).collect();
    assert!(bank.try_loan().unwrap().is_none());
    assert!(bank.settle_drained().is_err());
    assert!(debt.try_acquire_native(owner(), 4).unwrap().is_none());
    assert_eq!(debt.reserved().unwrap(), 4);
    assert_eq!(
        native.snapshot().unwrap().iter().filter(|s| matches!(s, SlotState::Held { .. })).count(),
        4
    );
    for loan in loans {
        bank.return_unused(loan).unwrap();
    }
    let loan = bank.try_loan().unwrap().unwrap();
    let original = loan.original().try_clone().unwrap();
    let (_, loan) = bank.return_unused(loan).unwrap_err().into_parts();
    assert!(bank.settle_drained().is_err());
    drop(original);
    // SAFETY: only the same original descriptor was cloned for inspection;
    // it was never used by a child/thread or exported and is now closed.
    unsafe { bank.return_after_scope(loan) }.unwrap();
    bank.settle_drained().unwrap();
    assert!(bank.try_loan().is_err());
    assert_eq!(debt.reserved().unwrap(), 0);
    assert!(
        native.snapshot().unwrap().iter().all(|slot| matches!(slot, SlotState::Available { .. }))
    );
    assert!(
        debt.try_acquire_native(owner(), 4).unwrap().is_some(),
        "settled original bank returns BOTH native and shadow backing even while its retired owner is retained"
    );
}

#[test]
fn original_capacity_bank_refuses_foreign_returns_and_unknown_drop_keeps_debt() {
    let Some((root, _, debt)) = setup() else { return };
    let Some((other_root, _, other_debt)) = another_domain() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank");
    let mut other = capacity_bank(other_root.path(), &other_debt, "bank");
    let loan = bank.try_loan().unwrap().unwrap();
    let (_, loan) = other.return_unused(loan).unwrap_err().into_parts();
    bank.return_unused(loan).unwrap();
    let lost = bank.try_loan().unwrap().unwrap();
    drop(lost);
    assert!(bank.settle_drained().is_err());
    drop(bank);
    assert_eq!(debt.reserved().unwrap(), 4);
    assert!(debt.try_acquire_native(owner(), 4).unwrap().is_none());
    other.settle_drained().unwrap();
}

pub(super) fn unit_plan(
    root: &Path,
    debt: &ExternalDebt,
    leaf: &str,
    context: [u8; 32],
) -> crate::PreparedRecovery {
    std::fs::set_permissions(root, std::fs::Permissions::from_mode(0o700)).unwrap();
    debt.prepare_recoverable(owner(), width(1), context)
        .unwrap()
        .persist(&root.canonicalize().unwrap(), leaf)
        .unwrap()
}

#[test]
fn idle_pair_return_releases_real_machine_backing_without_refunding_lost_loans() {
    let Some((root, native, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank");
    let lost = bank.try_loan().unwrap().unwrap();
    let lost_slot = lost.slot();
    drop(lost); // No closure capability returned: this unit must stay charged.
    for expected in [3, 2, 1] {
        let returned = bank.release_idle(width(1)).unwrap().unwrap();
        assert_ne!(returned, lost_slot);
        assert_eq!(bank.funded_width(), expected);
        assert_eq!(debt.reserved().unwrap(), expected as u32);
        assert!(matches!(
            native.snapshot().unwrap()[returned as usize],
            SlotState::Available { .. }
        ));
    }
    assert_eq!(bank.width(), 4, "original ceiling is not a new balance");
    assert!(bank.release_idle(width(1)).unwrap().is_none());
    assert!(bank.try_loan().unwrap().is_none(), "released holes are not funded");
    assert!(bank.settle_drained().is_err(), "lost original loan excludes full settlement");
    let fresh = debt.try_acquire_native(owner(), 4).unwrap().unwrap();
    assert_ne!(fresh.slot(), lost_slot, "another genuine owner can acquire returned capacity");
    drop(fresh);
    drop(bank);
    assert_eq!(debt.reserved().unwrap(), 1, "owner loss keeps unknown borrower debt");
}

#[test]
fn scoped_pair_reacquisition_requires_real_room_and_retained_original_borrower() {
    let Some((root, _, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    assert!(bank.is_wholly_idle().unwrap());
    let mut root_scope = unit_plan(root.path(), &debt, "root", [71; 32]);
    let loan = bank.try_loan(&mut root_scope).unwrap().unwrap();
    assert!(!bank.is_wholly_idle().unwrap());
    for _ in 0..3 {
        assert!(bank.release_idle(width(1)).unwrap().is_some());
    }
    let other = debt.try_acquire_native(owner(), 4).unwrap().unwrap();
    for name in ["restore-a", "restore-b"] {
        let mut idle = unit_plan(root.path(), &debt, name, [31; 32]);
        assert!(bank.try_reacquire_idle(&debt, &mut idle, 4).unwrap().is_some());
    }
    assert_eq!(bank.funded_width(), 3);
    let mut idle = unit_plan(root.path(), &debt, "restore-c", [31; 32]);
    assert!(bank.try_reacquire_idle(&debt, &mut idle, 4).unwrap().is_none());
    idle.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
    drop(other);
    assert!(bank.try_reacquire_idle(&debt, &mut idle, 4).unwrap().is_some());
    assert_eq!(bank.funded_width(), 4);
    assert_eq!(debt.reserved().unwrap(), 4);
    assert!(!bank.is_wholly_idle().unwrap(), "a genuine live borrower still excludes V1");
    let mut returned = unit_plan(root.path(), &debt, "returned-root", [31; 32]);
    bank.return_unused(loan, &mut returned).unwrap();
    assert!(bank.is_wholly_idle().unwrap());
    bank.settle_drained().unwrap();
    assert_eq!(debt.reserved().unwrap(), 0);
}

#[test]
fn scoped_pair_reacquisition_refuses_lost_and_foreign_originals_without_consuming_idle_key() {
    let Some((root, _, debt)) = setup() else { return };
    let Some((_foreign_root, _, foreign)) = another_domain() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    let mut scope = unit_plan(root.path(), &debt, "root", [72; 32]);
    let loan = bank.try_loan(&mut scope).unwrap().unwrap();
    assert!(bank.release_idle(width(1)).unwrap().is_some());
    let mut idle = unit_plan(root.path(), &debt, "restore", [31; 32]);
    assert!(bank.try_reacquire_idle(&foreign, &mut idle, 4).is_err());
    idle.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
    drop(loan);
    assert!(bank.try_reacquire_idle(&debt, &mut idle, 4).is_err());
    idle.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
    assert_eq!(bank.funded_width(), 3);
    assert_eq!(debt.reserved().unwrap(), 3);
}

#[test]
fn scoped_original_bank_rekeys_the_same_occupied_unit_and_old_keys_cannot_free_a_new_root() {
    let Some((root, _, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _original)| panic!("unused original bank: {error}"));
    let mut first = unit_plan(root.path(), &debt, "first", [41; 32]);
    let mut idle = unit_plan(root.path(), &debt, "idle", [31; 32]);
    let mut second = unit_plan(root.path(), &debt, "second", [42; 32]);
    let mut wrong = unit_plan(root.path(), &debt, "wrong", [43; 32]);
    assert!(bank.retry_pending_loan(&mut first).unwrap().is_none());
    first.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
    assert!(!bank.has_pending_loan());
    let loan = bank.try_loan(&mut first).unwrap().unwrap();
    let slot = loan.slot();
    assert_eq!(debt.reserved().unwrap(), 4);
    assert!(debt.try_reserve(owner(), width(1), 4).unwrap().is_none());
    let (_, loan) = bank.return_unused(loan, &mut wrong).unwrap_err().into_parts();
    wrong.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
    bank.return_unused(loan, &mut idle).unwrap(); // No description/worker was exported.
    assert_eq!(debt.reserved().unwrap(), 4, "return never publishes a Free shadow record");
    let loan = bank.try_loan(&mut second).unwrap().unwrap();
    assert_eq!(loan.slot(), slot, "the SAME actual native/shadow pair was rebound");
    assert!(bank.settle_drained().is_err());
    drop(loan); // Unknown borrower loss is durable second-scope debt, not a refund.
    drop(bank);
    drop(first);
    drop(idle);
    drop(second);
    drop(wrong);
    let original = debt
        .restore_recovery(&root.path().join("bank").canonicalize().unwrap(), "original")
        .unwrap();
    assert_eq!(original.retained_units(), 3, "old bank key cannot select the Root's rebound unit");
    original.settle().unwrap(); // All three idle originals were genuinely unexported.
    assert_eq!(debt.reserved().unwrap(), 1);
    let directory = root.path().canonicalize().unwrap();
    for obsolete in ["first", "idle"] {
        let former = debt.restore_recovery(&directory, obsolete).unwrap();
        assert_eq!(former.retained_units(), 0);
        former.settle().unwrap();
        assert_eq!(debt.reserved().unwrap(), 1);
    }
    let current = debt.restore_recovery(&directory, "second").unwrap();
    assert_eq!(current.retained_units(), 1);
    current.settle().unwrap(); // This fixture never exported execution.
    assert_eq!(debt.reserved().unwrap(), 0);
}

#[test]
fn scoped_original_bank_refuses_idle_scope_and_preserves_unused_conversion_custody() {
    let Some((root, _, debt)) = setup() else { return };
    let mut local = capacity_bank(root.path(), &debt, "bank");
    let loan = local.try_loan().unwrap().unwrap();
    let (error, mut local) = match local.try_into_scoped() {
        Err((error, original)) => (error, *original),
        Ok(_) => panic!("an issued original bank cannot become another phase owner"),
    };
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    local.return_unused(loan).unwrap();
    local.settle_drained().unwrap();

    let mut bank = capacity_bank(root.path(), &debt, "scoped")
        .try_into_scoped()
        .unwrap_or_else(|(error, _original)| panic!("unused original bank: {error}"));
    let mut idle = unit_plan(root.path(), &debt, "idle", [31; 32]);
    assert!(bank.try_loan(&mut idle).is_err());
    idle.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
    bank.settle_drained().unwrap();
}

#[test]
fn unit_recovery_uses_a_real_private_key_without_locking_unrelated_live_slots() {
    let Some((root, _, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _original)| panic!("unused original bank: {error}"));
    let mut scope = unit_plan(root.path(), &debt, "scope", [41; 32]);
    let nonce = scope.nonces().unwrap()[0];
    let loan = bank.try_loan(&mut scope).unwrap().unwrap();
    let candidates = debt.recovery_candidates().unwrap();
    assert_eq!(candidates.len(), 4);
    let candidate = candidates.into_iter().find(|entry| entry.nonce == nonce).unwrap();
    drop(loan); // Never exported; occupied Root debt survives the holder loss.
    drop(scope);
    let directory = root.path().canonicalize().unwrap();
    let mut forged = candidate;
    forged.nonce[0] ^= 1;
    assert!(debt.restore_unit_recovery(&directory, "scope", forged).is_err());
    assert_eq!(debt.reserved().unwrap(), 4);
    // Three unrelated original shadow slots are STILL locked by the bank.
    // This targeted recovery authenticates/locks only its own actual unit.
    let original = debt.restore_unit_recovery(&directory, "scope", candidate).unwrap().unwrap();
    assert_eq!(original.retained_units(), 1);
    assert_eq!(original.identities().unwrap()[0].nonce, nonce);
    original.settle().unwrap(); // Actual lexical non-use, not candidate DATA.
    assert_eq!(debt.reserved().unwrap(), 3);
    assert!(debt.restore_unit_recovery(&directory, "scope", candidate).unwrap().is_none());
    assert_eq!(debt.reserved().unwrap(), 3, "stale lookup grants/releases nothing");
    drop(bank);
    let base = debt
        .restore_recovery(&root.path().join("bank").canonicalize().unwrap(), "original")
        .unwrap();
    assert_eq!(base.retained_units(), 3);
    base.settle().unwrap(); // All three originals were never exported.
    assert_eq!(debt.reserved().unwrap(), 0);
}

#[cfg(feature = "native-host")]
#[test]
fn original_workload_continuation_keeps_shared_cursor_and_never_reacquires_at_zero_headroom() {
    use std::os::fd::AsFd as _;
    let Some((root, native, debt)) = setup() else { return };
    let store = root.path().join("continuation");
    std::fs::create_dir(&store).unwrap();
    std::fs::set_permissions(&store, std::fs::Permissions::from_mode(0o700)).unwrap();
    let store = store.canonicalize().unwrap();
    let mut prepared = debt
        .prepare_recoverable(owner(), width(4), [15; 32])
        .unwrap()
        .persist(&store, "original")
        .unwrap();
    let mut active = debt.try_acquire_all_recoverable(&mut prepared).unwrap().unwrap();
    let original = &active.native_leases()[0];
    let mut source = File::from(original.as_fd().try_clone_to_owned().unwrap());
    source.seek(SeekFrom::Start(13)).unwrap();
    // The private leaf is reached in production ONLY by the opaque live
    // receiver. This exact-source test supplies the actual typed original.
    let continuation =
        native.continue_workload_original(original.slot(), source.try_clone().unwrap()).unwrap();
    assert_eq!(source.stream_position().unwrap(), 13);
    assert_eq!(debt.reserved().unwrap(), 4);
    assert!(debt.try_acquire_native(owner(), 4).unwrap().is_none());
    drop(continuation);
    assert!(native.snapshot().unwrap().iter().all(|slot| matches!(slot, SlotState::Held { .. })));
    drop(source);
    active.settle_exclusion().unwrap();
}

#[test]
fn all_domain_waiters_keep_no_partial_primaries_and_original_debt_survives_fd_loss() {
    let Some((root, native, debt)) = setup() else { return };
    let first_store = root.path().join("first-root");
    let second_store = root.path().join("second-root");
    for path in [&first_store, &second_store] {
        std::fs::create_dir(path).unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
    }
    let first_store = first_store.canonicalize().unwrap();
    let second_store = second_store.canonicalize().unwrap();
    let mut first = debt
        .prepare_recoverable(owner(), width(4), [11; 32])
        .unwrap()
        .persist(&first_store, "original")
        .unwrap();
    let mut second = debt
        .prepare_recoverable(owner(), width(4), [12; 32])
        .unwrap()
        .persist(&second_store, "original")
        .unwrap();
    let old = debt.try_acquire_native(owner(), 4).unwrap().unwrap();
    let nonces = first.nonces().unwrap();
    for pending in [&mut first, &mut second] {
        assert!(debt.try_acquire_all_recoverable(pending).unwrap().is_none());
        assert_eq!(
            native
                .snapshot()
                .unwrap()
                .iter()
                .filter(|slot| matches!(slot, SlotState::Held { .. }))
                .count(),
            1
        );
        assert_eq!(debt.reserved().unwrap(), 0);
    }
    assert_eq!(first.nonces().unwrap(), nonces);
    drop(old);
    let active = debt.try_acquire_all_recoverable(&mut first).unwrap().unwrap();
    assert_eq!(active.native_leases().len(), 4);
    let slots =
        active.native_leases().iter().map(Lease::slot).collect::<std::collections::BTreeSet<_>>();
    assert_eq!(slots.len(), 4);
    assert_eq!(debt.reserved().unwrap(), 4);
    assert!(debt.try_acquire_all_recoverable(&mut second).unwrap().is_none());
    assert!(debt.try_acquire_native(owner(), 4).unwrap().is_none());
    // No target was ever dispatched in this primitive fixture. Deliberately
    // lose every live FD: that is NOT a positive-retirement observation.
    drop(active);
    drop(first);
    assert!(
        native.snapshot().unwrap().iter().all(|slot| matches!(slot, SlotState::Available { .. }))
    );
    assert_eq!(debt.reserved().unwrap(), 4);
    assert!(debt.try_acquire_all_recoverable(&mut second).unwrap().is_none());
    assert!(debt.try_acquire_native(owner(), 4).unwrap().is_none());
    let original = debt.restore_recovery(&first_store, "original").unwrap();
    assert_eq!(original.context(), [11; 32]);
    original.settle().unwrap(); // This fixture positively never launched work.
    let mut resumed = debt.try_acquire_all_recoverable(&mut second).unwrap().unwrap();
    assert_eq!(resumed.native_leases().len(), 4);
    resumed.settle_exclusion().unwrap();
    assert!(resumed.exclusion_settled());
    drop(resumed);
    assert_eq!(debt.reserved().unwrap(), 0);
    assert!(
        native.snapshot().unwrap().iter().all(|slot| matches!(slot, SlotState::Available { .. }))
    );
}

#[test]
fn all_domain_reservation_rejects_narrow_or_changed_original_preparation_without_acquiring() {
    let Some((root, native, debt)) = setup() else { return };
    let store = root.path().join("material");
    std::fs::create_dir(&store).unwrap();
    std::fs::set_permissions(&store, std::fs::Permissions::from_mode(0o700)).unwrap();
    let store = store.canonicalize().unwrap();
    let mut narrow = debt
        .prepare_recoverable(owner(), width(1), [13; 32])
        .unwrap()
        .persist(&store, "narrow")
        .unwrap();
    assert!(debt.try_acquire_all_recoverable(&mut narrow).is_err());
    let mut changed = debt
        .prepare_recoverable(owner(), width(4), [14; 32])
        .unwrap()
        .persist(&store, "changed")
        .unwrap();
    std::fs::write(store.join("changed"), b"incomplete original authority").unwrap();
    assert!(debt.try_acquire_all_recoverable(&mut changed).is_err());
    assert_eq!(std::fs::read(store.join("changed")).unwrap(), b"incomplete original authority");
    assert_eq!(debt.reserved().unwrap(), 0);
    assert!(
        native.snapshot().unwrap().iter().all(|slot| matches!(slot, SlotState::Available { .. }))
    );
}

#[test]
fn observation_absence_is_read_only_and_busy_has_no_counts() {
    let _fixture = crate::tests::kernel_fixture();
    let root = crate::tests::private_tempdir();
    let native = Pool::open_in(root.path(), width(2)).unwrap();
    let _lease = native.try_acquire(owner()).unwrap().unwrap();
    let (slots, external) = ExternalDebt::observe(&native, None).unwrap();
    assert_eq!(slots.iter().filter(|slot| matches!(slot, SlotState::Held { .. })).count(), 1);
    assert!(external.is_none());
    assert!(!native.path().join(ANCHOR).exists());
    assert!(!native.path().join(DOMAIN).exists());
    let lock = manifest(&native).unwrap();
    lock.lock().unwrap();
    assert_eq!(ExternalDebt::observe(&native, None).unwrap_err().kind(), io::ErrorKind::WouldBlock);
}

#[test]
fn observation_distinguishes_live_retained_and_settled_external_units() {
    let Some((_root, native, debt)) = setup() else { return };
    let _worker = debt.try_acquire_native(owner(), 4).unwrap().unwrap();
    let mut external = debt.try_reserve(owner(), width(2), 4).unwrap().unwrap();
    let anchor = native.path().join(ANCHOR);
    let before = std::fs::read(&anchor).unwrap();
    let observe = || {
        let (slots, external) = ExternalDebt::observe(&native, Some(&debt.retirement)).unwrap();
        let external = external.unwrap();
        (
            slots.iter().filter(|slot| matches!(slot, SlotState::Held { .. })).count(),
            external.iter().filter(|slot| matches!(slot, RetainedSlotState::Held { .. })).count(),
            external
                .iter()
                .filter(|slot| matches!(slot, RetainedSlotState::Retained { .. }))
                .count(),
        )
    };
    assert_eq!(observe(), (1, 2, 0));
    external.pop().unwrap().settle().unwrap();
    assert_eq!(observe(), (1, 1, 0));
    drop(external);
    assert_eq!(observe(), (1, 0, 1));
    assert_eq!(std::fs::read(&anchor).unwrap(), before);
}

#[test]
fn observation_refuses_partial_or_malformed_state_without_repair() {
    let Some((root, native, debt)) = setup() else { return };
    assert!(ExternalDebt::observe(&native, None).is_err());
    let anchor = native.path().join(ANCHOR);
    std::fs::write(&anchor, b"partial").unwrap();
    assert!(ExternalDebt::observe(&native, Some(&debt.retirement)).is_err());
    assert_eq!(std::fs::read(&anchor).unwrap(), b"partial");
    std::fs::remove_file(&anchor).unwrap();
    assert!(ExternalDebt::observe(&native, Some(&debt.retirement)).is_err());
    std::fs::rename(native.path().join(DOMAIN), root.path().join("detached-debt")).unwrap();
    crate::tests::private_file(&anchor, b"partial");
    assert!(ExternalDebt::observe(&native, Some(&debt.retirement)).is_err());
    assert!(!native.path().join(DOMAIN).exists());
}
pub(super) struct Fixture {
    root: Root,
    legacy: std::path::PathBuf,
    // Declared last, so it is released only after the directory is removed.
    // A second domain in one test runs under its first domain's hold.
    _kernel: Option<crate::tests::KernelFixture>,
}
impl Fixture {
    pub(super) fn path(&self) -> &Path {
        self.root.0.path()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::set_permissions(&self.legacy, std::fs::Permissions::from_mode(0o700));
    }
}
/// A fixture's directory. Its drop checks that the kernel fixture is still
/// held before the TempDir removes the directory, whatever released the hold
/// first: a field order or a drop elsewhere. `Fixture::drop` could not see a
/// field order, since it runs before any field is dropped.
struct Root(tempfile::TempDir);
impl Drop for Root {
    fn drop(&mut self) {
        // Asserting while another failure unwinds would abort the binary.
        if !std::thread::panicking() {
            assert!(
                crate::tests::kernel_fixture_held(),
                "a fixture's directory outlived its kernel fixture"
            );
        }
    }
}
/// These tests assert that a dropped lease, bundle or authority frees its
/// unit at once. A child that another test spawns holds a copy of every
/// descriptor of this process, these included, until its exec. Spawning tests
/// hold the crate's kernel fixture, so hold it before the first descriptor
/// opens and until the fixture's directory is removed.
pub(super) fn setup() -> Option<(Fixture, Pool, ExternalDebt)> {
    domain(Some(crate::tests::kernel_fixture()))
}

/// Another domain, inside a test whose first domain holds the kernel fixture.
pub(super) fn another_domain() -> Option<(Fixture, Pool, ExternalDebt)> {
    domain(None)
}

/// A domain under the kernel fixture: `setup`'s own hold, or the first
/// domain's for `another_domain`. Nothing opens before the hold is checked.
fn domain(kernel: Option<crate::tests::KernelFixture>) -> Option<(Fixture, Pool, ExternalDebt)> {
    assert!(
        crate::tests::kernel_fixture_held(),
        "a fixture would open descriptors before the kernel fixture is held"
    );
    let root = crate::tests::private_tempdir();
    let legacy = root.path().join("legacy");
    std::fs::create_dir(&legacy).unwrap();
    std::fs::set_permissions(&legacy, std::fs::Permissions::from_mode(0o700)).unwrap();
    let retired = LegacyRetirement::retire(&legacy, 1);
    // Permission retirement is deliberately unavailable to root.
    // SAFETY: geteuid only reads process identity.
    if unsafe { libc::geteuid() } == 0 {
        assert!(retired.is_err());
        return None;
    }
    let retired = retired.unwrap();
    let native = Pool::open_in(root.path(), width(4)).unwrap();
    let debt = ExternalDebt::activate(&native, &retired).unwrap();
    Some((Fixture { root: Root(root), legacy, _kernel: kernel }, native, debt))
}

#[test]
fn every_fixture_holds_the_kernel_fixture_for_its_life() {
    let Some((root, native, debt)) = setup() else { return };
    assert!(crate::tests::kernel_fixture_held(), "a fixture opened descriptors unguarded");
    drop((debt, native));
    drop(another_domain());
    assert!(crate::tests::kernel_fixture_held(), "another domain released the first one's hold");
    drop(root);
    assert!(!crate::tests::kernel_fixture_held(), "the hold outlived its fixture");
}

#[test]
fn native_and_retained_external_width_share_one_capacity() {
    let Some((_root, native, debt)) = setup() else {
        return;
    };
    let worker = debt.try_acquire_native(owner(), 4).unwrap().unwrap();
    let external = debt.try_reserve(owner(), width(3), 4).unwrap().unwrap();
    assert_eq!(debt.reserved().unwrap(), 3);
    assert!(debt.try_reserve(owner(), width(1), 4).unwrap().is_none());
    // The policy already reports native-only headroom; reserve subtracts from
    // physical width independently, never from that already-adjusted value.
    assert_eq!(debt.native_limit(2).unwrap(), 1);
    drop(external);
    assert_eq!(debt.reserved().unwrap(), 3, "closing custody cannot erase debt");
    drop(worker);
    let reopened = ExternalDebt::open(&native, &debt.retirement).unwrap().unwrap();
    assert_eq!(reopened.reserved().unwrap(), 3);
    assert_eq!(reopened.native_limit(1).unwrap(), 1);
    assert_eq!(reopened.native_limit(0).unwrap(), 0);
}

#[test]
fn settled_bundle_returns_exact_width_and_small_limit_never_partially_grants() {
    let Some((_root, _native, debt)) = setup() else {
        return;
    };
    assert!(debt.try_reserve(owner(), width(3), 2).unwrap().is_none());
    assert_eq!(debt.reserved().unwrap(), 0);
    let bundle = debt.try_reserve(owner(), width(2), 3).unwrap().unwrap();
    assert_eq!(bundle.len(), 2);
    assert!(debt.try_reserve(owner(), width(2), 3).unwrap().is_none());
    for lease in bundle {
        lease.settle().unwrap();
    }
    assert_eq!(debt.reserved().unwrap(), 0);
    assert_eq!(debt.native_limit(2).unwrap(), 2);
}

#[test]
fn actual_native_manifest_lock_prevents_external_admission() {
    let Some((_root, native, debt)) = setup() else {
        return;
    };
    let lock = manifest(&native).unwrap();
    lock.lock().unwrap();
    assert!(debt.try_reserve(owner(), width(1), 4).unwrap().is_none());
    assert_eq!(debt.reserved().unwrap(), 0);
    lock.unlock().unwrap();
    assert!(debt.try_reserve(owner(), width(1), 4).unwrap().is_some());
}

#[test]
fn competing_external_grants_do_not_overcommit() {
    let Some((_root, _native, debt)) = setup() else {
        return;
    };
    let barrier = Arc::new(Barrier::new(9));
    let handles: Vec<_> = (0..8)
        .map(|_| {
            let barrier = Arc::clone(&barrier);
            let debt = debt.clone();
            std::thread::spawn(move || {
                barrier.wait();
                debt.try_reserve(owner(), width(2), 4).unwrap()
            })
        })
        .collect();
    barrier.wait();
    let bundles: Vec<_> = handles.into_iter().filter_map(|worker| worker.join().unwrap()).collect();
    assert!(!bundles.is_empty());
    assert!(bundles.len() <= 2);
    assert_eq!(debt.reserved().unwrap(), (bundles.len() * 2) as u32);
    for bundle in bundles {
        for lease in bundle {
            lease.settle().unwrap();
        }
    }
    assert_eq!(debt.reserved().unwrap(), 0);
}

#[test]
fn incomplete_activation_and_missing_or_replaced_bound_domain_refuse() {
    let Some((root, native, debt)) = setup() else {
        return;
    };
    let bound = native.path().join(DOMAIN);
    std::fs::rename(&bound, root.path().join("old-bound")).unwrap();
    assert!(debt.reserved().is_err());
    assert!(ExternalDebt::open(&native, &debt.retirement).is_err());
    RetainedPool::create_private(&bound, width(4)).unwrap();
    assert!(ExternalDebt::open(&native, &debt.retirement).is_err());
    std::fs::remove_file(native.path().join(ANCHOR)).unwrap();
    assert!(ExternalDebt::open(&native, &debt.retirement).is_err());

    let root = crate::tests::private_tempdir();
    let native = Pool::open_in(root.path(), width(4)).unwrap();
    assert!(ExternalDebt::open(&native, &debt.retirement).unwrap().is_none());
    crate::tests::private_file(&native.path().join(ANCHOR), format!("{VERSION} initializing=1\n"));
    assert!(ExternalDebt::open(&native, &debt.retirement).is_err());
    assert!(ExternalDebt::activate(&native, &debt.retirement).is_err());
}

#[test]
fn malformed_anchor_is_never_read_as_zero_debt() {
    let Some((_root, native, debt)) = setup() else {
        return;
    };
    let anchor = native.path().join(ANCHOR);
    for bytes in [b"".as_slice(), b"partial", &[b'x'; 1024]] {
        std::fs::write(&anchor, bytes).unwrap();
        assert!(debt.reserved().is_err());
        assert!(ExternalDebt::open(&native, &debt.retirement).is_err());
    }
}

#[test]
fn concurrent_native_and_external_v3_clients_share_the_same_transaction() {
    let Some((_root, _native, debt)) = setup() else {
        return;
    };
    let barrier = Arc::new(Barrier::new(9));
    let workers: Vec<_> = (0..8)
        .map(|index| {
            let barrier = Arc::clone(&barrier);
            let debt = debt.clone();
            std::thread::spawn(move || {
                barrier.wait();
                if index % 2 == 0 {
                    (debt.try_acquire_native(owner(), 4).unwrap(), None)
                } else {
                    (None, debt.try_reserve(owner(), width(1), 4).unwrap())
                }
            })
        })
        .collect();
    barrier.wait();
    let granted: Vec<_> = workers.into_iter().map(|worker| worker.join().unwrap()).collect();
    let native = granted.iter().filter(|(lease, _)| lease.is_some()).count();
    let external = granted.iter().filter(|(_, leases)| leases.is_some()).count();
    assert!(native + external > 0);
    assert!(native + external <= 4);
    for (_, leases) in granted {
        if let Some(leases) = leases {
            for lease in leases {
                lease.settle().unwrap();
            }
        }
    }
}

#[test]
fn prepared_grant_preserves_refused_plan_then_publishes_exact_prejournaled_nonces() {
    let Some((_root, _native, debt)) = setup() else {
        return;
    };
    let mut prepared = PreparedReservation::new(width(3)).unwrap();
    let persisted = prepared.nonces().unwrap().to_vec();
    assert!(debt.try_reserve_prepared(owner(), &mut prepared, 2).unwrap().is_none());
    assert_eq!(prepared.nonces().unwrap(), persisted);
    assert_eq!(debt.reserved().unwrap(), 0);
    let bundle = debt.try_reserve_prepared(owner(), &mut prepared, 4).unwrap().unwrap();
    let actual = bundle.iter().map(|lease| lease.identity().unwrap().nonce).collect::<Vec<_>>();
    assert_eq!(actual, persisted);
    assert!(prepared.nonces().is_err());
    assert!(debt.try_reserve_prepared(owner(), &mut prepared, 4).is_err());
    drop(bundle);
    assert_eq!(debt.reserved().unwrap(), 3, "controller loss retains every published intent nonce");
}

fn recovery_store(root: &Fixture) -> std::path::PathBuf {
    let path = root.path().join("authority");
    std::fs::create_dir(&path).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    path.canonicalize().unwrap()
}
#[test]
fn private_original_authority_restores_exact_debt_and_never_reissues() {
    let Some((root, _native, debt)) = setup() else {
        return;
    };
    let store = recovery_store(&root);
    let mut prepared = debt
        .prepare_recoverable(owner(), width(2), [42; 32])
        .unwrap()
        .persist(&store, "grant")
        .unwrap();
    let nonces = prepared.nonces().unwrap();
    assert_eq!(debt.reserved().unwrap(), 0, "persistence is not a grant");
    assert!(debt.try_reserve_recoverable(&mut prepared, 1).unwrap().is_none());
    assert_eq!(prepared.nonces().unwrap(), nonces);
    let bundle = debt.try_reserve_recoverable(&mut prepared, 4).unwrap().unwrap();
    let identities = bundle.iter().map(|lease| lease.identity().unwrap()).collect::<Vec<_>>();
    assert_eq!(identities.iter().map(|id| id.nonce).collect::<Vec<_>>(), nonces);
    assert!(debt.try_reserve_recoverable(&mut prepared, 4).is_err());
    drop(bundle);
    assert_eq!(debt.reserved().unwrap(), 2);
    assert!(
        debt.restore_recovery(&store, "grant").is_err(),
        "original backing lock still owns authority"
    );
    drop(prepared);
    let restored = debt.restore_recovery(&store, "grant").unwrap();
    assert_eq!(restored.context(), [42; 32]);
    assert_eq!(restored.retained_units(), 2);
    assert_eq!(restored.identities().unwrap(), identities);
    // This fixture never dispatches any target: original no-work closure is
    // known independently of secret possession and the observations above.
    restored.settle().unwrap();
    assert_eq!(debt.reserved().unwrap(), 0);
    let old = debt.restore_recovery(&store, "grant").unwrap();
    assert_eq!(old.retained_units(), 0, "reopening cannot reissue settled units");
}
#[test]
fn public_nonces_or_foreign_domain_cannot_recover_original_authority() {
    let Some((root, _native, debt)) = setup() else {
        return;
    };
    let Some((_foreign, _native2, debt2)) = another_domain() else {
        return;
    };
    let store = recovery_store(&root);
    let mut prepared = debt
        .prepare_recoverable(owner(), width(1), [12; 32])
        .unwrap()
        .persist(&store, "grant")
        .unwrap();
    let public = prepared.nonces().unwrap();
    let bundle = debt.try_reserve_recoverable(&mut prepared, 4).unwrap().unwrap();
    drop(bundle);
    drop(prepared);
    let fake = store.join("public-only");
    std::fs::write(&fake, format!("{public:?}")).unwrap();
    std::fs::set_permissions(&fake, std::fs::Permissions::from_mode(0o600)).unwrap();
    assert!(debt.restore_recovery(&store, "public-only").is_err());
    assert!(debt2.restore_recovery(&store, "grant").is_err());
    assert_eq!(debt.reserved().unwrap(), 1);
    assert_eq!(debt2.reserved().unwrap(), 0);
    let recovered = debt.restore_recovery(&store, "grant").unwrap();
    assert_eq!(recovered.retained_units(), 1);
    recovered.settle().unwrap(); // no target ever dispatched in this fixture
}
#[test]
fn changed_recovery_commitment_never_becomes_settlement_authority() {
    let Some((root, _native, debt)) = setup() else {
        return;
    };
    let store = recovery_store(&root);
    let mut prepared = debt
        .prepare_recoverable(owner(), width(1), [9; 32])
        .unwrap()
        .persist(&store, "grant")
        .unwrap();
    let bundle = debt.try_reserve_recoverable(&mut prepared, 4).unwrap().unwrap();
    let identity = bundle[0].identity().unwrap();
    let path = debt
        .retained
        .path()
        .join(crate::RETAINED_DIRECTORY_NAME)
        .join(crate::unix::slot_name(identity.slot));
    let mut bytes = std::fs::read(&path).unwrap();
    let start =
        bytes.windows(b"commitment=".len()).position(|window| window == b"commitment=").unwrap()
            + b"commitment=".len();
    bytes[start] = if bytes[start] == b'0' { b'1' } else { b'0' };
    std::fs::write(&path, &bytes).unwrap();
    assert!(bundle[0].identity().is_err());
    drop(bundle);
    drop(prepared);
    assert!(debt.restore_recovery(&store, "grant").is_err());
    assert_eq!(std::fs::read(&path).unwrap(), bytes);
    assert_eq!(debt.reserved().unwrap(), 1);
}

#[test]
fn native_manifest_observation_revalidates_the_actual_bound_domain() {
    let Some((_root, native, debt)) = setup() else {
        return;
    };
    let meta = manifest(&native).unwrap().metadata().unwrap();
    assert_eq!(debt.native_manifest_identity().unwrap(), (meta.dev(), meta.ino()));
    std::fs::write(native.path().join(ANCHOR), b"unknown").unwrap();
    assert!(debt.native_manifest_identity().is_err());
}

#[test]
fn raw_native_acquisition_refuses_activated_and_partial_debt() {
    let Some((_root, native, debt)) = setup() else { return };
    let reopen = || Pool::try_open_in(native.path().parent().unwrap(), native.slots()).unwrap();
    assert!(reopen().try_acquire(owner()).is_err());
    #[cfg(feature = "observations")]
    assert!(reopen().try_legacy_fixed_transaction().is_err());
    assert!(debt.try_acquire_native(owner(), 4).unwrap().is_some());
    let anchor = native.path().join(ANCHOR);
    std::fs::write(&anchor, b"partial").unwrap();
    assert!(reopen().try_acquire(owner()).is_err());
    #[cfg(feature = "observations")]
    assert!(reopen().try_legacy_fixed_transaction().is_err());
    assert_eq!(std::fs::read(&anchor).unwrap(), b"partial");
    assert!(debt.try_acquire_native(owner(), 4).is_err());
}

#[cfg(feature = "jobserver")]
#[test]
fn shared_worker_returns_local_tokens_and_counts_crash_retained_debt() {
    use std::os::unix::ffi::OsStrExt;

    use crate::WorkerClient;
    let Some((root, native, debt)) = setup() else { return };
    let implicit = Arc::new(debt.try_acquire_native(owner(), 4).unwrap().unwrap());
    let mut external = debt.try_reserve(owner(), width(3), 4).unwrap().unwrap();
    let fifo = root.path().join("local-credits");
    let name = std::ffi::CString::new(fifo.as_os_str().as_bytes()).unwrap();
    // SAFETY: the NUL-terminated name is in this private fixture's directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let local = jobserver::Client::from_fifo(&fifo).unwrap();
    for _ in 0..3 {
        local.release_raw().unwrap();
    }
    let debt = Arc::new(debt);
    let foreign = crate::tests::private_tempdir();
    let foreign_pool = Pool::open_in(foreign.path(), width(1)).unwrap();
    let foreign_credit = Arc::new(foreign_pool.try_acquire(owner()).unwrap().unwrap());
    assert!(
        WorkerClient::new_shared(
            local.clone(),
            Arc::clone(&debt),
            foreign_credit,
            Arc::new(|_| 4),
            owner()
        )
        .is_err()
    );
    assert_eq!(local.available().unwrap(), 3);
    let client =
        WorkerClient::new_shared(local.clone(), debt, implicit, Arc::new(|_| 4), owner()).unwrap();
    assert!(client.try_acquire().unwrap().is_none());
    assert_eq!(local.available().unwrap(), 3);
    external.pop().unwrap().settle().unwrap();
    drop(external); // two units remain durable debt, not newly free capacity
    let pause = client.try_pause_extras().unwrap().unwrap();
    assert!(!client.extra_admission_running());
    assert!(client.try_acquire().unwrap().is_none());
    assert_eq!(local.available().unwrap(), 3);
    pause.resume().unwrap();
    let credit = client.try_acquire().unwrap().unwrap();
    assert!(client.try_pause_extras().unwrap().is_none());
    assert_eq!(local.available().unwrap(), 2);
    assert!(client.try_acquire().unwrap().is_none());
    assert_eq!(local.available().unwrap(), 2);
    drop(credit);
    assert_eq!(local.available().unwrap(), 3);
    drop(client.try_pause_extras().unwrap().unwrap());
    assert!(!client.extra_admission_running());
    assert_eq!(client.try_acquire().err().unwrap().kind(), io::ErrorKind::PermissionDenied);
    assert_eq!(local.available().unwrap(), 3);
    assert_eq!(
        native
            .snapshot()
            .unwrap()
            .iter()
            .filter(|slot| matches!(slot, SlotState::Held { .. }))
            .count(),
        1
    );
}

#[test]
fn inheritance_release_race_cannot_interleave_a_retained_grant_or_expand_entry_occupancy() {
    let Some((_root, native, debt)) = setup() else { return };
    let mut original = Some(debt.try_acquire_native(owner(), 4).unwrap().unwrap());
    let slot = original.as_ref().unwrap().slot();
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(native.path().join(format!("slot-{slot:08}")))
        .unwrap();
    assert!(native.try_adopt_inherited(&file, |_| 4).is_err(), "raw activated inheritance refuses");
    let adopted = debt
        .adopt_with(
            &file,
            |_| 4,
            || {
                // Deterministically reproduce the old held-probe/release/lock race.
                drop(original.take());
                assert!(
                    debt.try_reserve(owner(), width(4), 4).unwrap().is_none(),
                    "same manifest excludes a new retained grant"
                );
                assert!(debt.try_acquire_native(owner(), 4).unwrap().is_none());
            },
        )
        .unwrap()
        .unwrap();
    drop(file);
    let held =
        native.snapshot().unwrap().iter().filter(|s| matches!(s, SlotState::Held { .. })).count();
    assert_eq!(held, 1, "replacement cannot increase the entry occupancy");
    assert_eq!(debt.reserved().unwrap(), 0);
    assert!(debt.try_reserve(owner(), width(4), 4).unwrap().is_none());
    let external = debt.try_reserve(owner(), width(3), 4).unwrap().unwrap();
    assert_eq!(debt.reserved().unwrap() + held as u32, 4);
    drop(adopted);
    for lease in external {
        lease.settle().unwrap();
    }
}
