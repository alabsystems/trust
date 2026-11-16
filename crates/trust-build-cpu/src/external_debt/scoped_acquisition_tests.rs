use std::io::{Seek as _, SeekFrom, Write as _};
use std::os::fd::{AsFd as _, AsRawFd as _};

use super::*;
use crate::external_debt::tests::{another_domain, capacity_bank, setup, unit_plan, width};

#[test]
fn scoped_original_description_view_keeps_real_generation_and_requires_closed_return() {
    let Some((root, _, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "original-view")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    let mut scope = unit_plan(root.path(), &debt, "scope-view", [71; 32]);
    let loan = bank.try_loan(&mut scope).unwrap().unwrap();
    let nonce = scope.nonces().unwrap()[0];
    loan.with_original_descriptions(|descriptions, generation| {
        assert_eq!(generation.nonce, nonce);
        for descriptor in descriptions {
            // SAFETY: observe only the actual live borrowed original fd.
            let mut stat: libc::stat = unsafe { std::mem::zeroed() };
            // SAFETY: initialized native output and a held original descriptor.
            assert_eq!(unsafe { libc::fstat(descriptor.as_raw_fd(), &mut stat) }, 0);
            assert_ne!(stat.st_ino, 0);
        }
        Ok(())
    })
    .unwrap();
    let mut idle = unit_plan(root.path(), &debt, "idle-view", [31; 32]);
    let refusal = bank.return_unused(loan, &mut idle).unwrap_err();
    let (_, loan) = refusal.into_parts();
    // SAFETY: this callback only inspected borrowed originals. No descriptor
    // was duplicated, no target ran, and the callback has fully returned.
    unsafe { bank.return_after_scope(loan, &mut idle) }.unwrap();
    bank.settle_drained().unwrap();
    assert_eq!(debt.reserved().unwrap(), 0);
}

#[test]
fn pending_pair_acquisition_keeps_native_guard_and_exact_key_through_prefix_and_lost_ack() {
    for prefix in [true, false] {
        let Some((root, native, debt)) = setup() else { return };
        let mut bank = capacity_bank(root.path(), &debt, "bank")
            .try_into_scoped()
            .unwrap_or_else(|(error, _)| panic!("{error}"));
        bank.release_idle(width(1)).unwrap().unwrap();
        let mut idle = unit_plan(root.path(), &debt, "reacquire", [31; 32]);
        let mut wrong = unit_plan(root.path(), &debt, "wrong", [31; 32]);
        assert!(bank.retry_pending_reacquisition(&debt, &mut idle).unwrap().is_none());
        assert!(
            bank.reacquire_with(&debt, &mut idle, 4, |pending, key| {
                pending.finish_with(key, |file, text| {
                    file.seek(SeekFrom::Start(0))?;
                    file.set_len(0)?;
                    file.write_all(if prefix { &text.as_bytes()[..13] } else { text.as_bytes() })?;
                    file.sync_all()?;
                    Err(io::Error::other("actual write/ACK failed"))
                })
            })
            .is_err()
        );
        assert!(bank.has_pending_reacquisition());
        assert_eq!(bank.funded_width(), 3, "uncommitted backing is not lendable");
        assert!(
            native
                .snapshot()
                .unwrap()
                .iter()
                .all(|slot| matches!(slot, crate::SlotState::Held { .. })),
            "the pending owner retains the actual fourth native guard"
        );
        assert!(bank.release_idle(width(1)).is_err());
        assert!(bank.settle_drained().is_err());
        assert!(bank.retry_pending_reacquisition(&debt, &mut wrong).is_err());
        wrong.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
        assert!(bank.has_pending_reacquisition());
        // Zero policy cannot acquire fresh capacity. It can finish the SAME
        // already captured pair for stopped-owner cleanup, without renewal.
        assert!(bank.retry_pending_reacquisition(&debt, &mut idle).unwrap().is_some());
        assert!(!bank.has_pending_reacquisition());
        assert_eq!(bank.funded_width(), 4);
        assert_eq!(debt.reserved().unwrap(), 4);
        bank.settle_drained().unwrap(); // No execution was ever exported.
        assert_eq!(debt.reserved().unwrap(), 0);
    }
}

#[test]
fn prewrite_pair_retention_holds_both_actual_originals_through_sender_loss() {
    for torn in [false, true] {
        let Some((root, native, debt)) = setup() else { return };
        let mut bank = capacity_bank(root.path(), &debt, "bank")
            .try_into_scoped()
            .unwrap_or_else(|(error, _)| panic!("{error}"));
        bank.release_idle(width(1)).unwrap().unwrap();
        let mut idle = unit_plan(root.path(), &debt, "pending", [31; 32]);
        let wrong = unit_plan(root.path(), &debt, "wrong", [31; 32]);
        let (native_copy, shadow_copy, native_slot, shadow_slot, nonce) = {
            let offer = bank.prepare_reacquire_idle(&debt, &mut idle, 4).unwrap().unwrap();
            let [native, shadow] = offer.descriptions().unwrap();
            (
                native.try_clone_to_owned().unwrap(),
                shadow.try_clone_to_owned().unwrap(),
                offer.native_slot(),
                offer.shadow_slot().unwrap(),
                offer.nonce().unwrap(),
            )
        };
        assert_eq!(bank.funded_width(), 3, "preparation is not a published funded unit");
        assert!(bank.commit_reacquire_idle(&debt, &wrong).is_err());
        assert!(bank.release_idle(width(1)).is_err());
        let again = bank.prepare_reacquire_idle(&debt, &mut idle, 0).unwrap().unwrap();
        assert_eq!(
            (again.native_slot(), again.shadow_slot().unwrap(), again.nonce().unwrap()),
            (native_slot, shadow_slot, nonce),
            "same original key/FD pair, no new acquisition"
        );
        wrong.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
        if torn {
            assert!(
                bank.reacquire_with(&debt, &mut idle, 0, |pending, key| {
                    pending.finish_with(key, |file, text| {
                        file.set_len(0)?;
                        file.seek(SeekFrom::Start(0))?;
                        file.write_all(&text.as_bytes()[..13])?;
                        file.sync_all()?;
                        Err(io::Error::other("actual interrupted canonical write"))
                    })
                })
                .is_err()
            );
        }
        drop(bank);
        assert!(matches!(
            native.snapshot().unwrap()[native_slot as usize],
            crate::SlotState::Held { .. }
        ));
        assert!(matches!(
            debt.retained.snapshot().unwrap()[shadow_slot as usize],
            crate::RetainedSlotState::Held { .. }
        ));
        assert!(debt.retained.try_acquire(crate::Owner::current(None)).unwrap().is_none());
        assert!(
            std::fs::File::from(native_copy.as_fd().try_clone_to_owned().unwrap())
                .metadata()
                .unwrap()
                .is_file()
        );
        drop((native_copy, shadow_copy));
        if torn {
            assert!(
                debt.reserved().is_err(),
                "losing every live owner never converts torn debt to Free"
            );
        } else {
            assert_eq!(debt.reserved().unwrap(), 3, "unpublished untouched unit was not issued");
        }
        // Actual same-OFD retention only. No SDK grant, arbitrary descendant
        // quiescence, SIGKILL settlement or cold recovery is inferred here.
    }
}

#[test]
fn retained_prewrite_pair_commits_only_its_original_key_without_second_acquisition() {
    let Some((root, native, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    bank.release_idle(width(1)).unwrap().unwrap();
    let mut idle = unit_plan(root.path(), &debt, "captured", [31; 32]);
    let (actual_slot, originals) = {
        let offer = bank.prepare_reacquire_idle(&debt, &mut idle, 4).unwrap().unwrap();
        let [native, shadow] = offer.descriptions().unwrap();
        (
            offer.native_slot(),
            [native.try_clone_to_owned().unwrap(), shadow.try_clone_to_owned().unwrap()],
        )
    };
    assert_eq!(bank.funded_width(), 3);
    assert_eq!(bank.commit_reacquire_idle(&debt, &idle).unwrap(), actual_slot);
    assert_eq!(bank.funded_width(), 4);
    assert!(!bank.has_pending_reacquisition());
    assert!(bank.commit_reacquire_idle(&debt, &idle).is_err());
    assert!(
        native.snapshot().unwrap().iter().all(|slot| matches!(slot, crate::SlotState::Held { .. }))
    );
    drop(originals);
    bank.settle_drained().unwrap(); // Never exported execution in this fixture.
    assert_eq!(debt.reserved().unwrap(), 0);
}

#[test]
fn moved_pending_keeper_preserves_originals_and_only_returns_to_the_same_bank() {
    let Some((root, native, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    bank.release_idle(width(1)).unwrap().unwrap();
    let mut idle = unit_plan(root.path(), &debt, "moved", [31; 32]);
    let (slot, shadow, nonce) = {
        let pair = bank.prepare_reacquire_idle(&debt, &mut idle, 4).unwrap().unwrap();
        (pair.native_slot(), pair.shadow_slot().unwrap(), pair.nonce().unwrap())
    };
    let custody = bank.take_pending_custody().unwrap().unwrap();
    let (send, receive) = std::sync::mpsc::sync_channel(0);
    let (return_to_bank, returned) = std::sync::mpsc::sync_channel(0);
    let keeper = std::thread::spawn(move || {
        assert_eq!(custody.descriptions().unwrap().len(), 2);
        send.send(()).unwrap();
        returned.recv().unwrap();
        custody
    });
    receive.recv().unwrap();
    assert_eq!(bank.funded_width(), 3);
    assert!(bank.has_pending_reacquisition());
    assert!(bank.commit_reacquire_idle(&debt, &idle).is_err());
    assert!(bank.prepare_reacquire_idle(&debt, &mut idle, 4).is_err());
    assert!(bank.release_idle(width(1)).is_err());
    assert!(bank.settle_drained().is_err());
    assert!(matches!(native.snapshot().unwrap()[slot as usize], crate::SlotState::Held { .. }));
    assert!(matches!(
        debt.retained.snapshot().unwrap()[shadow as usize],
        crate::RetainedSlotState::Held { .. }
    ));
    return_to_bank.send(()).unwrap();
    let mut custody = Some(keeper.join().unwrap());
    let Some((other_root, _, other_debt)) = another_domain() else { panic!("fixture unavailable") };
    let mut other = capacity_bank(other_root.path(), &other_debt, "other")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    other.release_idle(width(1)).unwrap().unwrap();
    let mut other_idle = unit_plan(other_root.path(), &other_debt, "moved", [31; 32]);
    other.prepare_reacquire_idle(&other_debt, &mut other_idle, 4).unwrap().unwrap();
    let mut other_owner = other.take_pending_custody().unwrap();
    assert!(other.restore_pending_custody(&mut custody).is_err());
    assert!(custody.is_some());
    other.restore_pending_custody(&mut other_owner).unwrap();
    bank.restore_pending_custody(&mut custody).unwrap();
    assert!(custody.is_none());
    let pair = bank.prepare_reacquire_idle(&debt, &mut idle, 0).unwrap().unwrap();
    assert_eq!(
        (pair.native_slot(), pair.shadow_slot().unwrap(), pair.nonce().unwrap()),
        (slot, shadow, nonce)
    );
    assert_eq!(bank.commit_reacquire_idle(&debt, &idle).unwrap(), slot);
    bank.settle_drained().unwrap(); // Neither fixture exported work.
    other.commit_reacquire_idle(&other_debt, &other_idle).unwrap();
    other.settle_drained().unwrap();
}

#[test]
fn lost_move_only_keeper_never_reopens_the_original_bank() {
    let Some((root, native, debt)) = setup() else { return };
    let mut bank = capacity_bank(root.path(), &debt, "bank")
        .try_into_scoped()
        .unwrap_or_else(|(error, _)| panic!("{error}"));
    bank.release_idle(width(1)).unwrap().unwrap();
    let mut idle = unit_plan(root.path(), &debt, "lost", [31; 32]);
    let slot = bank.prepare_reacquire_idle(&debt, &mut idle, 4).unwrap().unwrap().native_slot();
    let custody = bank.take_pending_custody().unwrap().unwrap();
    drop(custody); // Uncommitted, never exported execution.
    assert!(matches!(
        native.snapshot().unwrap()[slot as usize],
        crate::SlotState::Available { .. }
    ));
    assert_eq!(bank.funded_width(), 3);
    assert!(bank.has_pending_reacquisition());
    assert!(bank.restore_pending_custody(&mut None).is_err());
    assert!(bank.retry_pending_reacquisition(&debt, &mut idle).is_err());
    assert!(bank.commit_reacquire_idle(&debt, &idle).is_err());
    assert!(bank.settle_drained().is_err());
    // A process/SDK/worker closure is not inferred from this local loss.
}
