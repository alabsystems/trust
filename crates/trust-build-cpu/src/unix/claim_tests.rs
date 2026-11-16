// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! A claimed slot's lock while a concurrent spawn holds a copy of the
//! descriptor table: a failed record write must unlock it, and only the lease
//! of a written claim may keep it.

use std::cell::RefCell;

use super::*;
use crate::tests::KernelFixture;
use crate::tests::descriptor_copy::{Unexecuted, relockable};

/// The copies made for one claim, and the error its record write returns.
/// `copies` is declared first, so every copy is killed and reaped before the
/// kernel fixture is released.
struct Armed {
    copies: Vec<Unexecuted>,
    failure: Option<io::ErrorKind>,
    fixture: KernelFixture,
}

thread_local! {
    static ARMED: RefCell<Option<Armed>> = const { RefCell::new(None) };
}

/// `try_acquire_in_transaction`'s hook: on a thread that `while_copied` armed,
/// copy the descriptor table while the new claim holds its slot, then fail the
/// claim before its record is written when the test asked for a failure.
pub(super) fn locked() -> io::Result<()> {
    ARMED.with_borrow_mut(|armed| {
        let Some(armed) = armed else { return Ok(()) };
        let copy = Unexecuted::copy(&armed.fixture);
        armed.copies.push(copy);
        armed.failure.map_or(Ok(()), |kind| Err(io::Error::new(kind, "injected record failure")))
    })
}

/// Runs `claim` with every slot it locks copied into an unexecuted fork, then
/// `observe` with its result while each copy still lives. Every copy is killed
/// and reaped, and the fixture released, before this returns or unwinds, so a
/// failed assertion leaves no copy holding other tests' descriptors. Returns
/// the observation and the number of locks copied.
fn while_copied<T, O>(
    fixture: KernelFixture,
    failure: Option<io::ErrorKind>,
    claim: impl FnOnce() -> T,
    observe: impl FnOnce(T) -> O,
) -> (O, usize) {
    struct Disarm;
    impl Drop for Disarm {
        fn drop(&mut self) {
            drop(ARMED.with_borrow_mut(Option::take));
        }
    }
    ARMED.with_borrow_mut(|armed| *armed = Some(Armed { copies: Vec::new(), failure, fixture }));
    let disarm = Disarm;
    let claimed = claim();
    // Stop copying, but keep the copies alive while observing.
    let armed = ARMED.with_borrow_mut(Option::take);
    drop(disarm);
    let observed = observe(claimed);
    let copies = armed.as_ref().map_or(0, |armed| armed.copies.len());
    drop(armed);
    (observed, copies)
}

fn owner() -> Owner {
    Owner::current(Some(123))
}

#[test]
fn a_failed_record_write_unlocks_its_slot_while_a_spawn_holds_a_copy() {
    // Each copy holds every open description: own the descriptor table.
    let fixture = crate::tests::kernel_fixture();
    let directory = crate::tests::private_tempdir();
    let pool = Pool::open_in(directory.path(), NonZeroU32::MIN).unwrap();
    let slot = pool.path().join(slot_name(0));
    let ((claim, relocked, snapshot), copies) = while_copied(
        fixture,
        Some(io::ErrorKind::StorageFull),
        || pool.try_acquire(owner()),
        |claim| (claim, relockable(&slot), pool.snapshot()),
    );
    assert_eq!(copies, 1, "the claim did not lock its one slot");
    assert_eq!(claim.err().map(|error| error.kind()), Some(io::ErrorKind::StorageFull));
    assert!(relocked, "a failed record write kept its slot locked through a spawn's copy");
    assert_eq!(
        snapshot.unwrap(),
        [SlotState::Available { slot: 0 }],
        "a failed record write was observed as held work"
    );
}

#[test]
fn a_written_claim_hands_its_lock_to_the_lease_alone() {
    let fixture = crate::tests::kernel_fixture();
    let directory = crate::tests::private_tempdir();
    let pool = Pool::open_in(directory.path(), NonZeroU32::MIN).unwrap();
    let slot = pool.path().join(slot_name(0));
    let ((leased, released), copies) = while_copied(
        fixture,
        None,
        || pool.try_acquire(owner()),
        |claim| {
            let lease = claim.unwrap().expect("the one free slot is claimed");
            let leased = (relockable(&slot), pool.snapshot().unwrap());
            drop(lease);
            (leased, relockable(&slot))
        },
    );
    assert_eq!(copies, 1, "the claim did not lock its one slot");
    assert_eq!(
        leased,
        (false, vec![SlotState::Held { slot: 0, reported_owner: Some(owner()) }]),
        "a written claim did not hand its lock to the lease"
    );
    // A lease is released by its final close, which a spawn's copy delays:
    // a child that inherits a lease keeps its slot.
    assert!(!released, "a dropped lease unlocked a slot that a spawn's copy still holds");
    assert!(relockable(&slot), "the slot stayed locked after its last copy was reaped");
}
