// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::num::NonZeroU32;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Barrier, mpsc};
use std::time::{Duration, Instant};

use crate::{Owner, Pool, SlotState};

fn width(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).unwrap()
}

#[test]
fn shrinking_pauses_new_admission_without_revoking_workers_and_recovers() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let pool = Pool::open_in(dir.path(), width(6)).unwrap();
    assert!(pool.try_acquire_with_limit(Owner::current(None), 0).unwrap().is_none());
    let mut held: Vec<_> = (0..4)
        .map(|_| pool.try_acquire_with_limit(Owner::current(None), 6).unwrap().unwrap())
        .collect();
    let slots: Vec<_> = held.iter().map(crate::Lease::slot).collect();
    assert!(pool.try_acquire_with_limit(Owner::current(None), 2).unwrap().is_none());
    assert_eq!(
        pool.snapshot().unwrap().iter().filter(|s| matches!(s, SlotState::Held { .. })).count(),
        4
    );
    assert_eq!(slots, held.iter().map(crate::Lease::slot).collect::<Vec<_>>());
    held.truncate(2);
    assert!(pool.try_acquire_with_limit(Owner::current(None), 2).unwrap().is_none());
    held.truncate(1);
    held.push(pool.try_acquire_with_limit(Owner::current(None), 2).unwrap().unwrap());
    held.push(pool.try_acquire_with_limit(Owner::current(None), 6).unwrap().unwrap());
    assert_eq!(held.len(), 3);
}

#[test]
fn competing_roots_cannot_race_past_the_measured_limit() {
    // How many refusals inside its own admission transaction a refused root
    // collects before it stops asking.
    const REFUSALS: usize = 16;
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let pool = Pool::open_in(dir.path(), width(16)).unwrap();
    let ready = Arc::new(Barrier::new(16));
    // Set when the hang detector gives up, so that no root keeps asking, and
    // holding its pool's descriptors, once this test fails.
    let abandoned = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    let threads: Vec<_> = (0..16)
        .map(|root| {
            // Separate open descriptions, as in independent compiler roots.
            let pool = Pool::open_in(dir.path(), width(16)).unwrap();
            let ready = Arc::clone(&ready);
            let abandoned = Arc::clone(&abandoned);
            let tx = tx.clone();
            std::thread::spawn(move || {
                ready.wait();
                // This is try_acquire_with_limit(owner, 3), observed. `None`
                // without an observation means another root held the admission
                // transaction, for as long as the scheduler kept it there, and
                // counts for nothing. Only this root's own transaction answers,
                // and each answer is reported: a lease ends its attempt, and so
                // does its REFUSALS-th refusal.
                let mut refusals = 0;
                while !abandoned.load(Ordering::Relaxed) {
                    let mut observed = None;
                    let lease = pool
                        .try_acquire_observed(Owner::current(None), |held| {
                            observed = Some(held);
                            3
                        })
                        .unwrap();
                    match (lease, observed) {
                        (Some(lease), _) => {
                            tx.send((root, Ok(lease))).unwrap();
                            return;
                        }
                        (None, Some(held)) => {
                            tx.send((root, Err(held))).unwrap();
                            refusals += 1;
                            if refusals == REFUSALS {
                                return;
                            }
                        }
                        (None, None) => {}
                    }
                    std::thread::yield_now();
                }
            })
        })
        .collect();
    drop(tx);
    // Each root's lease, retained until every contender has finished, and the
    // held count of each refusal it was given, in order.
    let mut roots: Vec<(Option<crate::Lease>, Vec<u32>)> =
        std::iter::repeat_with(|| (None, Vec::new())).take(16).collect();
    loop {
        match rx.recv_timeout(Duration::from_secs(60)) {
            Ok((root, Ok(lease))) => assert!(roots[root].0.replace(lease).is_none()),
            Ok((root, Err(held))) => roots[root].1.push(held),
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                // Stop every root, and give each a bounded time to leave and
                // close its pool under the kernel fixture. Not an unbounded
                // join: a root stuck inside an attempt would turn this
                // detector back into a hang.
                abandoned.store(true, Ordering::Relaxed);
                let stopped = Instant::now() + Duration::from_secs(10);
                while !threads.iter().all(std::thread::JoinHandle::is_finished)
                    && Instant::now() < stopped
                {
                    std::thread::sleep(Duration::from_millis(10));
                }
                panic!("test hang detector: no admission transaction answered")
            }
        }
    }
    for thread in threads {
        thread.join().unwrap();
    }
    assert_eq!(roots.iter().filter(|(lease, _)| lease.is_some()).count(), 3);
    // Three roots were admitted without a refusal. Each other root kept asking
    // after the limit was reached and was refused every time, inside its own
    // transaction, with exactly the limit held.
    let mut answers: Vec<_> =
        roots.iter().map(|(lease, refusals)| (lease.is_some(), refusals.clone())).collect();
    answers.sort();
    let expected: Vec<_> = std::iter::repeat_n((false, vec![3; REFUSALS]), 13)
        .chain(std::iter::repeat_n((true, Vec::new()), 3))
        .collect();
    assert_eq!(answers, expected);
    assert_eq!(
        pool.snapshot().unwrap().iter().filter(|s| matches!(s, SlotState::Held { .. })).count(),
        3
    );
}

#[test]
fn trusted_inherited_continuation_reuses_credit_while_unrelated_held_open_refuses() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let pool = Pool::open_in(dir.path(), width(1)).unwrap();
    let original = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let unrelated = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(pool.path().join("slot-00000000"))
        .unwrap();
    assert!(pool.adopt_inherited(unrelated).is_err());
    let inherited = pool.adopt_inherited(original.try_clone().unwrap().into_file()).unwrap();
    drop(original);
    assert!(pool.try_acquire(Owner::current(None)).unwrap().is_none());
    drop(inherited);
    let stale = std::fs::File::open(pool.path().join("slot-00000000")).unwrap();
    assert!(pool.adopt_inherited(stale).is_err());
    assert!(pool.try_acquire(Owner::current(None)).unwrap().is_some());
}

#[test]
fn busy_inheritance_keeps_the_original_descriptor_and_policy_veto_is_nonmutating() {
    let _fixture = crate::tests::kernel_fixture();
    let dir = crate::tests::private_tempdir();
    let pool = Pool::open_in(dir.path(), width(2)).unwrap();
    let original = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let file = original.try_clone().unwrap().into_file();
    let lock = std::fs::File::open(pool.path().join("pool")).unwrap();
    lock.lock().unwrap();
    assert!(pool.try_adopt_inherited(&file, |_| 2).unwrap().is_none());
    drop(lock);
    assert!(pool.try_adopt_inherited(&file, |_| 0).unwrap().is_none());
    assert!(pool.adopt_inherited_until(&file, std::time::Instant::now()).is_err());
    drop(original);
    assert_eq!(
        pool.snapshot().unwrap().iter().filter(|s| matches!(s, SlotState::Held { .. })).count(),
        1
    );
    drop(file);
    assert!(pool.snapshot().unwrap().iter().all(|s| matches!(s, SlotState::Available { .. })));
}
