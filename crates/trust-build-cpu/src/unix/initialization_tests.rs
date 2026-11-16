// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::fs::OpenOptions;
use std::os::unix::fs::PermissionsExt;
use std::sync::mpsc;
use std::time::Duration;

use super::*;
use crate::tests::kernel_fixture;

fn width(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).unwrap()
}

fn identity(path: &Path) -> (u64, u64) {
    let metadata = std::fs::symlink_metadata(path).unwrap();
    (metadata.dev(), metadata.ino())
}

#[test]
fn late_initializer_contention_returns_would_block_after_observed_absence() {
    let _fixture = kernel_fixture();
    let directory = crate::tests::private_tempdir();
    assert!(Pool::open_existing(directory.path()).unwrap().is_none());

    // The caller has passed the constructor's absence check. A peer now
    // creates the original backing and keeps its actual initialization lock.
    let peer = Pool::open_in(directory.path(), width(1)).unwrap();
    let manifest = peer.path().join("pool");
    let before = (identity(&manifest), std::fs::read(&manifest).unwrap());
    let held =
        OpenOptions::new().read(true).write(true).open(peer.path().join("init.lock")).unwrap();
    held.lock().unwrap();
    let capacity = directory.path().to_owned();
    let (send, receive) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        // Execute the SAME creation helper reached after the initial miss.
        // Calling the public constructor here would only test its early read.
        send.send(Pool::initialize_in(&capacity, width(1), Initialization::Try)).unwrap();
    });
    let result = receive.recv_timeout(Duration::from_secs(60));
    drop(held);
    worker.join().unwrap();
    let error =
        result.expect("nonblocking initialization must finish while peer holds lock").unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::WouldBlock);
    assert_eq!((identity(&manifest), std::fs::read(&manifest).unwrap()), before);

    let existing = Pool::initialize_in(directory.path(), width(1), Initialization::Wait).unwrap();
    assert_eq!(existing.path(), peer.path());
    assert_eq!((identity(&manifest), std::fs::read(&manifest).unwrap()), before);
}

#[test]
fn nonblocking_reopen_preserves_original_identities_width_and_live_leases() {
    let _fixture = kernel_fixture();
    let directory = crate::tests::private_tempdir();
    let pool = Pool::try_open_in(directory.path(), width(2)).unwrap();
    let manifest = pool.path().join("pool");
    let slots = [pool.path().join(slot_name(0)), pool.path().join(slot_name(1))];
    let before = (
        identity(&manifest),
        std::fs::read(&manifest).unwrap(),
        slots.each_ref().map(|p| identity(p)),
    );
    let owner = Owner::current(Some(123));
    let original = pool.try_acquire(owner).unwrap().unwrap();
    let reopened = Pool::try_open_in(directory.path(), width(2)).unwrap();
    let second = reopened.try_acquire(owner).unwrap().unwrap();
    assert!(pool.try_acquire(owner).unwrap().is_none());
    assert_eq!(
        Pool::try_open_in(directory.path(), width(3)).unwrap_err().kind(),
        io::ErrorKind::InvalidData
    );
    assert_eq!(
        (
            identity(&manifest),
            std::fs::read(&manifest).unwrap(),
            slots.each_ref().map(|p| identity(p))
        ),
        before,
    );
    assert!(reopened.snapshot().unwrap().iter().all(|slot| matches!(slot, SlotState::Held { .. })));
    drop((original, second));
    assert!(pool.try_acquire(owner).unwrap().is_some());
}

#[test]
fn nonblocking_constructor_preserves_interrupted_unpublished_backing() {
    let _fixture = kernel_fixture();
    let directory = crate::tests::private_tempdir();
    let partial = directory.path().join(DIRECTORY_NAME);
    DirBuilder::new().mode(0o700).create(&partial).unwrap();
    let slot = partial.join(slot_name(0));
    std::fs::write(&slot, b"unfinished original backing").unwrap();
    std::fs::set_permissions(&slot, std::fs::Permissions::from_mode(0o600)).unwrap();
    let before = (identity(&partial), identity(&slot), std::fs::read(&slot).unwrap());
    assert!(Pool::try_open_in(directory.path(), width(1)).is_err());
    assert_eq!((identity(&partial), identity(&slot), std::fs::read(&slot).unwrap()), before);
    assert_eq!(std::fs::read_dir(&partial).unwrap().count(), 1);
    assert!(!partial.join("init.lock").exists());
    assert!(!partial.join("pool").exists());
}

#[test]
fn nonblocking_constructor_preserves_the_actual_retained_fence() {
    let _fixture = kernel_fixture();
    let directory = crate::tests::private_tempdir();
    let capacity = directory.path().join("retained");
    let retained = crate::RetainedPool::create_private(&capacity, width(1)).unwrap();
    let fence = capacity.join(DIRECTORY_NAME);
    let before = (identity(&fence), std::fs::read(&fence).unwrap());
    assert!(Pool::try_open_in(&capacity, width(1)).is_err());
    assert_eq!((identity(&fence), std::fs::read(&fence).unwrap()), before);
    retained.try_acquire(Owner::current(Some(123))).unwrap().unwrap().settle().unwrap();
}

#[test]
fn nonblocking_constructor_refuses_unsafe_parent_without_repair() {
    let _fixture = kernel_fixture();
    let directory = crate::tests::private_tempdir();
    std::fs::set_permissions(directory.path(), std::fs::Permissions::from_mode(0o777)).unwrap();
    let before = identity(directory.path());
    assert_eq!(
        Pool::try_open_in(directory.path(), width(1)).unwrap_err().kind(),
        io::ErrorKind::PermissionDenied
    );
    assert_eq!(identity(directory.path()), before);
    assert_eq!(std::fs::metadata(directory.path()).unwrap().mode() & 0o777, 0o777);
    assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 0);
}
