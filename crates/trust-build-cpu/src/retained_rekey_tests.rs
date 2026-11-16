use std::os::unix::fs::PermissionsExt as _;

use super::*;
use crate::recovery_material::{RecoveryAuthority, RecoveryMaterial};

fn plan(root: &Path, leaf: &str, context: [u8; 32]) -> PreparedRecovery {
    std::fs::set_permissions(root, std::fs::Permissions::from_mode(0o700)).unwrap();
    RecoveryMaterial::mint([3; 32], Owner::current(None), NonZeroU32::new(1).unwrap(), context)
        .unwrap()
        .persist(&root.canonicalize().unwrap(), leaf)
        .unwrap()
}

#[derive(Clone, Copy)]
enum Failure {
    Prefix,
    LostAck,
}

#[test]
fn original_rekey_retries_only_its_own_partial_or_lost_ack_and_never_frees() {
    for failure in [Failure::Prefix, Failure::LostAck] {
        let root = crate::tests::private_tempdir();
        let pool =
            RetainedPool::create_private(&root.path().join("pool"), NonZeroU32::new(1).unwrap())
                .unwrap();
        let mut old = plan(root.path(), "old", [7; 32]);
        let unit = old.take_units().unwrap().pop().unwrap();
        let mut held = pool
            .try_acquire_recoverable(old.owner(), old.width(), &[3; 32], &old.context(), &unit)
            .unwrap()
            .unwrap();
        let original = held.identity().unwrap();
        let mut next = plan(root.path(), "next", [8; 32]);
        let mut wrong = plan(root.path(), "wrong", [9; 32]);
        assert!(
            held.rekey_with([3; 32], &mut next, |file, text| {
                match failure {
                    Failure::Prefix => {
                        file.seek(SeekFrom::Start(0))?;
                        file.set_len(0)?;
                        file.write_all(&text.as_bytes()[..13])?;
                        file.sync_all()?;
                    }
                    Failure::LostAck => write_record(file, text)?,
                }
                Err(io::Error::other("original native write/ACK refused"))
            })
            .is_err()
        );
        assert!(held.identity().is_err(), "pending transfer cannot publish a usable identity");
        assert!(held.rekey_recoverable([3; 32], &mut wrong).is_err());
        wrong.validate_issuance([3; 32]).unwrap();
        held.rekey_recoverable([3; 32], &mut next).unwrap();
        let moved = held.identity().unwrap();
        assert_eq!(moved.slot, original.slot);
        assert_eq!(moved.file, original.file);
        assert_ne!(moved.nonce, original.nonce);
        assert!(pool.try_acquire(Owner::current(None)).unwrap().is_none());
        drop(held); // Original occupied debt survives losing the live owner.
        drop(old);
        drop(next);
        drop(wrong);
        let directory = root.path().canonicalize().unwrap();
        let former =
            pool.restore_original(RecoveryAuthority::open(&directory, "old").unwrap()).unwrap();
        assert_eq!(former.retained_units(), 0, "old scope key cannot settle the rebound unit");
        former.settle().unwrap(); // No execution was ever exported in this fixture.
        let current =
            pool.restore_original(RecoveryAuthority::open(&directory, "next").unwrap()).unwrap();
        assert_eq!(current.retained_units(), 1);
        current.settle().unwrap(); // Same genuine lexical non-use.
        assert!(pool.try_acquire(Owner::current(None)).unwrap().is_some());
    }
}

#[test]
fn original_rekey_refuses_fixed_v1_and_foreign_domain_before_consuming_keys() {
    let root = crate::tests::private_tempdir();
    let pool = RetainedPool::create_private(&root.path().join("pool"), NonZeroU32::new(1).unwrap())
        .unwrap();
    let mut legacy = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let mut next = plan(root.path(), "next", [8; 32]);
    let before = legacy.identity().unwrap();
    assert!(legacy.rekey_recoverable([3; 32], &mut next).is_err());
    next.validate_issuance([3; 32]).unwrap();
    assert_eq!(legacy.identity().unwrap(), before);
    legacy.settle().unwrap(); // Actual unexported original capability.
    let mut original = plan(root.path(), "original", [7; 32]);
    let unit = original.take_units().unwrap().pop().unwrap();
    let mut held = pool
        .try_acquire_recoverable(
            original.owner(),
            original.width(),
            &[3; 32],
            &original.context(),
            &unit,
        )
        .unwrap()
        .unwrap();
    let before = held.identity().unwrap();
    assert!(held.rekey_recoverable([4; 32], &mut next).is_err());
    next.validate_issuance([3; 32]).unwrap();
    assert_eq!(held.identity().unwrap(), before);
    held.settle().unwrap(); // No execution/export occurred.
}
