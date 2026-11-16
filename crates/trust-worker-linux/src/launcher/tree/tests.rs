use std::time::Instant;

use trust_process_isolation::Limits;

use super::*;

fn budget(work: u64) -> Budget {
    Budget::new(
        Limits {
            frame_bytes: 4096,
            wire_bytes: 8192,
            allocation_bytes: 8192,
            values: 100,
            work,
            calls: 100,
            live_handles: 64,
            depth: 16,
        },
        Instant::now() + Duration::from_secs(1),
    )
    .unwrap()
}

#[test]
fn finite_parent_values_refuse_unlimited_zero_aliases_and_overflow() {
    assert_eq!(scalar(b"1\n").unwrap(), 1);
    assert_eq!(scalar(b"18446744073709551615\n").unwrap(), u64::MAX);
    for bytes in [b"max\n".as_slice(), b"01\n", b"+1\n", b"1", b"1\n2\n", b"18446744073709551616\n"]
    {
        assert!(scalar(bytes).is_err(), "{bytes:?}");
    }
    // Zero parses but is refused by the actual parent admission.
    let file = File::open("/dev/null").unwrap();
    let b = budget(100_000_000);
    let sibling = b.clone();
    assert!(Tree::create(&file, c"fresh", 0, &b).is_err());
    assert!(sibling.check().is_err());
}

#[test]
fn closure_requires_recursive_empty_and_unfrozen_kernel_event_state() {
    assert!(empty_events(b"populated 0\nfrozen 0\n").unwrap());
    assert!(!empty_events(b"populated 1\nfrozen 0\n").unwrap());
    for bytes in [
        b"populated 0\nfrozen 1\n".as_slice(),
        b"populated 0\n",
        b"populated 00\nfrozen 0\n",
        b"populated 0\nfrozen 0\nextra 0\n",
    ] {
        assert!(empty_events(bytes).is_err());
    }
}

#[test]
fn ordinary_directory_cannot_imitate_delegated_cgroup_and_refusal_is_shared() {
    let file = File::open(std::env::temp_dir()).unwrap();
    let b = budget(100_000_000);
    let sibling = b.clone();
    assert!(Tree::create(&file, c"not-created", 64 * 1024 * 1024, &b).is_err());
    assert!(sibling.check().is_err());
    assert!(Identity::capture(&file, Role::Directory).is_err());
}

#[test]
fn cleanup_prepayment_uses_original_work_and_endpoint_without_refund() {
    let b = budget(100_000_000);
    let sibling = b.clone();
    let deadline = b.deadline();
    let polls = cleanup_reservation(&b).unwrap();
    assert!(polls >= 1 && polls <= 1002);
    assert_eq!(sibling.usage().unwrap().work, polls * 8192);
    assert_eq!(sibling.deadline(), deadline);
    b.cancel();
    assert!(cleanup_reservation(&sibling).is_err());
    assert_eq!(sibling.usage().unwrap().work, polls * 8192);
    // Cleanup may observe its original endpoint after sticky refusal. It may
    // not create positive protocol credit: the ordinary check still refuses.
    assert!(original_endpoint(&sibling).is_ok());
    assert!(sibling.check().is_err());
}

#[test]
fn insufficient_original_work_refuses_cleanup_reservation_before_birth() {
    let b = budget(1);
    assert!(cleanup_reservation(&b).is_err());
    assert_eq!(b.usage().unwrap().work, 0);
    assert!(b.check().is_err());
}
