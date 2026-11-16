use std::os::fd::AsFd as _;
use std::time::{Duration, Instant};

use super::*;
fn check(same_pipe: bool, fetched: bool) {
    let original = Client::new(1).unwrap();
    let held = original.acquire().unwrap();
    let other = if same_pipe {
        let (read, write) = match original.transport_witnesses().unwrap() {
            jobserver::TransportWitnesses::NumericPipe { read, write }
            | jobserver::TransportWitnesses::NamedFifo { read, write, .. } => (read, write),
        };
        Client::from_pipe(read.as_fd(), write.as_fd()).unwrap()
    } else {
        Client::new(1).unwrap()
    };
    let waiter = ReadyWaiter::new(&original).unwrap();
    let result = Arc::clone(&waiter.result);
    let mut admission = ReadyTokenAdmission { waiter: Some(waiter), ..Default::default() };
    assert!(admission.try_acquire(&original).unwrap().is_none());
    let mut held = Some(held);
    if fetched {
        drop(held.take());
        let bound = Instant::now() + Duration::from_secs(5);
        while result.lock().unwrap().is_none() {
            assert!(Instant::now() < bound);
            std::thread::sleep(Duration::from_millis(1));
        }
    }
    let foreign = admission.try_acquire(&other);
    if let Ok(Some(credit)) = &foreign {
        assert!(credit.belongs_to(&original));
        assert!(!credit.belongs_to(&other));
    }
    assert!(foreign.is_err(), "a foreign client polled the original pending waiter");
    drop(held.take());
    let bound = Instant::now() + Duration::from_secs(5);
    let credit = loop {
        if let Some(credit) = admission.try_acquire(&original.clone()).unwrap() {
            break credit;
        }
        assert!(Instant::now() < bound);
        std::thread::sleep(Duration::from_millis(1));
    };
    assert!(credit.belongs_to(&original));
    drop(credit);
    admission.retire_joined().unwrap();
    assert_eq!(original.available().unwrap(), 1);
    assert!(
        admission.try_acquire(&other).is_err(),
        "retirement changed the original pool identity"
    );
}
#[test]
fn pending_waiter_rejects_foreign_and_same_pipe_reimport() {
    check(false, false);
    check(true, false);
}
#[test]
fn ready_guard_cannot_be_returned_as_another_clients_request() {
    check(false, true);
    check(true, true);
}
