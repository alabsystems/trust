use std::time::{Duration, Instant};

use super::*;
#[test]
fn joined_ready_retirement_closes_pending_and_fetched_original_guards() {
    // Actual GNU pipe/helper lifetimes only; no native grant or Full
    // constructor is fabricated by this low-level queue restriction test.
    for fetched in [false, true] {
        let original = Client::new(1).unwrap();
        let implicit = original.acquire().unwrap();
        let waiter = ReadyWaiter::new(&original).unwrap();
        let result = Arc::clone(&waiter.result);
        let mut admission = ReadyTokenAdmission { waiter: Some(waiter), ..Default::default() };
        assert!(admission.try_acquire(&original).unwrap().is_none());
        if fetched {
            drop(implicit);
            let deadline = Instant::now() + Duration::from_secs(5);
            while result.lock().unwrap().is_none() {
                assert!(Instant::now() < deadline, "actual helper never delivered its credit");
                std::thread::sleep(Duration::from_millis(1));
            }
            assert_eq!(original.available().unwrap(), 0);
            admission.retire_joined().unwrap();
            assert_eq!(original.available().unwrap(), 1);
        } else {
            admission.retire_joined().unwrap();
            assert_eq!(original.available().unwrap(), 0);
            drop(implicit);
            assert_eq!(original.available().unwrap(), 1);
        }
        assert!(admission.waiter.is_none());
        assert!(result.lock().unwrap().is_none());
    }
}

#[test]
fn waiter_drop_waits_for_the_actual_unpublished_callback_before_return() {
    struct Release(Option<std::sync::mpsc::Sender<()>>);
    impl Drop for Release {
        fn drop(&mut self) {
            if let Some(send) = self.0.take() {
                let _ = send.send(());
            }
        }
    }
    let original = Client::new(1).unwrap();
    let result = Arc::new(Mutex::new(None));
    let returned = Arc::clone(&result);
    let (entered, observed) = std::sync::mpsc::channel();
    let (release, wait) = std::sync::mpsc::channel();
    let release = Release(Some(release));
    let helper = original
        .clone()
        .into_helper_thread(move |credit| {
            entered.send(()).unwrap();
            wait.recv().unwrap();
            *returned.lock().unwrap() = Some(credit);
        })
        .unwrap();
    helper.request_token();
    observed.recv_timeout(Duration::from_secs(5)).unwrap();
    let waiter = ReadyWaiter { helper: Some(helper), result, outstanding: true };
    let (done, completion) = std::sync::mpsc::channel();
    let closing = std::thread::spawn(move || {
        drop(waiter);
        done.send(()).unwrap();
    });
    // The old bounded HelperThread::drop returned after about one second,
    // although this real callback still held its already-fetched byte.
    let early = completion.recv_timeout(Duration::from_millis(1500));
    assert!(matches!(early, Err(std::sync::mpsc::RecvTimeoutError::Timeout)));
    assert_eq!(original.available().unwrap(), 0);
    drop(release);
    closing.join().unwrap();
    completion.recv_timeout(Duration::from_secs(5)).unwrap();
    assert_eq!(original.available().unwrap(), 1);
}

#[test]
fn checkpoint_retires_blocked_wait_and_returns_racing_credit() {
    let original = Client::new(1).unwrap();
    let held = original.acquire().unwrap();
    let mut admission = ReadyTokenAdmission {
        waiter: Some(ReadyWaiter::new(&original).unwrap()),
        ..Default::default()
    };
    assert!(admission.try_acquire(&original).unwrap().is_none());
    // The pending acquisition must be interruptible even with no token.
    admission.retire();
    assert!(admission.waiter.is_none());
    drop(held);
    let mut admission = ReadyTokenAdmission {
        waiter: Some(ReadyWaiter::new(&original).unwrap()),
        ..Default::default()
    };
    assert!(admission.try_acquire(&original).unwrap().is_none());
    let deadline = Instant::now() + Duration::from_secs(5);
    while admission.waiter.as_ref().unwrap().result.lock().unwrap().is_none() {
        assert!(Instant::now() < deadline, "ready credit was never delivered");
        std::thread::sleep(Duration::from_millis(5));
    }
    // A stopped test frontier must not hide its raced supplementary
    // credit from still-active peers (including their nested builds).
    // Keep it only while an actual pending compiler can still use it.
    admission.retire_stopped_tests(true, true);
    assert!(admission.waiter.is_some());
    admission.retire_stopped_tests(true, false);
    assert!(admission.waiter.is_none());
    // retire() has joined the sole waiter, so the count and following
    // acquire cannot race another reader of this owned original pipe.
    assert_eq!(
        original.available().unwrap(),
        1,
        "stopped test frontier retained its racing credit"
    );
    let returned = original.acquire().unwrap();
    assert_eq!(original.available().unwrap(), 0);
    drop(returned);
    assert_eq!(original.available().unwrap(), 1);
}
