use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, mpsc};

use super::*;

struct Credit(Arc<AtomicBool>);
impl Drop for Credit {
    fn drop(&mut self) {
        self.0.store(true, Ordering::Release);
    }
}

#[test]
fn notification_does_not_release_the_actual_workers_credit_before_join() {
    let retired = Arc::new(AtomicBool::new(false));
    let (notified, notice) = mpsc::channel();
    let (release, wait) = mpsc::channel();
    let thread = std::thread::spawn(move || {
        notified.send(std::thread::current().id()).unwrap();
        wait.recv().unwrap();
    });
    let mut workers = Workers::new();
    workers.start(thread, Some(Credit(retired.clone())));
    let id = notice.recv().unwrap();
    let (joining, joined) = mpsc::channel();
    let coordinator = std::thread::spawn(move || {
        joining.send(()).unwrap();
        let credit = workers.finish(id).unwrap().unwrap();
        assert!(workers.is_empty());
        credit
    });
    joined.recv().unwrap();
    assert!(!retired.load(Ordering::Acquire));
    release.send(()).unwrap();
    let credit = coordinator.join().unwrap();
    assert!(!retired.load(Ordering::Acquire));
    drop(credit);
    assert!(retired.load(Ordering::Acquire));
}

#[test]
fn fresh_extra_funds_only_the_actual_implicit_worker_without_returning_it() {
    let retired = Arc::new(AtomicBool::new(false));
    let thread = std::thread::spawn(|| {});
    let id = thread.thread().id();
    let mut workers = Workers::new();
    workers.start(thread, None);
    workers.fund_implicit(Credit(retired.clone()));
    assert!(!retired.load(Ordering::Acquire));
    let credit = workers.finish(id).unwrap().unwrap();
    assert!(workers.is_empty());
    assert!(!retired.load(Ordering::Acquire));
    drop(credit);
    assert!(retired.load(Ordering::Acquire));
    assert!(workers.finish(id).is_err());
}

#[test]
fn coordinator_unwind_keeps_sibling_credit_until_that_original_worker_joins() {
    use std::time::Duration;
    let retired = Arc::new(AtomicBool::new(false));
    let (release, wait_release) = mpsc::channel();
    let (finished, wait_finished) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        wait_release.recv().unwrap();
        finished.send(()).unwrap();
    });
    let mut workers = Workers::new();
    workers.start(worker, Some(Credit(retired.clone())));
    let (dropping, wait_dropping) = mpsc::channel();
    let (dropped, wait_dropped) = mpsc::channel();
    let coordinator = std::thread::spawn(move || {
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _workers = workers;
            dropping.send(()).unwrap();
            panic!("owned coordinator unwind control");
        }));
        assert!(unwind.is_err());
        dropped.send(()).unwrap();
    });
    wait_dropping.recv_timeout(Duration::from_secs(30)).unwrap();
    let returned_early = wait_dropped.recv_timeout(Duration::from_millis(100)).is_ok();
    let retired_early = retired.load(Ordering::Acquire);
    // Always let our actual fixture worker finish, including on the RED image.
    release.send(()).unwrap();
    wait_finished.recv_timeout(Duration::from_secs(30)).unwrap();
    coordinator.join().unwrap();
    assert!(!returned_early, "coordinator detached a still-running sibling");
    assert!(!retired_early, "coordinator returned the sibling's credit before join");
    assert!(retired.load(Ordering::Acquire));
}
