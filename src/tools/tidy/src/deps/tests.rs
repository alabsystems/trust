// Trust: nested dependency scheduling must finish within the shared permit limit.
use std::num::NonZeroUsize;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, mpsc};
use std::time::Duration;

use super::for_each_with_parent_permit;
use crate::Semaphore;

fn check_schedule(permits: usize, peer_permits: usize) {
    let sem = Arc::new(Semaphore::new(NonZeroUsize::new(permits).unwrap()));
    let (done, finished) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let _parent = sem.acquire();
        let _peers: Vec<_> = (0..peer_permits).map(|_| sem.acquire()).collect();
        let active = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let seen: Vec<_> = (0..17).map(|_| AtomicUsize::new(0)).collect();
        for_each_with_parent_permit(&seen, &sem, |seen| {
            let running = active.fetch_add(1, Ordering::SeqCst) + 1;
            peak.fetch_max(running, Ordering::SeqCst);
            std::thread::sleep(Duration::from_millis(2));
            seen.fetch_add(1, Ordering::SeqCst);
            active.fetch_sub(1, Ordering::SeqCst);
        });
        assert!(peak.load(Ordering::SeqCst) <= permits - peer_permits);
        assert!(seen.iter().all(|seen| seen.load(Ordering::SeqCst) == 1));
        done.send(()).unwrap();
    });
    finished.recv_timeout(Duration::from_secs(5)).expect("nested checks did not finish");
    worker.join().unwrap();
}

#[test]
fn one_permit_checks_every_workspace() {
    check_schedule(1, 0);
}

#[test]
fn exhausted_peer_permits_make_progress_inline() {
    check_schedule(4, 3);
}

#[test]
fn parallel_checks_keep_the_shared_limit() {
    check_schedule(4, 0);
}
