//! Actual local scheduler controls for the workload assignment algorithm.
//! These private fixtures create no authenticated host, workload CPU grant or
//! bank return; production selects this algorithm only after original adoption.

use std::sync::mpsc;
use std::time::{Duration, Instant};

use super::super::{Client, Proxy};
use super::*;

fn fixture(width: usize) -> (Client, Arc<Proxy>) {
    let client = Client::new(width).unwrap();
    let proxy =
        Proxy::build_with_ownership(client.clone(), Some(native_park::Registry::new()), true);
    (client, proxy)
}

#[test]
fn releasing_primary_does_not_return_another_threads_extra() {
    let (client, proxy) = fixture(1);
    let (entered, wait_entered) = mpsc::channel();
    let (release, wait_release) = mpsc::channel();
    let other = proxy.clone();
    let worker = std::thread::spawn(move || {
        other.acquire_thread();
        entered.send(()).unwrap();
        wait_release.recv().unwrap();
        other.release_thread();
    });
    wait_entered.recv_timeout(Duration::from_secs(30)).unwrap();
    assert_eq!(client.available().unwrap(), 0);
    proxy.release_thread();
    assert_eq!(client.available().unwrap(), 0, "primary release returned a different task's extra");
    assert!(proxy.shared.data.lock().workload.as_ref().unwrap().implicit_available());
    release.send(()).unwrap();
    worker.join().unwrap();
    assert_eq!(client.available().unwrap(), 1);
    let data = proxy.shared.data.lock();
    assert_eq!(data.used, 0);
    assert!(data.workload.as_ref().unwrap().matches(data.active.as_ref().unwrap()));
}

#[test]
fn a_waiting_task_continues_on_the_original_primary_without_creating_tokens() {
    let (client, proxy) = fixture(0);
    let other = proxy.clone();
    let worker = std::thread::spawn(move || {
        other.acquire_thread();
        other.release_thread();
    });
    let deadline = Instant::now() + Duration::from_secs(30);
    while proxy.shared.data.lock().pending == 0 {
        assert!(Instant::now() < deadline, "workload task never waited");
        std::thread::yield_now();
    }
    proxy.release_thread();
    worker.join().unwrap();
    assert_eq!(client.available().unwrap(), 0, "handoff invented a GNU token");
    assert_eq!(proxy.shared.data.lock().used, 0);
    assert_eq!(proxy.shared.data.lock().pending, 0);
}
