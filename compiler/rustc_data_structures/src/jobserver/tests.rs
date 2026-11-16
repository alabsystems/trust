use std::sync::{Weak, mpsc};
use std::time::{Duration, Instant};

use super::*;

const TIMEOUT: Duration = Duration::from_secs(30);

fn assert_callback_finished(state: &Weak<ProxyShared>) {
    // Trust: upstream helper cleanup can return after its bounded best
    // effort to join. Test eventual cleanup, not scheduler latency.
    let deadline = Instant::now() + TIMEOUT;
    while state.strong_count() != 0 {
        assert!(Instant::now() < deadline, "helper did not finish its callback");
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): a process is owed a loan of its own
/// execution only on a bare protocol-1 admission. Every advertisement or other
/// custody locator, even alone, is transport that capture must judge.
#[test]
fn own_execution_is_owed_only_to_a_bare_protocol_one_admission() {
    fn owed(set: &[(&str, &str)]) -> bool {
        early::own_execution_owed(|name| {
            set.iter().find(|(key, _)| *key == name).map(|(_, value)| value.into())
        })
    }
    let bare = [("BUILD_SLOT_CPU_PROTOCOL", "1"), ("BUILD_SLOT_HELD", "1")];
    assert!(owed(&bare));
    // Unrelated variables change nothing.
    assert!(owed(&[bare[0], bare[1], ("CARGO_BUILD_JOBS", "6"), ("RUST_TEST_THREADS", "4")]));
    for refused in [
        &[][..],
        &[("BUILD_SLOT_CPU_PROTOCOL", "1")],
        &[("BUILD_SLOT_HELD", "1")],
        &[("BUILD_SLOT_CPU_PROTOCOL", "2"), ("BUILD_SLOT_HELD", "1")],
        &[("BUILD_SLOT_CPU_PROTOCOL", ""), ("BUILD_SLOT_HELD", "1")],
        &[("BUILD_SLOT_CPU_PROTOCOL", "1"), ("BUILD_SLOT_HELD", "0")],
    ] {
        assert!(!owed(refused), "{refused:?} is not a bare protocol-1 admission");
    }
    for locator in [
        "CARGO_JOBSERVER_HANDOFF",
        "TRUST_CPU_HANDOFF",
        "TRUST_FIXED_CLAIM_HANDOFF_V1",
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        "TRUST_CPU_IMPLICIT_FD",
        "ATERM_SDK_LEASE_V3",
        "ATERM_WORKLOAD_CPU_FDS_V1",
        "ATERM_WORKLOAD_HOST_STORE_FD_V1",
        "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
    ] {
        // Present at all, whatever the value: an empty or auth-free value is
        // still something the capture must judge, never something to replace.
        for value in ["", "-s", "--jobserver-auth=8,9"] {
            assert!(
                !owed(&[bare[0], bare[1], (locator, value)]),
                "{locator}={value:?} is transport"
            );
        }
    }
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): a loan binds libtest to one thread. It
/// narrows `RUST_TEST_THREADS`, an inherited default, so it is made only when
/// the command line, which libtest prefers, chose no other count in any
/// spelling.
#[test]
fn a_loan_is_made_only_for_a_run_that_can_be_one_test_at_a_time() {
    fn admits(args: &[&str]) -> bool {
        test_threads_admit_one(args.iter().map(std::ffi::OsString::from))
    }
    assert!(admits(&[]));
    assert!(admits(&["--exact", "tests::one", "--nocapture"]));
    assert!(admits(&["--quiet", "-Z", "unstable-options", "--format", "json"]));
    assert!(admits(&["--test-threads=1"]));
    assert!(!admits(&["--test-threads=4"]));
    assert!(!admits(&["--test-threads", "1"]));
    assert!(!admits(&["--test-threads=01"]));
    assert!(!admits(&["--test-threads=1", "--test-threads=3"]));
}

#[test]
fn repeated_proxies_release_the_helper_and_its_callback_state() {
    let client = Client::new(1).unwrap();
    let implicit = client.acquire().unwrap();
    for _ in 0..16 {
        let proxy = Proxy::with_client(client.clone());
        let owner = Arc::downgrade(&proxy);
        let callback_state = Arc::downgrade(&proxy.shared);
        let last_owner = Arc::clone(&proxy);
        drop(proxy);
        assert!(owner.upgrade().is_some());
        drop(last_owner);
        assert!(owner.upgrade().is_none(), "helper callback retained its owner");
        assert_callback_finished(&callback_state);
        assert_eq!(client.available().unwrap(), 0, "drop returned the implicit token");
    }
    drop(implicit);
    assert_eq!(client.available().unwrap(), 1);
}

#[test]
fn helper_cleanup_preserves_explicit_and_implicit_tokens() {
    let client = Client::new(2).unwrap();
    let implicit = client.acquire().unwrap();
    let proxy = Proxy::with_client(client.clone());
    let callback_state = Arc::downgrade(&proxy.shared);
    let worker_proxy = Arc::clone(&proxy);
    let (acquired_tx, acquired_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        worker_proxy.acquire_thread();
        acquired_tx.send(()).unwrap();
        release_rx.recv().unwrap();
        worker_proxy.release_thread();
    });
    acquired_rx.recv_timeout(TIMEOUT).unwrap();
    assert_eq!(client.available().unwrap(), 0, "worker did not use the original pool");
    release_tx.send(()).unwrap();
    worker.join().unwrap();
    assert_eq!(client.available().unwrap(), 1);
    proxy.release_thread();
    drop(proxy);
    assert_callback_finished(&callback_state);
    assert_eq!(client.available().unwrap(), 1, "helper changed the implicit reservation");
    drop(implicit);
    assert_eq!(client.available().unwrap(), 2, "helper lost or duplicated a token");
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): wait until `count` threads wait for
/// a token and the helper has `queued` requests it has not started to serve.
fn wait_for_waiters(proxy: &Proxy, count: u16, queued: usize) {
    let deadline = Instant::now() + TIMEOUT;
    loop {
        let pending = proxy.shared.data.lock().pending;
        if pending == count && proxy.queued_helper_requests() == queued {
            return;
        }
        assert!(Instant::now() < deadline, "waiters did not reach {count} with {queued} queued");
        std::thread::yield_now();
    }
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): a proxy on a pool of two tokens, both
/// held by the test, so the pool is empty and a helper request blocks on it.
fn proxy_on_an_empty_pool() -> (Client, Acquired, Acquired, Arc<Proxy>) {
    let client = Client::new(2).unwrap();
    let implicit = client.acquire().unwrap();
    let other = client.acquire().unwrap();
    let proxy = Proxy::with_client(client.clone());
    (client, implicit, other, proxy)
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): a waiter that is handed a slot
/// leaves behind the request the helper is already serving, blocked on the
/// empty pool. `shutdown` joins that helper: when it returns nothing of the
/// callback is left, with no polling for it, and no token moved.
#[test]
fn shutdown_retires_a_helper_serving_a_stale_request_on_an_empty_pool() {
    let (client, implicit, other, proxy) = proxy_on_an_empty_pool();
    let callback_state = Arc::downgrade(&proxy.shared);
    let worker_proxy = Arc::clone(&proxy);
    let worker = std::thread::spawn(move || {
        worker_proxy.acquire_thread();
        worker_proxy.release_thread();
    });
    // The worker waits and the helper has taken its request.
    wait_for_waiters(&proxy, 1, 0);
    // Hand this thread's slot to the worker. The helper's request is stale.
    proxy.release_thread();
    worker.join().unwrap();
    proxy.acquire_thread();
    proxy.shutdown().unwrap();
    proxy.shutdown().expect("a second shutdown only checks the accounting again");
    drop(proxy);
    assert_eq!(callback_state.strong_count(), 0, "shutdown returned before the helper was joined");
    assert_eq!(client.available().unwrap(), 0, "shutdown moved a token");
    drop(other);
    drop(implicit);
    assert_eq!(client.available().unwrap(), 2, "helper lost or duplicated a token");
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): the same stale request, with a token
/// arriving in the pool while the helper is being retired. The helper either
/// reads it and the callback returns it, or is interrupted first and leaves
/// it; after `shutdown` the token is in the pool every time.
#[test]
fn shutdown_conserves_a_token_that_arrives_for_a_stale_request() {
    let client = Client::new(2).unwrap();
    let implicit = client.acquire().unwrap();
    for round in 0..500 {
        let other = client.acquire().unwrap();
        let proxy = Proxy::with_client(client.clone());
        let callback_state = Arc::downgrade(&proxy.shared);
        let worker_proxy = Arc::clone(&proxy);
        let worker = std::thread::spawn(move || {
            worker_proxy.acquire_thread();
            worker_proxy.release_thread();
        });
        wait_for_waiters(&proxy, 1, 0);
        proxy.release_thread();
        worker.join().unwrap();
        proxy.acquire_thread();
        let returner = std::thread::spawn(move || drop(other));
        proxy.shutdown().unwrap();
        returner.join().unwrap();
        drop(proxy);
        assert_eq!(callback_state.strong_count(), 0);
        assert_eq!(client.available().unwrap(), 1, "round {round}: a token was lost or duplicated");
    }
    drop(implicit);
    assert_eq!(client.available().unwrap(), 2);
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): handing a slot to a waiter withdraws
/// that waiter's helper request while the helper has not started on it.
#[test]
fn a_handoff_withdraws_the_queued_helper_request() {
    let (client, implicit, other, proxy) = proxy_on_an_empty_pool();
    let workers: Vec<_> = (0..2u16)
        .map(|index| {
            let worker_proxy = Arc::clone(&proxy);
            let worker = std::thread::spawn(move || {
                worker_proxy.acquire_thread();
                worker_proxy.release_thread();
            });
            // The helper serves the first request, blocked on the empty pool,
            // so the second one stays queued.
            wait_for_waiters(&proxy, index + 1, usize::from(index));
            worker
        })
        .collect();
    proxy.release_thread();
    assert_eq!(proxy.queued_helper_requests(), 0, "the handoff left its request queued");
    // The first worker hands its slot to the second. No request is filed.
    for worker in workers {
        worker.join().unwrap();
    }
    assert_eq!(proxy.queued_helper_requests(), 0);
    assert_eq!(client.available().unwrap(), 0, "a handoff took a token from the pool");
    proxy.acquire_thread();
    proxy.shutdown().unwrap();
    drop((other, implicit));
    assert_eq!(client.available().unwrap(), 2);
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): `shutdown` refuses when a thread
/// still holds a pool token, and returns that token before it reports.
#[test]
fn shutdown_refuses_unsettled_accounting_and_returns_what_it_holds() {
    let client = Client::new(2).unwrap();
    let implicit = client.acquire().unwrap();
    let proxy = Proxy::with_client(client.clone());
    let worker_proxy = Arc::clone(&proxy);
    // The worker takes the second token and never releases its slot.
    std::thread::spawn(move || worker_proxy.acquire_thread()).join().unwrap();
    assert_eq!(client.available().unwrap(), 0);
    let error = proxy.shutdown().unwrap_err();
    assert!(error.contains("2 threads counted as working"), "{error}");
    assert!(error.contains("1 pool tokens held"), "{error}");
    assert_eq!(client.available().unwrap(), 1, "the held token was not returned");
    // What was given back is not reported, or counted as working, again.
    proxy.shutdown().unwrap();
    drop(implicit);
    assert_eq!(client.available().unwrap(), 2);
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): an admission failure the helper
/// reported while no thread waited is reported by `shutdown`, once.
#[test]
fn shutdown_reports_an_admission_failure_nobody_waited_for() {
    let proxy = Proxy::with_client(Client::new(0).unwrap());
    proxy.shared.failed("fixture admission failure".into());
    let error = proxy.shutdown().unwrap_err();
    assert!(error.contains("fixture admission failure"), "{error}");
    assert!(!error.contains("unsettled"), "{error}");
    proxy.shutdown().unwrap();
}

/// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): a thread that needs a token after the
/// helper was retired fails at once instead of waiting for one forever.
#[test]
fn a_request_after_shutdown_fails_instead_of_waiting() {
    let client = Client::new(1).unwrap();
    let implicit = client.acquire().unwrap();
    let proxy = Proxy::with_client(client.clone());
    proxy.shutdown().unwrap();
    // The creating thread still counts as working, so this needs the helper.
    let late = Arc::clone(&proxy);
    let failed = std::thread::spawn(move || late.acquire_thread()).join();
    assert!(failed.is_err());
    // Taking back the process's own token needs no helper.
    proxy.release_thread();
    proxy.acquire_thread();
    proxy.shutdown().unwrap();
    drop(implicit);
    assert_eq!(client.available().unwrap(), 1);
}

#[test]
fn failed_admission_wakes_a_waiting_worker() {
    let proxy = Proxy::with_client(Client::new(0).unwrap());
    let worker = Arc::clone(&proxy);
    let (done, result) = mpsc::channel();
    let thread = std::thread::spawn(move || {
        let failed =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| worker.acquire_thread()));
        done.send(failed.is_err()).unwrap();
    });
    let deadline = Instant::now() + TIMEOUT;
    while proxy.shared.data.lock().pending == 0 {
        assert!(Instant::now() < deadline, "worker did not start waiting");
        std::thread::yield_now();
    }
    proxy.shared.failed("fixture admission failure".into());
    assert!(result.recv_timeout(TIMEOUT).unwrap());
    thread.join().unwrap();
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): a strict context with no GNU
/// pool admits exactly the fixed metadata queries, in each getopts spelling
/// of them, and nothing that could compile, read input or widen the query.
#[test]
fn bounded_metadata_queries_admit_each_spelling_and_nothing_wider() {
    fn query(args: &[&str]) -> bool {
        early::bounded_metadata_query(args.iter().map(std::ffi::OsString::from))
    }
    for admitted in [
        &["-V"][..],
        &["-vV"],
        &["--version"],
        &["--print=sysroot"],
        &["--print", "sysroot"],
        &["--print=target-list"],
        &["--print", "target-list"],
        &["--resource-capabilities"],
    ] {
        assert!(query(admitted), "{admitted:?} is a bounded metadata query");
    }
    for refused in [
        &[][..],
        &["-"],
        &["lib.rs"],
        &["-v"],
        &["-Vv"],
        &["-V="],
        &["-V", "-"],
        &["-V", "--crate-type=lib"],
        &["--version", "lib.rs"],
        &["--print"],
        &["--print", "cfg"],
        &["--print", "sysroot", "lib.rs"],
        &["--print", "sysroot", "--print", "target-list"],
        &["--print=sysroot", "sysroot"],
        &["--print=cfg"],
        &["@args"],
        &["sysroot", "--print"],
        &["--resource-capabilities", "--extra"],
    ] {
        assert!(!query(refused), "{refused:?} is not a bounded metadata query");
    }
}
