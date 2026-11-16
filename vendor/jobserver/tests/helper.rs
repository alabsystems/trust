use jobserver::Client;
use std::sync::atomic::*;
use std::sync::*;

macro_rules! t {
    ($e:expr) => {
        match $e {
            Ok(e) => e,
            Err(e) => panic!("{} failed with {}", stringify!($e), e),
        }
    };
}

#[test]
fn helper_smoke() {
    let client = t!(Client::new(1));
    drop(client.clone().into_helper_thread(|_| ()).unwrap());
    drop(client.clone().into_helper_thread(|_| ()).unwrap());
    drop(client.clone().into_helper_thread(|_| ()).unwrap());
    drop(client.clone().into_helper_thread(|_| ()).unwrap());
    drop(client.clone().into_helper_thread(|_| ()).unwrap());
    drop(client.into_helper_thread(|_| ()).unwrap());
}

#[test]
fn acquire() {
    let (tx, rx) = mpsc::channel();
    let client = t!(Client::new(1));
    let helper = client
        .into_helper_thread(move |a| drop(tx.send(a)))
        .unwrap();
    assert!(rx.try_recv().is_err());
    helper.request_token();
    rx.recv().unwrap().unwrap();
    helper.request_token();
    rx.recv().unwrap().unwrap();

    helper.request_token();
    helper.request_token();
    rx.recv().unwrap().unwrap();
    rx.recv().unwrap().unwrap();

    helper.request_token();
    helper.request_token();
    drop(helper);
}

#[test]
fn prompt_shutdown() {
    for _ in 0..100 {
        let client = jobserver::Client::new(4).unwrap();
        let count = Arc::new(AtomicU32::new(0));
        let count2 = count.clone();
        let tokens = Arc::new(Mutex::new(Vec::new()));
        let helper = client
            .into_helper_thread(move |token| {
                tokens.lock().unwrap().push(token);
                count2.fetch_add(1, Ordering::SeqCst);
            })
            .unwrap();

        // Request more tokens than what are available.
        for _ in 0..5 {
            helper.request_token();
        }
        // Wait for at least some of the requests to finish.
        while count.load(Ordering::SeqCst) < 3 {
            std::thread::yield_now();
        }
        // Drop helper
        let t = std::time::Instant::now();
        drop(helper);
        let d = t.elapsed();
        assert!(d.as_secs_f64() < 0.5);
    }
}

// Trust: the tests below cover `HelperThread::shutdown_blocking`,
// `cancel_request` and `queued_requests` (see TRUST-PATCH.md).

const TRUST_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(60);

/// Wait until the helper has taken every queued request, so that it is
/// serving one (blocked on the empty pool) and none is left to withdraw.
fn trust_wait_until_serving(helper: &jobserver::HelperThread) {
    let deadline = std::time::Instant::now() + TRUST_TIMEOUT;
    while helper.queued_requests() != 0 {
        assert!(
            std::time::Instant::now() < deadline,
            "helper did not take its request"
        );
        std::thread::yield_now();
    }
}

/// Run `f` on another thread and fail, instead of hanging the test run, if it
/// does not return.
fn trust_within_timeout<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    let thread = std::thread::spawn(move || drop(tx.send(f())));
    let value = rx
        .recv_timeout(TRUST_TIMEOUT)
        .expect("helper shutdown did not return");
    thread.join().unwrap();
    value
}

#[test]
fn shutdown_blocking_joins_a_helper_blocked_on_an_empty_pool() {
    for _ in 0..50 {
        let client = t!(Client::new(0));
        let calls = Arc::new(AtomicU32::new(0));
        let calls2 = calls.clone();
        let helper = client
            .clone()
            .into_helper_thread(move |_| {
                calls2.fetch_add(1, Ordering::SeqCst);
            })
            .unwrap();
        helper.request_token();
        trust_wait_until_serving(&helper);
        trust_within_timeout(move || helper.shutdown_blocking()).unwrap();
        // The thread is joined, so its callback and everything the callback
        // owns are gone: no polling is needed to observe that.
        assert_eq!(Arc::strong_count(&calls), 1);
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(client.available().unwrap(), 0);
    }
}

#[cfg(unix)]
#[test]
fn shutdown_blocking_joins_a_helper_blocked_on_an_empty_fifo() {
    use std::os::unix::ffi::OsStrExt;

    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("credits");
    let name = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
    // SAFETY: creates only a new FIFO inside this test's private directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    for _ in 0..50 {
        let client = t!(Client::from_fifo(&path));
        let state = Arc::new(());
        let state2 = state.clone();
        let helper = client
            .clone()
            .into_helper_thread(move |_| {
                let _ = &state2;
            })
            .unwrap();
        helper.request_token();
        trust_wait_until_serving(&helper);
        trust_within_timeout(move || helper.shutdown_blocking()).unwrap();
        assert_eq!(Arc::strong_count(&state), 1);
        assert_eq!(client.available().unwrap(), 0);
    }
}

#[test]
fn shutdown_blocking_conserves_a_token_that_arrives_while_it_runs() {
    let client = t!(Client::new(1));
    for _ in 0..500 {
        let held = client.acquire().unwrap();
        let received = Arc::new(Mutex::new(Vec::new()));
        let received2 = received.clone();
        let helper = client
            .clone()
            .into_helper_thread(move |token| received2.lock().unwrap().push(token))
            .unwrap();
        helper.request_token();
        trust_wait_until_serving(&helper);
        // The pool is empty and the helper is waiting on it. Return the token
        // while the helper is being retired: the helper either reads it and
        // hands it to the callback, or is interrupted and leaves it in the
        // pool. It is never held by a thread that no longer exists.
        let returner = std::thread::spawn(move || drop(held));
        trust_within_timeout(move || helper.shutdown_blocking()).unwrap();
        returner.join().unwrap();
        let received = Arc::try_unwrap(received)
            .expect("the joined helper still owns its callback")
            .into_inner()
            .unwrap();
        assert!(received.len() <= 1);
        assert_eq!(client.available().unwrap(), 1 - received.len());
        for token in received {
            drop(token.unwrap());
        }
        assert_eq!(client.available().unwrap(), 1);
    }
}

#[test]
fn cancel_request_withdraws_only_a_request_not_yet_served() {
    let client = t!(Client::new(0));
    let calls = Arc::new(AtomicU32::new(0));
    let calls2 = calls.clone();
    let helper = client
        .clone()
        .into_helper_thread(move |_| {
            calls2.fetch_add(1, Ordering::SeqCst);
        })
        .unwrap();
    assert!(!helper.cancel_request());
    helper.request_token();
    trust_wait_until_serving(&helper);
    // The helper is serving the first request and cannot start another.
    helper.request_token();
    helper.request_token();
    assert_eq!(helper.queued_requests(), 2);
    assert!(helper.cancel_request());
    assert!(helper.cancel_request());
    assert_eq!(helper.queued_requests(), 0);
    assert!(
        !helper.cancel_request(),
        "the request being served is not withdrawn"
    );
    // One token satisfies the request being served, and no other is taken.
    client.release_raw().unwrap();
    client.release_raw().unwrap();
    let deadline = std::time::Instant::now() + TRUST_TIMEOUT;
    while calls.load(Ordering::SeqCst) == 0 {
        assert!(std::time::Instant::now() < deadline);
        std::thread::yield_now();
    }
    trust_within_timeout(move || helper.shutdown_blocking()).unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    // The callback dropped its token, so both are back.
    assert_eq!(client.available().unwrap(), 2);
}

#[test]
fn shutdown_blocking_reports_a_panicked_callback_and_does_not_wait_for_it() {
    let client = t!(Client::new(1));
    let entered = Arc::new(AtomicBool::new(false));
    let entered2 = entered.clone();
    let helper = client
        .clone()
        .into_helper_thread(move |_token| {
            entered2.store(true, Ordering::SeqCst);
            panic!("fixture callback panic");
        })
        .unwrap();
    helper.request_token();
    let deadline = std::time::Instant::now() + TRUST_TIMEOUT;
    while !entered.load(Ordering::SeqCst) {
        assert!(std::time::Instant::now() < deadline);
        std::thread::yield_now();
    }
    let error = trust_within_timeout(move || helper.shutdown_blocking()).unwrap_err();
    assert!(error.to_string().contains("panicked"), "{error}");
    // Unwinding dropped the token the callback was given.
    assert_eq!(client.available().unwrap(), 1);
}

#[cfg(unix)]
#[test]
fn a_helper_started_with_its_interrupt_signal_blocked_can_still_be_retired() {
    let client = t!(Client::new(0));
    trust_within_timeout(move || {
        // SAFETY: changes only this test thread's own signal mask.
        unsafe {
            let mut set: libc::sigset_t = std::mem::zeroed();
            libc::sigemptyset(&mut set);
            libc::sigaddset(&mut set, libc::SIGUSR1);
            assert_eq!(
                libc::pthread_sigmask(libc::SIG_BLOCK, &set, std::ptr::null_mut()),
                0
            );
        }
        // The helper thread inherits this thread's mask.
        let helper = client.into_helper_thread(|_| ()).unwrap();
        helper.request_token();
        trust_wait_until_serving(&helper);
        helper.shutdown_blocking()
    })
    .unwrap();
}

/// Trust: what `shutdown_blocking` adds over the bounded `shutdown`. A helper
/// that holds a token for longer than the bounded join waits (about a second)
/// is abandoned by `shutdown`, still holding it: a process that exits then
/// loses the token. `shutdown_blocking` returns only when the helper has
/// handed the token on.
#[cfg(unix)]
#[test]
fn only_shutdown_blocking_outwaits_a_helper_that_holds_a_token_for_over_a_second() {
    const HELD_FOR: std::time::Duration = std::time::Duration::from_millis(1500);

    /// A helper whose callback keeps its token until `gate` is opened and
    /// only then returns it to the pool.
    fn holding_helper(
        client: &Client,
    ) -> (jobserver::HelperThread, mpsc::Sender<()>, mpsc::Receiver<()>) {
        let (gate, opened) = mpsc::channel::<()>();
        let (entered_tx, entered) = mpsc::channel();
        let helper = client
            .clone()
            .into_helper_thread(move |token| {
                let token = token.unwrap();
                entered_tx.send(()).unwrap();
                drop(opened.recv_timeout(TRUST_TIMEOUT));
                drop(token);
            })
            .unwrap();
        helper.request_token();
        entered.recv_timeout(TRUST_TIMEOUT).unwrap();
        (helper, gate, entered)
    }

    let client = t!(Client::new(1));

    // Bounded: gives up with the token still inside the helper thread.
    let (helper, gate, _entered) = holding_helper(&client);
    let error = trust_within_timeout(move || helper.shutdown()).unwrap_err();
    assert!(error.to_string().contains("unknown"), "{error}");
    assert_eq!(
        client.available().unwrap(),
        0,
        "the abandoned helper still holds the token"
    );
    gate.send(()).unwrap();
    let deadline = std::time::Instant::now() + TRUST_TIMEOUT;
    while client.available().unwrap() != 1 {
        assert!(std::time::Instant::now() < deadline);
        std::thread::sleep(std::time::Duration::from_millis(1));
    }

    // Unbounded: returns after the helper has handed the token on, not before.
    let (helper, gate, _entered) = holding_helper(&client);
    let start = std::time::Instant::now();
    let opener = std::thread::spawn(move || {
        std::thread::sleep(HELD_FOR);
        gate.send(()).unwrap();
    });
    trust_within_timeout(move || helper.shutdown_blocking()).unwrap();
    assert!(start.elapsed() >= HELD_FOR, "returned while the helper held the token");
    assert_eq!(client.available().unwrap(), 1);
    opener.join().unwrap();
}
