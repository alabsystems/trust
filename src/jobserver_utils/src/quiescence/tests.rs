//! Actual GNU/helper controls only, never native compiler/Root authority.
use std::sync::mpsc;
use std::time::{Duration, Instant};

use super::*;

fn until(mut condition: impl FnMut() -> bool) {
    let end = Instant::now() + Duration::from_secs(10);
    while !condition() {
        assert!(Instant::now() < end, "actual GNU/helper condition did not settle");
        std::thread::yield_now();
    }
}
#[test]
fn actual_held_byte_blocks_pause_and_pause_blocks_new_admission_without_new_credits() {
    use std::os::unix::ffi::OsStrExt as _;
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("owned-credits");
    let name = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let original = jobserver::Client::from_fifo(&path).unwrap();
    original.release_raw().unwrap(); // This test owns its one real GNU byte.
    let gate = Client::new(original.clone());
    let credit = gate.try_acquire().unwrap().unwrap();
    assert_eq!(original.available().unwrap(), 0);
    assert!(credit.commit());
    assert!(gate.try_pause().unwrap().is_none());
    drop(credit);
    assert_eq!(original.available().unwrap(), 1);
    let helper =
        gate.clone().into_helper_thread(|_| panic!("paused client cannot request")).unwrap();
    let pause = gate.try_pause().unwrap().unwrap();
    assert!(gate.try_acquire().is_err());
    assert!(helper.request_token().is_err());
    assert_eq!(original.available().unwrap(), 1);
    pause.resume().unwrap();
    helper.shutdown_blocking().unwrap();
    drop(gate.try_acquire().unwrap().unwrap());
    assert_eq!(original.available().unwrap(), 1);
}
#[test]
fn fetched_unpublished_byte_and_callback_are_both_covered_until_actual_join() {
    let original = jobserver::Client::new(1).unwrap();
    let gate = Client::new(original.clone());
    let (published, received) = mpsc::channel();
    let (finish, wait_finish) = mpsc::channel();
    let helper = gate
        .clone()
        .into_helper_thread(move |credit| {
            published.send(credit.unwrap()).unwrap();
            wait_finish.recv_timeout(Duration::from_secs(10)).unwrap();
        })
        .unwrap();
    {
        // Hold the exact production gate across the actual request. The native
        // helper can read the real byte but cannot publish behind this lock.
        let mut state = gate.lock().unwrap();
        helper.request_locked(&mut state).unwrap();
        until(|| original.available().unwrap() == 0);
        assert_eq!(state.held, 0);
        assert_eq!(state.callbacks, 0);
        assert_eq!(state.helpers[&helper.id], 1, "unpublished read lost its pending guard");
    }
    let credit = received.recv_timeout(Duration::from_secs(10)).unwrap();
    assert!(gate.try_pause().unwrap().is_none());
    drop(credit);
    assert_eq!(original.available().unwrap(), 1);
    assert!(gate.try_pause().unwrap().is_none(), "callback still owns publication work");
    finish.send(()).unwrap();
    helper.shutdown_blocking().unwrap();
    gate.try_pause().unwrap().unwrap().resume().unwrap();
    assert_eq!(original.available().unwrap(), 1);
}
#[test]
fn only_real_cancel_ack_or_join_can_clear_a_waiting_native_helper() {
    let original = jobserver::Client::new(0).unwrap();
    let gate = Client::new(original.clone());
    let helper =
        gate.clone().into_helper_thread(|_| panic!("empty actual pool returned a byte")).unwrap();
    helper.request_token().unwrap();
    until(|| helper.queued_requests() == 0); // first is actually reading
    helper.request_token().unwrap();
    assert!(helper.cancel_request().unwrap()); // only second can withdraw
    assert!(!helper.cancel_request().unwrap());
    assert_eq!(gate.lock().unwrap().helpers[&helper.id], 1);
    assert!(gate.try_pause().unwrap().is_none());
    helper.shutdown_blocking().unwrap();
    assert!(gate.lock().unwrap().helpers.is_empty());
    gate.try_pause().unwrap().unwrap().resume().unwrap();
    assert_eq!(original.available().unwrap(), 0);
}
#[test]
fn actual_callback_panic_and_abandoned_pause_poison_instead_of_renewing_admission() {
    let original = jobserver::Client::new(1).unwrap();
    let gate = Client::new(original.clone());
    let helper = gate
        .clone()
        .into_helper_thread(|credit| {
            let _credit = credit.unwrap();
            panic!("controlled real helper callback failure");
        })
        .unwrap();
    helper.request_token().unwrap();
    until(|| matches!(gate.lock().unwrap().phase, Phase::Poisoned));
    assert!(helper.shutdown_blocking().is_err());
    assert!(gate.try_acquire().is_err());
    assert!(gate.try_pause().is_err());
    assert_eq!(original.available().unwrap(), 1);
    let separate = Client::new(original.clone());
    drop(separate.try_pause().unwrap().unwrap());
    assert!(separate.try_acquire().is_err());
    assert_eq!(original.available().unwrap(), 1);
}

#[cfg(target_os = "macos")]
#[test]
fn numeric_try_acquire_refusal_keeps_actual_bytes_and_shared_flags_unchanged() {
    use std::os::fd::AsRawFd as _;
    let original = jobserver::Client::new(1).unwrap();
    let jobserver::TransportWitnesses::NumericPipe { read, write } =
        original.transport_witnesses().unwrap()
    else {
        panic!("test owned a numeric pipe");
    };
    let flags = || {
        [read.as_raw_fd(), write.as_raw_fd()].map(|fd| unsafe { libc::fcntl(fd, libc::F_GETFL) })
    };
    let before = flags();
    let gate = Client::new(original.clone());
    assert_eq!(gate.try_acquire().unwrap_err().kind(), io::ErrorKind::Unsupported);
    assert_eq!(original.available().unwrap(), 1);
    assert_eq!(flags(), before);
    gate.try_pause().unwrap().unwrap().resume().unwrap();
}
