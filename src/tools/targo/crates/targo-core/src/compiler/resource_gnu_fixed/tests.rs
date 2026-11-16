use std::os::fd::AsRawFd;
use std::time::{Duration, Instant};

use super::*;

fn wait_available(server: &Jobserver, expected: usize) {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if server.client().available().unwrap() == expected {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "actual GNU credits did not arrive"
        );
        std::thread::sleep(Duration::from_millis(1));
    }
}

fn anonymous(capacity: usize) -> Jobserver {
    let server = Jobserver::new(capacity).unwrap();
    server.client().acquire_raw().unwrap();
    server
}

#[test]
fn actual_inherited_credits_fund_the_ceiling_and_return_only_after_restricted_retirement() {
    let named = PrivateFifo::fixture(6);
    for source in [anonymous(6), named.jobserver.clone()] {
        let mut bridge = FixedGnuBridge::new(&source, 3, Arc::new(())).unwrap();
        let restricted = bridge.jobserver();
        wait_available(&restricted, 2);
        assert_eq!(source.client().available().unwrap(), 3);
        let first = restricted.client().try_acquire().unwrap().unwrap();
        let second = restricted.client().try_acquire().unwrap().unwrap();
        assert!(restricted.client().try_acquire().unwrap().is_none());
        assert!(!bridge.try_retire().unwrap());
        assert_eq!(source.client().available().unwrap(), 3);
        drop(first);
        assert!(!bridge.try_retire().unwrap());
        assert_eq!(
            restricted.client().available().unwrap(),
            1,
            "partial read rolled back"
        );
        drop(second);
        assert!(bridge.try_retire().unwrap());
        assert_eq!(source.client().available().unwrap(), 5);
        assert!(
            restricted.client().try_acquire().unwrap().is_none(),
            "retired bytes burned"
        );
        assert!(
            bridge.try_retire().unwrap(),
            "retirement cannot refund twice"
        );
        assert_eq!(source.client().available().unwrap(), 5);
    }
}

#[test]
fn unavailable_originals_do_not_mint_and_original_pipe_flags_never_change() {
    let source = anonymous(3);
    let originals: Vec<_> = (0..2).map(|_| source.client().acquire().unwrap()).collect();
    let read = source.pipe_descriptors().unwrap()[0].as_raw_fd();
    let flags = unsafe { libc::fcntl(read, libc::F_GETFL) };
    assert_ne!(flags, -1);
    let mut bridge = FixedGnuBridge::new(&source, 3, Arc::new(())).unwrap();
    let restricted = bridge.jobserver();
    assert_eq!(restricted.client().available().unwrap(), 0);
    assert!(restricted.client().try_acquire().unwrap().is_none());
    drop(originals);
    wait_available(&restricted, 2);
    assert_eq!(unsafe { libc::fcntl(read, libc::F_GETFL) }, flags);
    assert!(bridge.try_retire().unwrap());
    assert_eq!(unsafe { libc::fcntl(read, libc::F_GETFL) }, flags);
    assert_eq!(source.client().available().unwrap(), 2);
}

#[test]
fn retiring_partial_funding_interrupts_the_same_original_helper_without_waiting_for_more() {
    let source = anonymous(2);
    let mut bridge = FixedGnuBridge::new(&source, 4, Arc::new(())).unwrap();
    wait_available(&bridge.jobserver(), 1);
    assert!(bridge.try_retire().unwrap());
    assert_eq!(source.client().available().unwrap(), 1);
    assert_eq!(bridge.jobserver().client().available().unwrap(), 0);
}

#[test]
fn implicit_only_never_borrows_or_creates_a_supplementary_credit() {
    let source = anonymous(6);
    let mut bridge = FixedGnuBridge::new(&source, 1, Arc::new(())).unwrap();
    assert_eq!(bridge.jobserver().client().available().unwrap(), 0);
    assert_eq!(source.client().available().unwrap(), 5);
    assert!(bridge.try_retire().unwrap());
    assert_eq!(source.client().available().unwrap(), 5);
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "actual separate GNU worker custody control"
)]
fn owning_target_wait_cannot_refund_a_live_workers_restricted_credit() {
    const ACTOR: &str = "TARGO_FIXED_RUN_CREDIT_ACTOR";
    if let Some(root) = std::env::var_os(ACTOR) {
        let root = std::path::PathBuf::from(root);
        let path = std::env::var_os("TARGO_FIXED_RUN_CREDIT_FIFO").unwrap();
        let server = Jobserver::from_fifo(std::path::Path::new(&path)).unwrap();
        let token = server.client().acquire().unwrap();
        std::fs::write(root.join("held"), b"actual-credit-held").unwrap();
        let deadline = Instant::now() + Duration::from_secs(20);
        while !root.join("return").exists() {
            assert!(
                Instant::now() < deadline,
                "actual worker return was not requested"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
        drop(token);
        std::fs::write(root.join("returned"), b"actual-credit-returned").unwrap();
        return;
    }
    let root = tempfile::tempdir().unwrap();
    let original = anonymous(6);
    let mut bridge = FixedGnuBridge::new(&original, 2, Arc::new(())).unwrap();
    let restricted = bridge.jobserver();
    wait_available(&restricted, 1);
    let jobserver::TransportWitnesses::NamedFifo { path, .. } =
        restricted.client().transport_witnesses().unwrap()
    else {
        panic!("actual restricted FIFO missing");
    };
    let module = module_path!().split_once("::").unwrap().1;
    let exact =
        format!("{module}::owning_target_wait_cannot_refund_a_live_workers_restricted_credit");
    let mut worker = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", &exact, "--nocapture", "--test-threads=1"])
        .env(ACTOR, root.path())
        .env("TARGO_FIXED_RUN_CREDIT_FIFO", path)
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    while !root.path().join("held").exists() {
        assert!(
            Instant::now() < deadline,
            "actual worker never acquired its byte"
        );
        std::thread::sleep(Duration::from_millis(1));
    }
    // An actual other target was waited; this proves no closure of the live
    // worker. Only its actual restricted byte can settle the original guard.
    assert!(
        std::process::Command::new("/usr/bin/true")
            .status()
            .unwrap()
            .success()
    );
    assert!(!bridge.try_retire().unwrap());
    assert_eq!(original.client().available().unwrap(), 4);
    std::fs::write(root.path().join("return"), b"return").unwrap();
    assert!(worker.wait().unwrap().success());
    assert_eq!(
        std::fs::read(root.path().join("returned")).unwrap(),
        b"actual-credit-returned"
    );
    assert!(bridge.try_retire().unwrap());
    assert_eq!(original.client().available().unwrap(), 5);
    assert_eq!(restricted.client().available().unwrap(), 0);
}

#[test]
fn unfunded_restricted_byte_refuses_instead_of_refunding_an_original() {
    let source = anonymous(3);
    let mut bridge = FixedGnuBridge::new(&source, 3, Arc::new(())).unwrap();
    let restricted = bridge.jobserver();
    wait_available(&restricted, 2);
    restricted.client().release_raw().unwrap();
    assert_eq!(
        bridge.try_retire().unwrap_err().kind(),
        io::ErrorKind::InvalidData
    );
    assert_eq!(source.client().available().unwrap(), 0);
    // Remove the test's own injected byte; neither production nor an unknown
    // Drop repairs an unbound pool or infers an extra original guard.
    restricted
        .client()
        .try_acquire()
        .unwrap()
        .unwrap()
        .drop_without_releasing();
    assert!(bridge.try_retire().unwrap());
    assert_eq!(source.client().available().unwrap(), 2);
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "isolated real GNU custody-loss actor"
)]
fn unknown_retirement_keeps_actual_original_guards_and_custody() {
    const ACTOR: &str = "TARGO_FIXED_GNU_CUSTODY_ACTOR";
    if let Some(parent) = std::env::var_os(ACTOR) {
        struct Custody(std::path::PathBuf);
        impl Drop for Custody {
            fn drop(&mut self) {
                std::fs::write(self.0.join("custody-released"), b"released").unwrap();
            }
        }
        let parent = std::path::PathBuf::from(parent);
        let source = PrivateFifo::fixture_in(3, &parent);
        let bridge =
            FixedGnuBridge::new(&source.jobserver, 3, Arc::new(Custody(parent.clone()))).unwrap();
        let restricted = bridge.jobserver();
        wait_available(&restricted, 2);
        let outstanding = restricted.client().try_acquire().unwrap().unwrap();
        drop(bridge);
        assert_eq!(source.available(), 0);
        assert!(!parent.join("custody-released").exists());
        drop(outstanding);
        assert_eq!(
            source.available(),
            0,
            "unknown Drop must not refund originals later"
        );
        std::fs::write(parent.join("checked"), b"originals-retained").unwrap();
        std::process::exit(75);
    }
    let parent = tempfile::tempdir().unwrap();
    let module = module_path!().split_once("::").unwrap().1;
    let exact = format!("{module}::unknown_retirement_keeps_actual_original_guards_and_custody");
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", &exact, "--nocapture"])
        .env(ACTOR, parent.path())
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(75));
    assert_eq!(
        std::fs::read(parent.path().join("checked")).unwrap(),
        b"originals-retained"
    );
    assert!(!parent.path().join("custody-released").exists());
}
