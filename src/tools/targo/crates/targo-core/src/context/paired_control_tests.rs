//! Actual cancellation endpoint custody only; no host/resource/proof fixture.
use super::*;
use std::io::Write as _;
use std::os::unix::net::UnixStream;
#[test]
fn sequential_contexts_keep_the_same_consumed_stop_and_original_private_endpoint() {
    let root = tempfile::tempdir().unwrap();
    let cwd = root.path().canonicalize().unwrap();
    let (original, mut owner) = UnixStream::pair().unwrap();
    let control = root_control::RootControl::for_test(original).unwrap();
    let mut first = GlobalContext::new(
        Shell::from_write(Box::new(Vec::<u8>::new())),
        cwd.clone(),
        cwd.join("home"),
    );
    first.install_root_control(control).unwrap();
    owner.write_all(b"C").unwrap();
    assert!(first.poll_root_cancellation());
    let control = first.into_root_control().unwrap();
    let mut next = GlobalContext::new(
        Shell::from_write(Box::new(Vec::<u8>::new())),
        cwd.clone(),
        cwd.join("home"),
    );
    next.install_root_control(control).unwrap();
    assert!(
        next.poll_root_cancellation(),
        "moving contexts cannot clear an already consumed stop or replace its actual socket"
    );
    drop(owner);
    assert!(next.poll_root_cancellation());
}
