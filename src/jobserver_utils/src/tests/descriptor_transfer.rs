use std::fs::File;
use std::os::unix::net::UnixStream;
use std::time::Duration;

use super::*;

#[test]
fn transfer_refuses_expired_empty_and_excessive_bundles_before_sending() {
    let (sender, mut receiver) = UnixStream::pair().unwrap();
    receiver.set_nonblocking(true).unwrap();
    let file = File::open("/dev/null").unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    assert_eq!(send(&sender, &[], 1, deadline).unwrap_err().kind(), io::ErrorKind::InvalidInput);
    assert_eq!(
        send(&sender, &vec![file.as_fd(); MAX_DESCRIPTORS + 1], 1, deadline).unwrap_err().kind(),
        io::ErrorKind::InvalidInput
    );
    assert_eq!(
        send(&sender, &[file.as_fd()], 1, Instant::now()).unwrap_err().kind(),
        io::ErrorKind::TimedOut
    );
    use std::io::Read as _;
    assert_eq!(receiver.read(&mut [0]).unwrap_err().kind(), io::ErrorKind::WouldBlock);
}

#[test]
fn closed_peer_actor() {
    if std::env::var_os("TRUST_TRANSFER_SIGPIPE_ACTOR").is_none() {
        return;
    }
    // Only this isolated test process restores the default disposition.
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_DFL);
    }
    let (sender, receiver) = UnixStream::pair().unwrap();
    drop(receiver);
    let file = File::open("/dev/null").unwrap();
    let error =
        send(&sender, &[file.as_fd()], 1, Instant::now() + Duration::from_secs(60)).unwrap_err();
    assert!(matches!(error.kind(), io::ErrorKind::BrokenPipe | io::ErrorKind::ConnectionReset));
}

#[test]
fn descriptor_transfer_survives_closed_peer_with_default_sigpipe() {
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "descriptor_transfer::tests::closed_peer_actor", "--nocapture"])
        .env("TRUST_TRANSFER_SIGPIPE_ACTOR", "1")
        .status()
        .unwrap();
    assert!(status.success());
}
