//! Actual descriptor transfer only; no native Job, cache owner or SDK fixture.
use super::*;
use std::{fs::File, os::unix::net::UnixStream, time::Duration};

#[test]
fn original_readonly_directory_moves_to_state_on_the_same_carrier() {
    let home = std::fs::canonicalize(std::env::temp_dir()).unwrap();
    let original = File::open(&home).unwrap();
    let (left, right) = UnixStream::pair().unwrap();
    let mut sender = Channel::new(left).unwrap();
    let mut receiver = Channel::new(right).unwrap();
    let end = Instant::now() + Duration::from_secs(10);
    send_preparation_cache_directory(&mut sender, &home, original.as_fd(), end, || Ok(())).unwrap();
    let delivery = receive_preparation_cache_directory(&mut receiver, end).unwrap();
    let mut state = Vec::new();
    assert!(delivery.into_parts(&mut state));
    assert_eq!(state.len(), 1);
    assert_eq!(
        inspect(state[0].as_fd()).unwrap().0,
        inspect(original.as_fd()).unwrap().0
    );
    sender.send(b"same original source channel", end).unwrap();
    assert_eq!(
        receiver.receive(end).unwrap(),
        b"same original source channel"
    );
}

#[test]
fn foreign_directory_and_regular_file_refuse_before_sending() {
    let home = std::fs::canonicalize(std::env::temp_dir()).unwrap();
    let foreign = File::open("/").unwrap();
    assert!(check_directory(&home, foreign.as_fd()).is_err());
    let file = File::open(std::env::current_exe().unwrap()).unwrap();
    assert!(check_directory(&home, file.as_fd()).is_err());
}

#[test]
fn wrong_marker_and_extra_rights_remain_in_the_receivers_actual_population() {
    let home = File::open("/").unwrap();
    for (marker, count) in [(0x7b, 1), (PREPARATION_CACHE_DIRECTORY_RIGHTS_MARKER, 2)] {
        let (left, right) = UnixStream::pair().unwrap();
        let mut sender = Channel::new(left).unwrap();
        let mut receiver = Channel::new(right).unwrap();
        let end = Instant::now() + Duration::from_secs(10);
        let rights = (0..count).map(|_| home.as_fd()).collect::<Vec<_>>();
        sender
            .send_bootstrap_descriptions(&rights, marker, end)
            .unwrap();
        let delivered = receive_preparation_cache_directory(&mut receiver, end).unwrap();
        let mut state = Vec::new();
        assert!(!delivered.into_parts(&mut state));
        assert_eq!(state.len(), count);
        assert!(state.iter().all(|fd| inspect(fd.as_fd()).is_ok()));
        assert!(
            receiver.receive(end).is_err(),
            "malformed carrier remains poisoned"
        );
    }
}
