//! Bounded controls for untrusted file paths, not result or proof authority.
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
#![cfg(unix)]

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

use trust_test_execution::results::{read_bounded, read_exit};

const FIFO_PATH: &str = "TRUST_RESULT_READER_FIFO_PATH";
const READ_EXIT: &str = "TRUST_RESULT_READER_EXIT";

#[test]
fn fifo_reader_child() {
    let Some(path) = std::env::var_os(FIFO_PATH) else { return };
    let error = if std::env::var_os(READ_EXIT).is_some() {
        read_exit(Path::new(&path)).unwrap_err()
    } else {
        read_bounded(Path::new(&path), 1024).unwrap_err()
    };
    assert_eq!(error, "not a regular file");
}

#[test]
fn fifo_paths_are_refused_without_waiting_for_a_writer() {
    use std::os::unix::ffi::OsStrExt;
    let root = std::env::temp_dir().join(format!(
        "trust-result-fifo-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    std::fs::create_dir(&root).unwrap();
    let fifo = root.join("no-writer");
    let name = std::ffi::CString::new(fifo.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    for exit in [false, true] {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", "fifo_reader_child", "--nocapture"])
            .env(FIFO_PATH, &fifo)
            .env_remove(READ_EXIT);
        if exit {
            command.env(READ_EXIT, "1");
        }
        let mut child = command.spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                std::fs::remove_dir_all(&root).unwrap();
                panic!("reader blocked on a FIFO with no writer (read_exit={exit})");
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        assert!(status.success(), "reader child failed (read_exit={exit}): {status}");
    }
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn regular_result_bytes_still_obey_the_exact_limit() {
    let file = std::env::temp_dir().join(format!(
        "trust-result-regular-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    std::fs::write(&file, b"1234").unwrap();
    assert_eq!(read_bounded(&file, 4).unwrap(), b"1234");
    assert_eq!(read_bounded(&file, 3).unwrap_err(), "larger than 3 bytes");
    std::fs::remove_file(file).unwrap();
}
