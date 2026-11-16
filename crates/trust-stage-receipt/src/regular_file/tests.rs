// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::fs::{self, File, FileTimes, OpenOptions};
use std::io::Write as _;
use std::os::unix::net::UnixListener;
use std::time::{Duration, UNIX_EPOCH};

use super::*;

#[test]
fn required_empty_exact_limit_and_binary_bytes_are_preserved() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("artifact");
    assert!(read_required_regular_file(&path, 3).is_err(), "required absence must refuse");
    fs::write(&path, b"").unwrap();
    assert_eq!(read_required_regular_file(&path, 0).unwrap(), b"");
    fs::write(&path, b"\0\xffx").unwrap();
    assert_eq!(read_required_regular_file(&path, 3).unwrap(), b"\0\xffx");
    assert!(read_required_regular_file(&path, 2).is_err());
    assert!(read_required_regular_file(&path, u64::MAX).is_err());
}

#[test]
fn required_sparse_oversize_refuses_before_opening_or_reading() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("large");
    File::create(&path).unwrap().set_len(1024 * 1024 * 1024).unwrap();
    let mut opened = false;
    assert!(
        read_with_hook(&path, 1024, |point| {
            if point == ReadPoint::BeforeOpen {
                opened = true;
            }
        })
        .is_err()
    );
    assert!(!opened, "oversize metadata must refuse before descriptor admission");
}

#[test]
fn required_special_files_and_links_refuse_without_waiting_or_following() {
    let directory = tempfile::tempdir().unwrap();
    assert!(read_required_regular_file(directory.path(), 1024).is_err());
    let target = directory.path().join("target");
    fs::write(&target, b"outside").unwrap();
    let link = directory.path().join("link");
    std::os::unix::fs::symlink(&target, &link).unwrap();
    assert!(read_required_regular_file(&link, 1024).is_err());
    fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink(directory.path(), &link).unwrap();
    assert!(read_required_regular_file(&link, 1024).is_err());
    let fifo = directory.path().join("fifo");
    let name = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: one owned temporary pathname, valid throughout mkfifo.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    assert!(read_required_regular_file(&fifo, 1024).is_err());
    let _socket = UnixListener::bind(directory.path().join("socket")).unwrap();
    assert!(read_required_regular_file(&directory.path().join("socket"), 1024).is_err());
}

#[test]
fn required_replacement_before_or_after_open_refuses_even_with_same_bytes_and_mtime() {
    for when in [ReadPoint::BeforeOpen, ReadPoint::AfterOpen] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("artifact");
        fs::write(&path, b"same").unwrap();
        let modified = fs::metadata(&path).unwrap().modified().unwrap();
        let result = read_with_hook(&path, 4, |point| {
            if point == when {
                fs::rename(&path, directory.path().join("original")).unwrap();
                fs::write(&path, b"same").unwrap();
                File::options()
                    .write(true)
                    .open(&path)
                    .unwrap()
                    .set_times(FileTimes::new().set_modified(modified))
                    .unwrap();
            }
        });
        assert!(result.is_err());
    }
}

#[test]
fn required_regular_to_fifo_open_race_is_nonblocking_and_refused() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("artifact");
    fs::write(&path, b"regular").unwrap();
    let result = read_with_hook(&path, 100, |point| {
        if point == ReadPoint::BeforeOpen {
            fs::remove_file(&path).unwrap();
            let name = std::ffi::CString::new(path.as_os_str().as_encoded_bytes()).unwrap();
            // SAFETY: test-owned pathname and no other writer.
            assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        }
    });
    assert!(result.is_err());
}

#[test]
fn required_mid_read_growth_shrink_and_same_size_rewrite_refuse() {
    for mutation in ["grow", "shrink", "rewrite"] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("artifact");
        fs::write(&path, vec![b'a'; 64 * 1024]).unwrap();
        let mut changed = false;
        let result = read_with_hook(&path, 128 * 1024, |point| {
            if point != ReadPoint::AfterChunk || changed {
                return;
            }
            changed = true;
            match mutation {
                "grow" => OpenOptions::new()
                    .append(true)
                    .open(&path)
                    .unwrap()
                    .write_all(b"extra")
                    .unwrap(),
                "shrink" => OpenOptions::new().write(true).open(&path).unwrap().set_len(0).unwrap(),
                "rewrite" => {
                    fs::write(&path, vec![b'b'; 64 * 1024]).unwrap();
                    // Force an observable timestamp change without depending
                    // on clock resolution or a sleep between writes.
                    File::options()
                        .write(true)
                        .open(&path)
                        .unwrap()
                        .set_times(
                            FileTimes::new().set_modified(UNIX_EPOCH + Duration::from_secs(1)),
                        )
                        .unwrap();
                }
                _ => unreachable!(),
            }
        });
        assert!(changed && result.is_err(), "{mutation}");
    }
}

#[test]
fn required_final_path_removal_or_symlink_replacement_refuses() {
    for replace in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("artifact");
        let other = directory.path().join("other");
        fs::write(&path, b"same").unwrap();
        fs::write(&other, b"same").unwrap();
        let result = read_with_hook(&path, 4, |point| {
            if point == ReadPoint::BeforeFinalCheck {
                fs::remove_file(&path).unwrap();
                if replace {
                    std::os::unix::fs::symlink(&other, &path).unwrap();
                }
            }
        });
        assert!(result.is_err());
    }
}
