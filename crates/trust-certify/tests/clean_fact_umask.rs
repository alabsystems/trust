// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! TG6 STORE-1: the fact store's own directories never make it refuse itself.
//!
//! The store refuses a cargo home with a group- or world-writable ancestor.
//! Under a umask that leaves group write (`002`, the default for user-private
//! groups on many Linux distributions) `trust/results/v1` used to be created
//! group-writable: the process that created the store used it, and every later
//! one refused it. The umask is process-global, so this check has its own test
//! binary and is its only test.
#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

use nix::sys::stat::{Mode, umask};
use trust_certify::clean_fact::FactStore;

#[test]
fn a_group_writable_umask_does_not_make_the_store_refuse_itself() {
    let home = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("clean-fact-umask-{}", std::process::id()));
    let _ = fs::remove_dir_all(&home);
    fs::create_dir_all(&home).expect("scratch");
    fs::set_permissions(&home, fs::Permissions::from_mode(0o700)).expect("private");
    let previous = umask(Mode::from_bits_truncate(0o002));
    let first = FactStore::open(&home).map(drop);
    let second = FactStore::open(&home).map(drop);
    umask(previous);
    assert!(first.is_ok(), "first open: {first:?}");
    assert!(second.is_ok(), "second open: {second:?}");
    for directory in ["trust", "trust/results", "trust/results/v1"] {
        let mode = fs::metadata(home.join(directory)).expect(directory).permissions().mode();
        assert_eq!(mode & 0o022, 0, "{directory} is group- or world-writable: {mode:o}");
    }
    let _ = fs::remove_dir_all(&home);
}
