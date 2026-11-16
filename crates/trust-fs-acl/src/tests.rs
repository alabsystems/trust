// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

#[test]
fn ordinary_file_has_no_extended_acl() {
    let file = tempfile::tempfile().unwrap();
    require_no_acl_grants(&file).unwrap();
    require_no_acl_entries(&file).unwrap();
}

#[cfg(target_os = "macos")]
#[test]
fn deny_entries_remain_private_but_grants_and_nonempty_acls_refuse() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("record");
    std::fs::write(&path, b"facts").unwrap();
    let file = File::open(&path).unwrap();
    let chmod = |entry| {
        assert!(
            std::process::Command::new("/bin/chmod")
                .args(["+a", entry])
                .arg(&path)
                .status()
                .unwrap()
                .success()
        );
    };
    chmod("everyone deny write");
    require_no_acl_grants(&file).unwrap();
    assert!(require_no_acl_entries(&file).is_err());
    chmod("everyone allow read");
    assert!(require_no_acl_grants(&file).is_err());
    assert!(require_no_acl_entries(&file).is_err());
}
