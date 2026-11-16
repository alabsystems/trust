// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::os::unix::fs::{DirBuilderExt, PermissionsExt};

use super::*;

fn root() -> tempfile::TempDir {
    let dir =
        tempfile::Builder::new().tempdir_in(std::env::temp_dir().canonicalize().unwrap()).unwrap();
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
    dir
}
#[test]
fn private_readonly_files_are_bounded_and_symlink_ancestors_refuse() {
    let root = root();
    let path = root.path().join("record");
    std::fs::write(&path, b"facts").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o500)).unwrap();
    let dir = directory(root.path()).unwrap();
    require_no_acl_entries(&dir).unwrap();
    assert_eq!(read_private(&dir, OsStr::new("record"), 5).unwrap().0, b"facts");
    assert!(read_private(&dir, OsStr::new("record"), 4).is_err());
    std::os::unix::fs::symlink(&path, root.path().join("link")).unwrap();
    assert!(open_private(&dir, OsStr::new("link")).is_err());
    let child = root.path().join("child");
    std::fs::DirBuilder::new().mode(0o700).create(&child).unwrap();
    std::os::unix::fs::symlink(&child, root.path().join("alias")).unwrap();
    assert!(directory(&root.path().join("alias")).is_err());
    assert!(open_private(&dir, OsStr::new("../record")).is_err());
}
#[cfg(target_os = "macos")]
#[test]
fn deny_only_acl_is_private_but_an_allow_entry_is_not() {
    let root = root();
    let path = root.path().join("record");
    std::fs::write(&path, b"facts").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
    let chmod = |entry| {
        assert!(
            std::process::Command::new("/bin/chmod")
                .args(["+a", entry])
                .arg(&path)
                .status()
                .unwrap()
                .success()
        )
    };
    chmod("everyone deny write");
    let dir = directory(root.path()).unwrap();
    let file = open_private(&dir, OsStr::new("record")).unwrap();
    assert!(require_no_acl_entries(&file).is_err());
    chmod("everyone allow read");
    assert!(open_private(&dir, OsStr::new("record")).is_err());
}
