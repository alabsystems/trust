// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;
use std::time::Duration;
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn mutable_directory_keeps_original_identity_and_allows_intended_membership_changes() {
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().canonicalize().unwrap().join("bookkeeping");
    std::fs::create_dir(&path).unwrap();
    let held = HeldDirectoryInput::open(&path, deadline()).unwrap();
    std::fs::write(path.join("new-fingerprint"), b"data").unwrap();
    held.validate(deadline()).unwrap();
    assert_eq!(held.path(), path);
    assert!(held.descriptor_count() <= HeldDirectoryInput::capture_descriptor_bound());
    assert!(held.descriptor(deadline()).is_ok());
}
#[test]
fn directory_parent_substitution_and_late_errors_stay_terminal() {
    let temp = tempfile::tempdir().unwrap();
    let base = temp.path().canonicalize().unwrap();
    let path = base.join("parent/bookkeeping");
    std::fs::create_dir_all(&path).unwrap();
    let held = HeldDirectoryInput::open(&path, deadline()).unwrap();
    std::fs::rename(base.join("parent"), base.join("retained-parent")).unwrap();
    std::fs::create_dir_all(&path).unwrap();
    assert!(held.validate(deadline()).is_err());
    std::fs::remove_dir(&path).unwrap();
    std::fs::remove_dir(base.join("parent")).unwrap();
    std::fs::rename(base.join("retained-parent"), base.join("parent")).unwrap();
    assert!(held.validate(deadline()).is_err());
    let fresh = HeldDirectoryInput::open(&path, deadline()).unwrap();
    assert!(fresh.validate(Instant::now()).is_err());
    fresh.validate(deadline()).unwrap();
    assert!(fresh.descriptor(Instant::now()).is_err());
    assert!(fresh.descriptor(deadline()).is_ok());
}
#[test]
fn actual_ancestor_identity_population_vetoes_case_independent_containment() {
    use std::os::unix::fs::MetadataExt as _;
    let temp=tempfile::tempdir().unwrap();
    let base=temp.path().canonicalize().unwrap();
    let selected=base.join("selected");let source=selected.join("source");
    std::fs::create_dir_all(&source).unwrap();
    let held=HeldDirectoryInput::open(&source,deadline()).unwrap();
    let root=std::fs::metadata(&selected).unwrap();
    assert!(held.original_tree_identities(deadline()).unwrap().contains(&(root.dev(),root.ino())));
    let own=std::fs::metadata(&source).unwrap();
    assert_eq!(held.original_identity(deadline()).unwrap(),(own.dev(),own.ino()));
}
#[test]
fn directory_input_refuses_parent_aliases_and_regular_files() {
    let temp = tempfile::tempdir().unwrap();
    let base = temp.path().canonicalize().unwrap();
    std::fs::create_dir_all(base.join("parent/bookkeeping")).unwrap();
    std::os::unix::fs::symlink(base.join("parent"), base.join("alias")).unwrap();
    assert!(HeldDirectoryInput::open(&base.join("alias/bookkeeping"), deadline()).is_err());
    std::fs::write(base.join("file"), b"data").unwrap();
    assert!(HeldDirectoryInput::open(&base.join("file"), deadline()).is_err());
}
