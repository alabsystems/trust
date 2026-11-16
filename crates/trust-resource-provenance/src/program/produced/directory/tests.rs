// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual directory originals only; no compiler, producer or SDK is fabricated.
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use super::*;
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}
#[test]
fn received_directory_retains_original_and_rejects_a_sibling_or_replaced_name() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let output = HeldOutputRoot::open(&root, deadline()).unwrap();
    let selected = root.join("private/unit");
    let parent = output.prepare_directory(&selected, deadline()).unwrap();
    let original = File::from(parent.descriptor(deadline()).unwrap().try_clone_to_owned().unwrap());
    let raw = original.as_raw_fd();
    let held = output.directory_from_original(&selected, original, deadline()).unwrap();
    assert_eq!(held.descriptor(deadline()).unwrap().as_raw_fd(), raw);
    let sibling = root.join("private/other");
    std::fs::create_dir(&sibling).unwrap();
    assert!(
        output
            .directory_from_original(&selected, File::open(&sibling).unwrap(), deadline())
            .is_err()
    );
    std::fs::rename(&selected, root.join("private/retained-unit")).unwrap();
    std::fs::create_dir(&selected).unwrap();
    assert!(held.validate(deadline()).is_err());
    assert!(held.validate(deadline()).is_err());
}

#[test]
fn parent_prepares_new_private_namespace_from_original_root_and_retains_it() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let output = HeldOutputRoot::open(&root, deadline()).unwrap();
    let path = root.join("private/unit/selected");
    let held = output.prepare_directory(&path, deadline()).unwrap();
    assert_eq!(held.path(), path);
    assert_eq!(held.output_root(), root);
    assert_eq!(held.descriptor_count(), 3);
    assert!(held.descriptor_count() <= HeldRootDirectory::capture_descriptor_bound());
    assert_eq!(std::fs::metadata(&path).unwrap().mode() & 0o777, 0o700);
    std::fs::write(path.join("actual-compiler-data"), b"mutable contents").unwrap();
    held.validate(deadline()).unwrap();
    assert_eq!(
        output.prepare_directory(&path, deadline()).err().unwrap().kind(),
        io::ErrorKind::AlreadyExists
    );
    assert_eq!(std::fs::read(path.join("actual-compiler-data")).unwrap(), b"mutable contents");
    let existing = output.directory(&path, deadline()).unwrap();
    drop(output);
    held.validate(deadline()).unwrap();
    existing.validate(deadline()).unwrap();
    assert_eq!(
        File::from(held.descriptor(deadline()).unwrap().try_clone_to_owned().unwrap())
            .metadata()
            .unwrap()
            .ino(),
        std::fs::metadata(path).unwrap().ino()
    );
}

#[test]
fn preparation_never_mutates_through_symlink_special_or_escaping_namespace() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let output = HeldOutputRoot::open(&root, deadline()).unwrap();
    let outside = tempfile::tempdir().unwrap();
    std::os::unix::fs::symlink(outside.path(), root.join("alias")).unwrap();
    assert!(output.prepare_directory(&root.join("alias/new"), deadline()).is_err());
    assert!(!outside.path().join("new").exists());
    std::fs::write(root.join("file"), b"original").unwrap();
    assert!(output.prepare_directory(&root.join("file/new"), deadline()).is_err());
    let fifo = root.join("fifo");
    let name = std::ffi::CString::new(fifo.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    assert!(output.prepare_directory(&fifo.join("new"), deadline()).is_err());
    for path in [&root, &outside.path().join("new"), &root.join("new/../escape")] {
        assert!(output.prepare_directory(path, deadline()).is_err());
    }
    assert!(!root.join("new").exists(), "validate complete syntax before the first mkdir");
    let mut too_deep = root.clone();
    for _ in 0..128 {
        too_deep.push("next");
    }
    assert!(output.prepare_directory(&too_deep, deadline()).is_err());
    assert!(!root.join("next").exists());
    assert_eq!(std::fs::read(root.join("file")).unwrap(), b"original");
}

#[test]
fn changed_parent_permissions_or_selected_directory_are_terminal() {
    for mode in 0..3 {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let output = HeldOutputRoot::open(&root, deadline()).unwrap();
        let path = root.join("private/unit");
        let held = output.prepare_directory(&path, deadline()).unwrap();
        match mode {
            0 => {
                std::fs::rename(root.join("private"), root.join("retained-private")).unwrap();
                std::fs::create_dir_all(&path).unwrap();
                assert!(held.validate(deadline()).is_err());
                std::fs::remove_dir_all(root.join("private")).unwrap();
                std::fs::rename(root.join("retained-private"), root.join("private")).unwrap();
            }
            1 => {
                std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o500)).unwrap();
                assert!(held.validate(deadline()).is_err());
                std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
            }
            _ => {
                let retained = root.join("retained-unit");
                std::fs::rename(&path, &retained).unwrap();
                std::fs::create_dir(&path).unwrap();
                assert!(held.validate(deadline()).is_err());
                std::fs::remove_dir(&path).unwrap();
                std::fs::rename(&retained, &path).unwrap();
            }
        }
        assert!(
            held.validate(deadline()).is_err(),
            "later success cannot clear failure mode {mode}"
        );
        assert!(held.descriptor(deadline()).is_err());
    }
}
