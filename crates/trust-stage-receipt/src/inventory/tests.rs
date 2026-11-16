use std::fs;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::net::UnixListener;
use std::path::Path;

use super::*;

fn snapshot(path: &Path) -> DirectorySnapshot {
    capture_directory(path, Limits::default()).unwrap()
}

#[test]
fn recursive_inventory_includes_metadata_unknown_suffixes_and_empty_directories() {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("libstd.rlib"), b"code").unwrap();
    fs::write(root.path().join("libstd.rmeta"), b"metadata").unwrap();
    fs::write(root.path().join("unrecognized.member"), b"other").unwrap();
    fs::create_dir(root.path().join("empty")).unwrap();
    fs::create_dir(root.path().join("rustc-dependencies")).unwrap();
    fs::write(root.path().join("rustc-dependencies/child.rmeta"), b"child").unwrap();
    let observed = snapshot(root.path());
    assert_eq!(observed.root(), fs::canonicalize(root.path()).unwrap());
    assert_eq!(observed.total_bytes(), 22);
    assert_eq!(observed.entries().len(), 6);
    assert_eq!(
        observed
            .entries()
            .iter()
            .map(|entry| entry.relative_path().to_str().unwrap())
            .collect::<Vec<_>>(),
        [
            "empty",
            "libstd.rlib",
            "libstd.rmeta",
            "rustc-dependencies",
            "rustc-dependencies/child.rmeta",
            "unrecognized.member"
        ]
    );
    assert!(matches!(observed.entries()[0].kind(), EntryKind::Directory));
    assert_eq!(
        observed.entries()[2].kind(),
        &EntryKind::File { bytes: 8, sha256: crate::hash(b"metadata") }
    );
    assert_eq!(observed, snapshot(root.path()));
}

#[test]
fn content_metadata_addition_removal_rename_and_empty_directory_changes_affect_identity() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("lib.rmeta");
    fs::write(&path, b"one").unwrap();
    let original = snapshot(root.path());
    fs::write(&path, b"two").unwrap();
    assert_ne!(snapshot(root.path()), original);
    fs::write(&path, b"one").unwrap();
    assert_eq!(snapshot(root.path()), original);
    fs::rename(&path, root.path().join("renamed.rmeta")).unwrap();
    assert_ne!(snapshot(root.path()), original);
    fs::rename(root.path().join("renamed.rmeta"), &path).unwrap();
    fs::write(root.path().join("extra.anything"), b"").unwrap();
    assert_ne!(snapshot(root.path()), original);
    fs::remove_file(root.path().join("extra.anything")).unwrap();
    fs::create_dir(root.path().join("empty")).unwrap();
    assert_ne!(snapshot(root.path()), original);
    fs::remove_dir(root.path().join("empty")).unwrap();
    assert_eq!(snapshot(root.path()), original);
    fs::remove_file(path).unwrap();
    assert_ne!(snapshot(root.path()), original);
}

#[test]
fn links_fifos_and_sockets_are_refused_without_following_or_waiting() {
    let root = tempfile::tempdir().unwrap();
    let outside = tempfile::tempdir().unwrap();
    let link = root.path().join("link");
    std::os::unix::fs::symlink(outside.path(), &link).unwrap();
    assert!(capture_directory(root.path(), Limits::default()).is_err());
    fs::remove_file(&link).unwrap();
    fs::write(outside.path().join("metadata"), b"outside").unwrap();
    std::os::unix::fs::symlink(outside.path().join("metadata"), &link).unwrap();
    assert!(capture_directory(root.path(), Limits::default()).is_err());
    fs::remove_file(link).unwrap();
    let fifo = root.path().join("fifo");
    let name = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: one owned temporary pathname, valid throughout mkfifo.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    assert!(capture_directory(root.path(), Limits::default()).is_err());
    fs::remove_file(fifo).unwrap();
    let socket = UnixListener::bind(root.path().join("socket")).unwrap();
    assert!(capture_directory(root.path(), Limits::default()).is_err());
    drop(socket);
}

#[test]
fn count_depth_file_total_and_path_bounds_are_enforced() {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("first.rmeta"), b"1234").unwrap();
    fs::write(root.path().join("second.rlib"), b"5678").unwrap();
    for limits in [
        Limits { max_entries: 1, ..Limits::default() },
        Limits { max_file_bytes: 3, ..Limits::default() },
        Limits { max_total_bytes: 7, ..Limits::default() },
        Limits { max_depth: 0, ..Limits::default() },
        Limits { max_path_bytes: 1, ..Limits::default() },
        Limits { max_total_path_bytes: 1, ..Limits::default() },
    ] {
        assert!(capture_directory(root.path(), limits).is_err(), "{limits:?}");
    }
    fs::create_dir(root.path().join("nested")).unwrap();
    fs::write(root.path().join("nested/third.rmeta"), b"").unwrap();
    assert!(capture_directory(root.path(), Limits { max_depth: 1, ..Limits::default() }).is_err());
}

#[test]
fn non_utf8_and_control_names_do_not_become_lossy_inventory_keys() {
    // APFS rejects non-UTF-8 names before a fixture can be created. Exercise
    // the same lossless path validator directly on every Unix filesystem.
    let name = std::ffi::OsString::from_vec(b"bad\xff.rmeta".to_vec());
    assert!(super::unix::text(Path::new(&name), Limits::default().max_path_bytes).is_err());
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("bad\n.rmeta"), b"metadata").unwrap();
    assert!(capture_directory(root.path(), Limits::default()).is_err());
}

#[test]
fn final_whole_tree_check_detects_an_earlier_sibling_changed_after_capture() {
    let root = tempfile::tempdir().unwrap();
    fs::create_dir(root.path().join("a")).unwrap();
    fs::create_dir(root.path().join("z")).unwrap();
    fs::write(root.path().join("a/first.rmeta"), b"old").unwrap();
    fs::write(root.path().join("z/last.rlib"), b"last").unwrap();
    let result =
        super::unix::capture_with_verification_hook(root.path(), Limits::default(), || {
            // Writing an existing file does not change its parent directory's
            // namespace. Checking only root/last-subtree stamps would miss this.
            fs::write(root.path().join("a/first.rmeta"), b"changed length").unwrap();
        });
    assert!(result.is_err());
}

#[test]
fn an_empty_tree_can_be_observed_and_relative_roots_refuse() {
    let root = tempfile::tempdir().unwrap();
    let observed = snapshot(root.path());
    assert!(observed.entries().is_empty());
    assert_eq!(observed.total_bytes(), 0);
    assert!(capture_directory(Path::new("."), Limits::default()).is_err());
}
