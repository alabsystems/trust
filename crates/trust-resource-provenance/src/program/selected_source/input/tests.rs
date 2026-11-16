//! Actual physical originals only; no semantic source, Manager or native role.
use std::fs;
use std::os::fd::AsFd as _;
use std::os::unix::fs::{PermissionsExt as _, symlink};
use std::time::Duration;

use super::*;

fn until() -> Instant {
    Instant::now() + Duration::from_secs(30)
}
fn capture(root: &File) -> HeldSourceReadSet {
    HeldSourceReadSet::capture(root.as_fd(), until()).unwrap()
}
fn fixture() -> (tempfile::TempDir, File) {
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir(temp.path().join("inputs")).unwrap();
    fs::write(temp.path().join("inputs/config.toml"), b"[net]\noffline=true\n").unwrap();
    fs::set_permissions(temp.path().join("inputs/config.toml"), fs::Permissions::from_mode(0o600))
        .unwrap();
    fs::write(temp.path().join("inputs/empty.toml"), b"").unwrap();
    fs::set_permissions(temp.path().join("inputs/empty.toml"), fs::Permissions::from_mode(0o644))
        .unwrap();
    let root = File::open(temp.path()).unwrap();
    (temp, root)
}

#[test]
fn actual_payload_empty_file_and_directory_use_the_same_bounded_read_set() {
    let (_temp, root) = fixture();
    let mut reads = capture(&root);
    let actual = reads.capture_input(root.as_fd(), Path::new("inputs/config.toml")).unwrap();
    assert!(
        actual == SourceRead::File { mode: 0o100600, bytes: b"[net]\noffline=true\n".to_vec() }
    );
    // The expectation route remains connected to exactly these captured bytes.
    assert!(
        reads.observe(root.as_fd(), Path::new("inputs/config.toml"), actual.clone()).unwrap()
            == actual
    );
    assert!(
        reads.capture_input(root.as_fd(), Path::new("inputs/empty.toml")).unwrap()
            == SourceRead::File { mode: 0o100644, bytes: Vec::new() }
    );
    assert!(
        reads.capture_input(root.as_fd(), Path::new("inputs")).unwrap() == SourceRead::Directory
    );
    assert_eq!(reads.bytes, b"[net]\noffline=true\n".len());
    assert_eq!(reads.selected_population(), 4); // same root, ancestor and two files
    reads.check_current(root.as_fd()).unwrap();
}

#[test]
fn absent_input_anchors_the_first_missing_component_and_never_rediscovers_it() {
    let (temp, root) = fixture();
    let mut reads = capture(&root);
    assert!(
        reads.capture_input(root.as_fd(), Path::new("inputs/missing/config.toml")).unwrap()
            == SourceRead::Absent
    );
    assert!(reads.directories.contains_key(Path::new("inputs")));
    assert!(matches!(reads.leaves.get(Path::new("inputs/missing")), Some(Leaf::Absent)));
    assert!(!reads.leaves.contains_key(Path::new("inputs/missing/config.toml")));
    let population = reads.selected_population();
    assert!(
        reads.capture_input(root.as_fd(), Path::new("inputs/missing/other.toml")).unwrap()
            == SourceRead::Absent
    );
    assert_eq!(reads.selected_population(), population);
    fs::create_dir(temp.path().join("inputs/missing")).unwrap();
    assert!(reads.check_current(root.as_fd()).is_err());
    fs::remove_dir(temp.path().join("inputs/missing")).unwrap();
    assert!(reads.capture_input(root.as_fd(), Path::new("inputs/missing/config.toml")).is_err());
}

#[test]
fn nofollow_leaf_and_ancestor_refusals_retain_the_original_parent_set() {
    for ancestor in [false, true] {
        let (temp, root) = fixture();
        if ancestor {
            symlink("inputs", temp.path().join("alias")).unwrap();
        } else {
            symlink("config.toml", temp.path().join("inputs/alias.toml")).unwrap();
        }
        let mut reads = capture(&root);
        let path = if ancestor { "alias/config.toml" } else { "inputs/alias.toml" };
        assert!(reads.capture_input(root.as_fd(), Path::new(path)).is_err());
        assert_eq!(reads.selected_population(), if ancestor { 1 } else { 2 });
        assert!(reads.check_current(root.as_fd()).is_err());
        assert_eq!(reads.root.metadata().unwrap().ino(), root.metadata().unwrap().ino());
    }
}

#[test]
fn oversize_failure_retains_the_actual_file_without_payload_allocation() {
    let (temp, root) = fixture();
    let path = temp.path().join("inputs/large.toml");
    File::create(&path).unwrap().set_len(MAX_FILE_BYTES as u64 + 1).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
    let mut reads = capture(&root);
    assert!(reads.capture_input(root.as_fd(), Path::new("inputs/large.toml")).is_err());
    let Some(Leaf::File { file, bytes, stamp, .. }) =
        reads.leaves.get(Path::new("inputs/large.toml"))
    else {
        panic!("same pending actual file must remain retained")
    };
    assert_eq!(file.metadata().unwrap().ino(), stamp.ino);
    assert!(bytes.is_empty());
    assert_eq!(reads.bytes, 0);
    assert_eq!(reads.selected_population(), 3);
    assert!(reads.check_current(root.as_fd()).is_err());
}

#[test]
fn shared_byte_bound_refusal_retains_the_pending_original_without_a_refund() {
    let (_temp, root) = fixture();
    let mut reads = capture(&root);
    reads.bytes = MAX_BYTES; // saturate the SAME existing global accounting guard
    assert!(reads.capture_input(root.as_fd(), Path::new("inputs/config.toml")).is_err());
    assert_eq!(reads.bytes, MAX_BYTES);
    let Some(Leaf::File { bytes, .. }) = reads.leaves.get(Path::new("inputs/config.toml")) else {
        panic!("same pending actual file must remain retained")
    };
    assert!(bytes.is_empty());
    assert!(reads.check_current(root.as_fd()).is_err());
}

#[test]
fn observed_nested_byte_drift_and_restore_permanently_quarantine_the_same_set() {
    let (temp, root) = fixture();
    let mut reads = capture(&root);
    let path = Path::new("inputs/config.toml");
    let original = reads.capture_input(root.as_fd(), path).unwrap();
    fs::write(temp.path().join(path), b"[net]\noffline=false\n").unwrap();
    assert!(reads.capture_input(root.as_fd(), path).is_err());
    let SourceRead::File { bytes, .. } = original else { panic!() };
    fs::write(temp.path().join(path), bytes).unwrap();
    assert!(reads.check_current(root.as_fd()).is_err());
    assert!(reads.capture_input(root.as_fd(), path).is_err());
    assert!(reads.leaves.contains_key(path));
}

#[test]
fn expiry_and_foreign_creator_refusals_never_restore_the_captured_issuer() {
    for expired in [false, true] {
        let (_temp, root) = fixture();
        let mut reads = capture(&root);
        let end = reads.deadline;
        let creator = reads.creator;
        if expired {
            reads.deadline = Instant::now();
        } else {
            reads.creator = creator.wrapping_add(1);
        }
        assert!(reads.capture_input(root.as_fd(), Path::new("inputs/config.toml")).is_err());
        reads.deadline = end;
        reads.creator = creator;
        assert!(reads.capture_input(root.as_fd(), Path::new("inputs/config.toml")).is_err());
        assert!(reads.check_current(root.as_fd()).is_err());
    }
}

#[test]
fn repeated_capture_preserves_original_file_and_root_description_state() {
    let (_temp, root) = fixture();
    let mut reads = capture(&root);
    let path = Path::new("inputs/config.toml");
    let first = reads.capture_input(root.as_fd(), path).unwrap();
    let Leaf::File { file, .. } = &reads.leaves[path] else { panic!() };
    let fd = file.as_raw_fd();
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    let local = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    let root_flags = unsafe { libc::fcntl(root.as_raw_fd(), libc::F_GETFL) };
    assert_eq!(flags & libc::O_ACCMODE, libc::O_RDONLY);
    assert_ne!(local & libc::FD_CLOEXEC, 0);
    assert_eq!(unsafe { libc::lseek(fd, 3, libc::SEEK_SET) }, 3);
    let second = reads.capture_input(root.as_fd(), path).unwrap();
    assert!(first == second);
    reads.check_current(root.as_fd()).unwrap();
    assert_eq!(reads.selected_population(), 3);
    assert_eq!(unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) }, 3);
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFL) }, flags);
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFD) }, local);
    assert_eq!(unsafe { libc::fcntl(root.as_raw_fd(), libc::F_GETFL) }, root_flags);
}
