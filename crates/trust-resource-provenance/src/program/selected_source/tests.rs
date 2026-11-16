//! Actual physical guards only: no Manager, native Job, selection or SDK role.
use std::fs;
use std::os::fd::AsFd as _;
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use super::*;

#[test]
fn original_file_reads_leave_the_retained_description_cursor_and_flags_unchanged() {
    let temp = tempfile::tempdir().unwrap();
    let bytes = b"[package]\nname='original'\n";
    fs::write(temp.path().join("Cargo.toml"), bytes).unwrap();
    fs::set_permissions(temp.path().join("Cargo.toml"), fs::Permissions::from_mode(0o644)).unwrap();
    let root = File::open(temp.path()).unwrap();
    let mut reads =
        HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30)).unwrap();
    let wanted = SourceRead::File { mode: 0o100644, bytes: bytes.to_vec() };
    reads.observe(root.as_fd(), Path::new("Cargo.toml"), wanted.clone()).unwrap();
    let Leaf::File { file, .. } = &reads.leaves[Path::new("Cargo.toml")] else { panic!() };
    let fd = file.as_raw_fd();
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    assert_eq!(unsafe { libc::lseek(fd, 3, libc::SEEK_SET) }, 3);
    reads.observe(root.as_fd(), Path::new("Cargo.toml"), wanted).unwrap();
    reads.check_current(root.as_fd()).unwrap();
    assert_eq!(unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) }, 3);
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFL) }, flags);
}

#[test]
fn arbitrary_paths_cannot_escape_or_become_canonical_relative_inputs() {
    let temp = tempfile::tempdir().unwrap();
    let root = File::open(temp.path()).unwrap();
    for path in ["../outside", "./file", "nested//file", "nested/../file", "/absolute", ""] {
        let mut reads =
            HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30))
                .unwrap();
        assert!(
            reads.observe(root.as_fd(), Path::new(path), SourceRead::Absent).is_err(),
            "{path}"
        );
        assert!(reads.check_current(root.as_fd()).is_err());
    }
}

#[test]
fn actual_listings_keep_literal_kinds_original_cursor_and_sticky_namespace() {
    use std::os::unix::fs::symlink;
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir(temp.path().join("members")).unwrap();
    fs::create_dir(temp.path().join("members/committed")).unwrap();
    fs::create_dir(temp.path().join("members/untracked")).unwrap();
    fs::write(temp.path().join("members/file"), b"ordinary file").unwrap();
    symlink("committed", temp.path().join("members/alias")).unwrap();
    let root = File::open(temp.path()).unwrap();
    let mut reads =
        HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30)).unwrap();
    let listing = reads.directory_entries(root.as_fd(), Path::new("members")).unwrap();
    assert!(
        listing
            .iter()
            .any(|entry| entry.name == b"untracked" && entry.kind == SourceEntryKind::Directory)
    );
    assert!(
        listing.iter().any(|entry| entry.name == b"alias" && entry.kind == SourceEntryKind::Link)
    );
    assert!(
        listing.iter().any(|entry| entry.name == b"file" && entry.kind == SourceEntryKind::File)
    );
    let fd = reads.directories[Path::new("members")].file.as_raw_fd();
    let cursor = unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) };
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    reads.directory_entries(root.as_fd(), Path::new("members")).unwrap();
    assert_eq!(unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) }, cursor);
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFL) }, flags);
    fs::rename(temp.path().join("members/untracked"), temp.path().join("members/moved")).unwrap();
    assert!(reads.check_current(root.as_fd()).is_err());
    fs::rename(temp.path().join("members/moved"), temp.path().join("members/untracked")).unwrap();
    assert!(reads.check_current(root.as_fd()).is_err());
}

#[test]
fn listing_capture_keeps_global_population_and_retained_byte_bounds() {
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir(temp.path().join("members")).unwrap();
    fs::write(temp.path().join("members/file"), b"file").unwrap();
    let root = File::open(temp.path()).unwrap();
    let mut reads =
        HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30)).unwrap();
    for index in 0..MAX_DESCRIPTORS - 1 {
        reads.leaves.insert(PathBuf::from(format!("absent-{index}")), Leaf::Absent);
    }
    assert!(reads.directory_entries(root.as_fd(), Path::new("members")).is_err());
    assert_eq!(reads.selected_population(), MAX_DESCRIPTORS);
    let mut reads =
        HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30)).unwrap();
    reads.bytes = MAX_BYTES;
    assert!(reads.directory_entries(root.as_fd(), Path::new("members")).is_err());
    assert!(reads.check_current(root.as_fd()).is_err());
}

#[test]
fn root_listing_uses_original_endpoint_and_never_follows_directory_links() {
    use std::os::unix::fs::symlink;
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir(temp.path().join("real")).unwrap();
    symlink("real", temp.path().join("alias")).unwrap();
    let root = File::open(temp.path()).unwrap();
    let mut reads =
        HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30)).unwrap();
    reads.directory_entries(root.as_fd(), Path::new(".")).unwrap();
    assert!(reads.directory_entries(root.as_fd(), Path::new("alias")).is_err());
    let mut reads =
        HeldSourceReadSet::capture(root.as_fd(), Instant::now() + Duration::from_secs(30)).unwrap();
    reads.deadline = Instant::now();
    assert!(reads.directory_entries(root.as_fd(), Path::new(".")).is_err());
}
