//! Actual physical files only, without semantic source/Graph/native owners.
use std::fs;
use std::os::unix::fs::{PermissionsExt as _, symlink};
use std::time::Duration;

use super::*;

fn until() -> Instant {
    Instant::now() + Duration::from_secs(30)
}
fn source() -> (tempfile::TempDir, File, HeldSourceReadSet) {
    let temp = tempfile::tempdir().unwrap();
    fs::create_dir(temp.path().join("archives")).unwrap();
    let file = File::create(temp.path().join("archives/seed.tar.xz")).unwrap();
    file.set_len(MAX_FILE_BYTES as u64 + 4096).unwrap();
    fs::set_permissions(
        temp.path().join("archives/seed.tar.xz"),
        fs::Permissions::from_mode(0o644),
    )
    .unwrap();
    let root = File::open(temp.path()).unwrap();
    let reads = HeldSourceReadSet::capture(root.as_fd(), until()).unwrap();
    (temp, root, reads)
}
fn offer(reads: HeldSourceReadSet, root: &File) -> HeldSourceFileOffer {
    reads
        .into_readonly_file_offer(root.as_fd(), Path::new("archives/seed.tar.xz"), MAX_OFFER_BYTES)
        .unwrap_or_else(|error| panic!("{}", error.error()))
}

#[test]
fn large_original_is_not_buffered_and_outlives_caller_handles_then_closes_its_population() {
    let (_temp, root, reads) = source();
    let end = reads.original_deadline();
    let demand = reads.file_offer_descriptor_bound(Path::new("archives/seed.tar.xz")).unwrap();
    let offered = offer(reads, &root);
    assert_eq!(offered.relative(), Path::new("archives/seed.tar.xz"));
    assert_eq!(offered.original_deadline(), end);
    assert_eq!(offered.bytes().unwrap(), MAX_FILE_BYTES as u64 + 4096);
    assert_eq!(offered.reads.bytes, 0);
    assert!(offered.reads.leaves.is_empty());
    assert!(offered.descriptor_population() + 2 <= demand);
    let root_fd = offered.reads.root.as_raw_fd();
    let ancestor_fd = offered.reads.directories[Path::new("archives")].file.as_raw_fd();
    let file_fd = offered.descriptor().unwrap().as_raw_fd();
    let identities: Vec<_> = [root_fd, ancestor_fd, file_fd]
        .into_iter()
        .map(|fd| {
            let mut info = std::mem::MaybeUninit::<libc::stat>::uninit();
            assert_eq!(unsafe { libc::fstat(fd, info.as_mut_ptr()) }, 0);
            let info = unsafe { info.assume_init() };
            (fd, info.st_dev, info.st_ino)
        })
        .collect();
    drop(root);
    offered.check_current().unwrap();
    let mut byte = 0u8;
    assert_eq!(unsafe { libc::pread(file_fd, (&mut byte as *mut u8).cast(), 1, 0) }, 1);
    drop(offered);
    for (fd, device, inode) in identities {
        let mut info = std::mem::MaybeUninit::<libc::stat>::uninit();
        if unsafe { libc::fstat(fd, info.as_mut_ptr()) } == 0 {
            // Another concurrently running physical control may reuse this
            // descriptor number, but cannot reuse this still-linked fixture.
            let info = unsafe { info.assume_init() };
            assert_ne!((info.st_dev, info.st_ino), (device, inode));
        } else {
            assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EBADF));
        }
    }
}

#[test]
fn descriptor_bookends_preserve_the_original_cursor_and_flags() {
    let (_temp, root, reads) = source();
    let offered = offer(reads, &root);
    let fd = offered.descriptor().unwrap().as_raw_fd();
    let before = flags(&offered.file).unwrap();
    assert_eq!(unsafe { libc::lseek(fd, 19, libc::SEEK_SET) }, 19);
    offered.check_current().unwrap();
    offered.bytes().unwrap();
    assert_eq!(unsafe { libc::lseek(fd, 0, libc::SEEK_CUR) }, 19);
    assert_eq!(flags(&offered.file).unwrap(), before);
}

#[test]
fn readonly_offer_keeps_the_buffered_reader_limit_unchanged() {
    let (_temp, root, mut reads) = source();
    let expected = SourceRead::File { mode: 0o100644, bytes: vec![0; MAX_FILE_BYTES + 4096] };
    assert!(reads.observe(root.as_fd(), Path::new("archives/seed.tar.xz"), expected).is_err());
    assert!(reads.check_current(root.as_fd()).is_err());
}

#[test]
fn nofollow_leaf_ancestor_and_original_root_refusals_keep_failed_custody() {
    for ancestor in [false, true] {
        let (temp, root, _reads) = source();
        if ancestor {
            fs::rename(temp.path().join("archives"), temp.path().join("actual")).unwrap();
            symlink("actual", temp.path().join("archives")).unwrap();
        } else {
            fs::rename(temp.path().join("archives/seed.tar.xz"), temp.path().join("archives/real"))
                .unwrap();
            symlink("real", temp.path().join("archives/seed.tar.xz")).unwrap();
        }
        let reads = HeldSourceReadSet::capture(root.as_fd(), until()).unwrap();
        let error = reads
            .into_readonly_file_offer(
                root.as_fd(),
                Path::new("archives/seed.tar.xz"),
                MAX_OFFER_BYTES,
            )
            .err()
            .unwrap();
        assert!(error.reads.revoked.load(Ordering::Acquire));
        assert!(error.descriptor_population() >= 1);
        assert!(error.reads.check_current(root.as_fd()).is_err());
    }
    let (_temp, _root, reads) = source();
    let wrong = tempfile::tempdir().unwrap();
    let wrong = File::open(wrong.path()).unwrap();
    let error = reads
        .into_readonly_file_offer(wrong.as_fd(), Path::new("archives/seed.tar.xz"), MAX_OFFER_BYTES)
        .err()
        .unwrap();
    assert!(error.reads.revoked.load(Ordering::Acquire));
}

#[test]
fn file_drift_and_restore_permanently_refuse_the_same_offer() {
    let (temp, root, reads) = source();
    let offered = offer(reads, &root);
    fs::write(temp.path().join("archives/seed.tar.xz"), b"changed").unwrap();
    assert!(offered.check_current().is_err());
    let file = File::create(temp.path().join("archives/seed.tar.xz")).unwrap();
    file.set_len(MAX_FILE_BYTES as u64 + 4096).unwrap();
    assert!(offered.descriptor().is_err());
}

#[test]
fn renamed_ancestor_and_replaced_leaf_never_rebind_the_retained_original() {
    for ancestor in [false, true] {
        let (temp, root, reads) = source();
        let offered = offer(reads, &root);
        let path = if ancestor { "archives" } else { "archives/seed.tar.xz" };
        let moved = if ancestor { "moved" } else { "archives/moved" };
        fs::rename(temp.path().join(path), temp.path().join(moved)).unwrap();
        if !ancestor {
            fs::write(temp.path().join(path), b"replacement").unwrap();
        }
        assert!(offered.check_current().is_err());
        if !ancestor {
            fs::remove_file(temp.path().join(path)).unwrap();
        }
        fs::rename(temp.path().join(moved), temp.path().join(path)).unwrap();
        assert!(offered.check_current().is_err());
    }
}

#[test]
fn original_population_and_byte_permission_link_bounds_are_not_replaced() {
    for maximum in [0, MAX_OFFER_BYTES + 1, MAX_FILE_BYTES as u64] {
        let (_temp, root, reads) = source();
        let failed = reads
            .into_readonly_file_offer(root.as_fd(), Path::new("archives/seed.tar.xz"), maximum)
            .err()
            .unwrap();
        assert!(failed.reads.revoked.load(Ordering::Acquire));
        assert_eq!(failed.original_deadline(), failed.reads.original_deadline());
    }
    for mode in [0o664, 0o646] {
        let (temp, root, reads) = source();
        fs::set_permissions(
            temp.path().join("archives/seed.tar.xz"),
            fs::Permissions::from_mode(mode),
        )
        .unwrap();
        let failed = reads
            .into_readonly_file_offer(
                root.as_fd(),
                Path::new("archives/seed.tar.xz"),
                MAX_OFFER_BYTES,
            )
            .err()
            .unwrap();
        assert!(failed.pending.is_some());
    }
    let (temp, root, reads) = source();
    fs::hard_link(temp.path().join("archives/seed.tar.xz"), temp.path().join("archives/alias"))
        .unwrap();
    assert!(
        reads
            .into_readonly_file_offer(
                root.as_fd(),
                Path::new("archives/seed.tar.xz"),
                MAX_OFFER_BYTES
            )
            .is_err()
    );
}

#[test]
fn earlier_selected_inputs_remain_part_of_the_consumed_offer() {
    let (temp, root, _reads) = source();
    fs::write(temp.path().join("pin"), b"original").unwrap();
    fs::set_permissions(temp.path().join("pin"), fs::Permissions::from_mode(0o644)).unwrap();
    let mut reads = HeldSourceReadSet::capture(root.as_fd(), until()).unwrap();
    reads
        .observe(
            root.as_fd(),
            Path::new("pin"),
            SourceRead::File { mode: 0o100644, bytes: b"original".to_vec() },
        )
        .unwrap();
    let offered = offer(reads, &root);
    fs::write(temp.path().join("pin"), b"modified").unwrap();
    assert!(offered.check_current().is_err());
    fs::write(temp.path().join("pin"), b"original").unwrap();
    assert!(offered.check_current().is_err());
}

#[test]
fn expired_and_flag_modified_offers_cannot_revive() {
    let (_temp, root, reads) = source();
    let offered = offer(reads, &root);
    let fd = offered.descriptor().unwrap().as_raw_fd();
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_SETFD, 0) }, 0);
    assert!(offered.check_current().is_err());
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
    assert!(offered.check_current().is_err());
    let (_temp, root, _reads) = source();
    let end = Instant::now() + Duration::from_millis(40);
    let reads = HeldSourceReadSet::capture(root.as_fd(), end).unwrap();
    let offered = offer(reads, &root);
    std::thread::sleep(Duration::from_millis(45));
    assert_eq!(offered.check_current().unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert!(offered.descriptor().is_err());
}

#[test]
fn actual_foreign_process_cannot_validate_the_inherited_physical_offer() {
    let (_temp, root, reads) = source();
    let offered = offer(reads, &root);
    // Only this real fork's creator check is exercised. This does not test or
    // authorize any production native NoFork/loan/settlement capability.
    let child = unsafe { libc::fork() };
    assert!(child >= 0);
    if child == 0 {
        let refused = offered.check_current().is_err();
        unsafe { libc::_exit(if refused { 0 } else { 1 }) }
    }
    let mut status = 0;
    assert_eq!(unsafe { libc::waitpid(child, &mut status, 0) }, child);
    assert!(libc::WIFEXITED(status));
    assert_eq!(libc::WEXITSTATUS(status), 0);
    offered.check_current().unwrap();
}

#[test]
fn advertised_two_scratch_descriptors_suffice_under_real_descriptor_pressure() {
    const CHILD: &str = "TRUST_PHYSICAL_FILE_OFFER_PRESSURE_TEST_CHILD";
    if std::env::var_os(CHILD).is_none() {
        // A separate instance of THIS test image restricts only its own file
        // table. This selector creates no production owner or capability.
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "program::selected_source::file_offer::tests::advertised_two_scratch_descriptors_suffice_under_real_descriptor_pressure",
                "--exact", "--nocapture", "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        return;
    }
    let (_temp, root, reads) = source();
    let offered = offer(reads, &root);
    drop(root);
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) }, 0);
    let mut limit = unsafe { limit.assume_init() };
    limit.rlim_cur = limit.rlim_cur.min(256);
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
    let mut fillers = Vec::new();
    loop {
        match File::open("/dev/null") {
            Ok(file) => fillers.push(file),
            Err(error) => {
                assert_eq!(error.raw_os_error(), Some(libc::EMFILE));
                break;
            }
        }
    }
    assert!(fillers.len() >= 2);
    drop(fillers.pop());
    drop(fillers.pop());
    offered.check_current().unwrap();
    offered.descriptor().unwrap();
    offered.bytes().unwrap();
}
