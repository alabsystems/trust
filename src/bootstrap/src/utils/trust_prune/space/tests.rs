// Trust: real filesystem boundaries for native cleanup observations.

use std::fs::{self, OpenOptions};
use std::os::unix::fs::{OpenOptionsExt, symlink};

use super::*;

// Tests lend observation-only directory descriptions. Production gets this
// exact anchor only from its actual independently held OutputLock.
fn open_directory(path: &Path) -> File {
    OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(path)
        .unwrap()
}
fn accounting(root: &Path) -> Accounting {
    Accounting::new(root, open_directory(root).as_fd()).unwrap()
}

fn file(path: &Path) -> PathBuf {
    fs::write(path, [0xa5; 65536]).unwrap();
    path.to_owned()
}

fn allocated(path: &Path) -> u64 {
    let meta = fs::metadata(path).unwrap();
    (meta.blocks() * 512).max(meta.len())
}

#[test]
fn all_selected_hard_links_count_once_and_outside_links_count_zero() {
    let root = tempfile::tempdir().unwrap();
    let a = file(&root.path().join("a"));
    let b = root.path().join("b");
    fs::hard_link(&a, &b).unwrap();
    let mut one = accounting(root.path());
    one.collect(std::slice::from_ref(&a)).unwrap();
    let estimate = one.finish().unwrap();
    assert_eq!((estimate.counted_inodes, estimate.allocated_upper_bytes), (0, 0));
    let mut both = accounting(root.path());
    both.collect(&[a.clone(), b]).unwrap();
    let estimate = both.finish().unwrap();
    assert_eq!(estimate.counted_inodes, 1);
    assert_eq!(estimate.allocated_upper_bytes, allocated(&a));
}

#[test]
fn complete_cross_tree_links_are_measured_before_an_earlier_tree_is_removed() {
    let root = tempfile::tempdir().unwrap();
    let a = file(&root.path().join("a"));
    let b = root.path().join("b");
    fs::hard_link(&a, &b).unwrap();
    let mut accounting = accounting(root.path());
    accounting.collect(std::slice::from_ref(&a)).unwrap();
    accounting.collect(std::slice::from_ref(&b)).unwrap();
    let estimate = accounting.finish().unwrap();
    fs::remove_file(&a).unwrap();
    assert_eq!(estimate.counted_inodes, 1);
    assert_eq!(estimate.allocated_upper_bytes, allocated(&b));
}

#[test]
fn overlapping_paths_count_once_and_directory_links_are_not_followed() {
    let root = tempfile::tempdir().unwrap();
    let directory = root.path().join("selected");
    fs::create_dir(&directory).unwrap();
    let selected = file(&directory.join("file"));
    let outside = root.path().join("outside");
    fs::create_dir(&outside).unwrap();
    file(&outside.join("kept"));
    symlink(&outside, directory.join("link")).unwrap();
    let mut accounting = accounting(root.path());
    accounting.collect(&[directory, selected.clone(), selected.clone()]).unwrap();
    let estimate = accounting.finish().unwrap();
    assert_eq!(estimate.counted_inodes, 2); // Original file and symlink inode only.
    assert!(estimate.allocated_upper_bytes >= allocated(&selected));
    assert!(
        estimate.allocated_upper_bytes < allocated(&selected) + allocated(&outside.join("kept"))
    );
}

#[test]
fn missing_inventory_is_an_error_and_never_a_zero_estimate() {
    let root = tempfile::tempdir().unwrap();
    assert!(accounting(root.path()).collect(&[root.path().join("missing")]).is_err());
}

#[test]
fn volume_observation_keeps_its_original_directory_after_path_removal() {
    let root = tempfile::tempdir().unwrap();
    let directory = root.path().join("build");
    fs::create_dir(&directory).unwrap();
    let original = open_directory(&directory);
    let before = VolumeBefore::capture(original.as_fd()).unwrap();
    fs::remove_dir(&directory).unwrap();
    let result = before.finish().unwrap();
    assert!(result.available_before_bytes > 0);
    assert!(result.available_after_bytes > 0);
}

#[cfg(target_os = "macos")]
#[test]
fn native_clone_private_size_is_distinct_from_its_allocated_upper_bound() {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    let root = tempfile::tempdir().unwrap();
    let source = file(&root.path().join("source"));
    let clone = root.path().join("clone");
    let source_name = CString::new(source.as_os_str().as_bytes()).unwrap();
    let clone_name = CString::new(clone.as_os_str().as_bytes()).unwrap();
    // SAFETY: both names are live NUL-terminated paths; destination is absent.
    assert_eq!(
        unsafe { libc::clonefile(source_name.as_ptr(), clone_name.as_ptr(), 0) },
        0,
        "native clone fixture: {}",
        io::Error::last_os_error()
    );
    let mut accounting = accounting(root.path());
    accounting.collect(std::slice::from_ref(&source)).unwrap();
    let estimate = accounting.finish().unwrap();
    assert_eq!(estimate.allocated_upper_bytes, allocated(&source));
    assert_eq!(estimate.private_lower_bytes, Some(0));
    assert_eq!(fs::read(clone).unwrap(), fs::read(source).unwrap());
}

#[cfg(target_os = "macos")]
#[test]
fn fifo_substitution_cannot_block_private_allocation_observation() {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    use std::sync::mpsc;
    use std::time::Duration;
    let root = tempfile::tempdir().unwrap();
    let path = file(&root.path().join("member"));
    let parent = open_directory(root.path());
    let before = Snapshot::metadata(&fs::symlink_metadata(&path).unwrap());
    fs::remove_file(&path).unwrap();
    let name = CString::new(path.as_os_str().as_bytes()).unwrap();
    // SAFETY: name is a live NUL-terminated path; the old file is absent.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let (send, receive) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        send.send(private_size(parent.as_fd(), OsStr::new("member"), &before)).unwrap();
    });
    // A hang detector, not a latency budget. On a broken implementation the
    // owned fallback reader/writer unblocks its read-only open before joining.
    let result = receive.recv_timeout(Duration::from_secs(60));
    let unblock = result.is_err().then(|| {
        OpenOptions::new()
            .read(true)
            .write(true)
            .custom_flags(libc::O_NONBLOCK)
            .open(&path)
            .unwrap()
    });
    worker.join().unwrap();
    drop(unblock);
    assert_eq!(result.unwrap(), None);
}

#[test]
fn deleting_a_selected_link_then_adding_an_outside_link_invalidates_the_census() {
    let root = tempfile::tempdir().unwrap();
    let a = file(&root.path().join("a"));
    let b = root.path().join("b");
    let outside = root.path().join("outside");
    fs::hard_link(&a, &b).unwrap();
    let mut selected = accounting(root.path());
    selected.collect(std::slice::from_ref(&a)).unwrap();
    fs::remove_file(&a).unwrap();
    fs::hard_link(&b, &outside).unwrap();
    let result = selected.collect(std::slice::from_ref(&b)).and_then(|()| selected.finish());
    assert!(result.is_err(), "outside hardlink must not be counted as freed: {result:?}");
    assert_eq!(fs::read(&outside).unwrap(), fs::read(&b).unwrap());
    assert_eq!(fs::metadata(&outside).unwrap().nlink(), 2);
}

#[test]
fn outside_link_added_after_the_last_collect_invalidates_finish() {
    let root = tempfile::tempdir().unwrap();
    let selected = file(&root.path().join("selected"));
    let outside = root.path().join("outside");
    let mut inventory = accounting(root.path());
    inventory.collect(std::slice::from_ref(&selected)).unwrap();
    fs::hard_link(&selected, &outside).unwrap();
    assert!(inventory.finish().is_err());
    assert_eq!(fs::read(&selected).unwrap(), fs::read(outside).unwrap());
}

#[cfg(target_os = "macos")]
#[test]
fn private_size_uses_the_original_parent_while_its_name_is_an_outside_alias() {
    let root = tempfile::tempdir().unwrap();
    let selected = root.path().join("selected");
    let original = root.path().join("original-selected");
    let outside = root.path().join("outside");
    fs::create_dir(&selected).unwrap();
    fs::create_dir(&outside).unwrap();
    let path = file(&selected.join("member"));
    fs::write(outside.join("member"), vec![0xb6; 2 * 1024 * 1024]).unwrap();
    let parent = open_directory(&selected);
    let before = Snapshot::metadata(&fs::symlink_metadata(&path).unwrap());
    let expected = private_size(parent.as_fd(), OsStr::new("member"), &before);
    fs::rename(&selected, &original).unwrap();
    symlink(&outside, &selected).unwrap();
    let observed = private_size(parent.as_fd(), OsStr::new("member"), &before);
    fs::remove_file(&selected).unwrap();
    fs::rename(&original, &selected).unwrap();
    assert_eq!(observed, expected);
    assert_eq!(fs::read(path).unwrap(), vec![0xa5; 65536]);
    assert_eq!(fs::read(outside.join("member")).unwrap(), vec![0xb6; 2 * 1024 * 1024]);
}

#[test]
fn directory_symlink_aba_never_inventories_the_outside_namespace() {
    use std::sync::{Arc, Mutex};
    let root = tempfile::tempdir().unwrap();
    let directory = root.path().join("selected");
    let original = root.path().join("original-selected");
    let outside = root.path().join("outside");
    fs::create_dir(&directory).unwrap();
    fs::create_dir(&outside).unwrap();
    let inside_file = file(&directory.join("inside"));
    fs::write(outside.join("outside-only"), vec![0xb6; 2 * 1024 * 1024]).unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let observed = Arc::clone(&seen);
    let selected = directory.clone();
    let outside_name = outside.clone();
    let mut inventory = accounting(root.path());
    inventory.observer = Some(Box::new(move |path, point| {
        if point == Point::ObservedLeaf {
            observed.lock().unwrap().push(path.to_owned());
        }
        if path != Path::new("selected") {
            return;
        }
        match point {
            Point::OpenedDirectory => {
                fs::rename(&selected, &original).unwrap();
                symlink(&outside_name, &selected).unwrap();
            }
            Point::ListedDirectory => {
                fs::remove_file(&selected).unwrap();
                fs::rename(&original, &selected).unwrap();
            }
            Point::ObservedLeaf => unreachable!(),
        }
    }));
    let result =
        inventory.collect(std::slice::from_ref(&directory)).and_then(|()| inventory.finish());
    assert_eq!(&*seen.lock().unwrap(), &[PathBuf::from("selected/inside")]);
    if let Ok(estimate) = result {
        assert_eq!(estimate.counted_inodes, 1);
        assert_eq!(estimate.allocated_upper_bytes, allocated(&inside_file));
    }
    assert_eq!(fs::read(&inside_file).unwrap(), vec![0xa5; 65536]);
    assert_eq!(fs::read(outside.join("outside-only")).unwrap(), vec![0xb6; 2 * 1024 * 1024]);
}

#[test]
fn enumeration_does_not_move_the_original_directory_description_cursor() {
    let root = tempfile::tempdir().unwrap();
    let path = file(&root.path().join("selected"));
    let directory = open_directory(root.path());
    let original = unsafe { libc::lseek(directory.as_raw_fd(), 0, libc::SEEK_CUR) };
    assert!(original >= 0);
    let mut inventory = Accounting::new(root.path(), directory.as_fd()).unwrap();
    inventory.collect(&[root.path().to_owned(), path]).unwrap();
    assert_eq!(inventory.finish().unwrap().counted_inodes, 1);
    assert_eq!(unsafe { libc::lseek(directory.as_raw_fd(), 0, libc::SEEK_CUR) }, original);
}
