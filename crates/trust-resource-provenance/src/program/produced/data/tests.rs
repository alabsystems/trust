// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Native file-custody controls only. No compiler, SDK, proof or retired
//! producer is fabricated; the actual graph must establish those separately.
use super::*;
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}
struct Fixture {
    root: tempfile::TempDir,
    output: HeldOutputRoot,
    selected: PathBuf,
}
impl Fixture {
    fn new(bytes: &[u8]) -> Self {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().canonicalize().unwrap();
        std::fs::create_dir_all(path.join("debug/deps")).unwrap();
        let selected = path.join("debug/deps/selected.rmeta");
        std::fs::write(&selected, bytes).unwrap();
        let output = HeldOutputRoot::open(&path, deadline()).unwrap();
        Self {
            root,
            output,
            selected,
        }
    }
}
fn read(original: &HeldRootFile) -> Vec<u8> {
    let file = File::from(
        original
            .descriptor(deadline())
            .unwrap()
            .try_clone_to_owned()
            .unwrap(),
    );
    let mut bytes = vec![0; original.observation().bytes as usize];
    file.read_exact_at(&mut bytes, 0).unwrap();
    bytes
}
#[test]
fn received_file_retains_the_original_ofd_and_refuses_equal_byte_substitutes() {
    use std::io::{Seek as _, SeekFrom};
    let fixture = Fixture::new(b"held original bytes");
    let mut original = File::open(&fixture.selected).unwrap();
    original.seek(SeekFrom::Start(3)).unwrap();
    let mut witness = original.try_clone().unwrap();
    let raw = original.as_raw_fd();
    let held = fixture
        .output
        .file_from_original(&fixture.selected, original, deadline())
        .unwrap();
    assert_eq!(held.descriptor(deadline()).unwrap().as_raw_fd(), raw);
    assert_eq!(
        witness.stream_position().unwrap(),
        3,
        "read_at capture must not consume the transferred OFD offset"
    );
    assert_eq!(read(&held), b"held original bytes");
    let other = fixture.selected.with_file_name("equal-bytes.rmeta");
    std::fs::write(&other, b"held original bytes").unwrap();
    assert!(
        fixture
            .output
            .file_from_original(&fixture.selected, File::open(&other).unwrap(), deadline())
            .is_err()
    );
    let writable = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&fixture.selected)
        .unwrap();
    assert!(
        fixture
            .output
            .file_from_original(&fixture.selected, writable, deadline())
            .is_err()
    );
    std::fs::write(&fixture.selected, b"late original mutation").unwrap();
    assert!(held.validate(deadline()).is_err());
    assert!(held.validate(deadline()).is_err());
}

#[test]
fn original_data_allows_zero_and_unrelated_outputs_without_becoming_an_executable() {
    for bytes in [b"".as_slice(), b"original binary\0rmeta\xff"] {
        let fixture = Fixture::new(bytes);
        let held = fixture.output.file(&fixture.selected, deadline()).unwrap();
        assert_eq!(held.observation().bytes, bytes.len() as u64);
        assert_eq!(read(&held), bytes);
        assert_eq!(
            held.descriptor_count(),
            3,
            "two held parents and actual file"
        );
        assert!(held.descriptor_count() <= HeldRootFile::capture_descriptor_bound());
        std::fs::write(
            fixture.selected.with_file_name("new-unrelated.rlib"),
            b"new output",
        )
        .unwrap();
        held.validate(deadline()).unwrap();
        drop(fixture.output);
        held.validate(deadline()).unwrap();
        assert_eq!(
            read(&held),
            bytes,
            "SAME output-root descriptor remains retained"
        );
        drop(held);
        drop(fixture.root);
    }
}

#[test]
fn selected_file_content_metadata_and_name_failures_are_sticky() {
    for kind in 0..4 {
        let fixture = Fixture::new(b"original bytes");
        let held = fixture.output.file(&fixture.selected, deadline()).unwrap();
        match kind {
            0 => std::fs::write(&fixture.selected, b"changed data of a different length").unwrap(),
            1 => {
                std::fs::set_permissions(&fixture.selected, std::fs::Permissions::from_mode(0o400))
                    .unwrap()
            }
            2 => {
                let old = fixture.selected.with_file_name("retained-old.rmeta");
                std::fs::rename(&fixture.selected, &old).unwrap();
                std::fs::write(&fixture.selected, b"original bytes").unwrap();
            }
            _ => {
                let old = fixture.selected.with_file_name("retained-old.rmeta");
                std::fs::rename(&fixture.selected, &old).unwrap();
                assert!(held.validate(deadline()).is_err());
                std::fs::rename(&old, &fixture.selected).unwrap();
            }
        }
        assert!(held.validate(deadline()).is_err(), "mutation {kind}");
        assert!(held.descriptor(deadline()).is_err());
        assert!(
            held.validate(deadline()).is_err(),
            "later bookend cannot clear failure"
        );
    }
}

#[test]
fn original_parent_substitution_cannot_be_cleared_by_renaming_it_back() {
    let fixture = Fixture::new(b"original");
    let held = fixture.output.file(&fixture.selected, deadline()).unwrap();
    let parent = fixture.selected.parent().unwrap();
    let moved = parent.with_file_name("retained-deps");
    std::fs::rename(parent, &moved).unwrap();
    std::fs::create_dir(parent).unwrap();
    std::fs::write(&fixture.selected, b"original").unwrap();
    assert!(held.validate(deadline()).is_err());
    std::fs::remove_file(&fixture.selected).unwrap();
    std::fs::remove_dir(parent).unwrap();
    std::fs::rename(&moved, parent).unwrap();
    assert!(
        held.validate(deadline()).is_err(),
        "observed parent ABA stays terminal"
    );
}

#[test]
fn selected_output_traversal_refuses_escape_symlinks_special_files_and_oversize() {
    let fixture = Fixture::new(b"original");
    assert!(
        fixture
            .output
            .file(fixture.output.path(), deadline())
            .is_err()
    );
    assert!(
        fixture
            .output
            .file(&fixture.output.path().join("debug/../escape"), deadline())
            .is_err()
    );
    assert!(
        fixture
            .output
            .file(&fixture.root.path().join("../outside"), deadline())
            .is_err()
    );
    let link = fixture.selected.with_file_name("symlink.rmeta");
    std::os::unix::fs::symlink(&fixture.selected, &link).unwrap();
    assert!(fixture.output.file(&link, deadline()).is_err());
    let parent_link = fixture.output.path().join("alias");
    std::os::unix::fs::symlink(fixture.selected.parent().unwrap(), &parent_link).unwrap();
    assert!(
        fixture
            .output
            .file(&parent_link.join("selected.rmeta"), deadline())
            .is_err()
    );
    let fifo = fixture.selected.with_file_name("fifo.rmeta");
    let name = CString::new(fifo.as_os_str().as_bytes()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    assert!(fixture.output.file(&fifo, deadline()).is_err());
    let large = fixture.selected.with_file_name("oversize.rlib");
    File::create(&large)
        .unwrap()
        .set_len(MAX_BYTES + 1)
        .unwrap();
    assert!(fixture.output.file(&large, deadline()).is_err());
}

#[test]
fn a_late_failed_bookend_does_not_become_valid_with_a_fresh_deadline() {
    let fixture = Fixture::new(b"original");
    let held = fixture.output.file(&fixture.selected, deadline()).unwrap();
    let original = fixture.selected.with_extension("retained-original");
    std::fs::rename(&fixture.selected, &original).unwrap();
    std::fs::write(&fixture.selected, b"different backing").unwrap();
    assert!(
        held.validate(deadline()).is_err(),
        "observe genuine structural drift under the full hang budget"
    );
    std::fs::remove_file(&fixture.selected).unwrap();
    std::fs::rename(original, &fixture.selected).unwrap();
    assert!(held.validate(Instant::now()).is_err());
    assert!(
        held.validate(deadline()).is_err(),
        "restoring a name and deadline cannot clear structural drift"
    );
}

#[test]
fn retained_originals_use_each_current_operation_deadline_without_erasing_timeouts_or_drift() {
    // Real FS originals only. No CPU, SDK, publisher or compiler grant is
    // fabricated; actual grant/Root deadlines remain their callers' concern.
    let temp = tempfile::tempdir().unwrap();
    let root_path = temp.path().canonicalize().unwrap();
    let directory_path = root_path.join("unit");
    std::fs::create_dir(&directory_path).unwrap();
    let file_path = directory_path.join("libfixture.rmeta");
    std::fs::write(&file_path, b"captured data, no metadata eligibility").unwrap();
    let capture_deadline = deadline();
    let output = HeldOutputRoot::open(&root_path, capture_deadline).unwrap();
    let directory = output.directory(&directory_path, capture_deadline).unwrap();
    let file = output.file(&file_path, capture_deadline).unwrap();
    // An independently expired CURRENT operation must refuse without IO or
    // borrowing a descriptor. Actual setup retains the one-minute hang budget;
    // no scheduler-latency assertion or shortened capture deadline is used.
    let expired_operation = Instant::now();
    assert_eq!(
        directory.validate(expired_operation).unwrap_err().kind(),
        std::io::ErrorKind::TimedOut
    );
    assert_eq!(
        file.validate(expired_operation).unwrap_err().kind(),
        std::io::ErrorKind::TimedOut
    );
    let next_deadline = deadline();
    directory.validate(next_deadline).unwrap();
    file.validate(next_deadline).unwrap();
    // Positive revalidation belongs to this separate current operation. The
    // earlier timeout still refuses when presented again.
    assert_eq!(
        file.validate(expired_operation).unwrap_err().kind(),
        std::io::ErrorKind::TimedOut
    );
    let moved = root_path.join("retired-unit");
    std::fs::rename(&directory_path, &moved).unwrap();
    std::fs::create_dir(&directory_path).unwrap();
    assert!(directory.validate(next_deadline).is_err());
    assert!(file.validate(next_deadline).is_err());
    std::fs::remove_dir(&directory_path).unwrap();
    std::fs::rename(&moved, &directory_path).unwrap();
    assert!(
        directory.validate(next_deadline).is_err(),
        "restoring the original name cannot erase structural drift"
    );
    assert!(
        file.validate(next_deadline).is_err(),
        "restoring the original name cannot erase structural drift"
    );
}
