// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;
use std::os::unix::fs::{PermissionsExt as _, symlink};
use std::process::Command;

fn item(root: &Path, name: &str, mode: &str, sha256: bool) -> Item {
    let repository = tempfile::tempdir().unwrap();
    let format = if sha256 { "sha256" } else { "sha1" };
    let initialized = Command::new("git")
        .args(["init", "--quiet", "--object-format", format])
        .arg(repository.path())
        .output()
        .unwrap();
    assert!(
        initialized.status.success(),
        "{}",
        String::from_utf8_lossy(&initialized.stderr)
    );
    let output = if mode == "120000" {
        let target = fs::read_link(root.join(name)).unwrap();
        use std::os::unix::ffi::OsStrExt as _;
        let mut child = Command::new("git")
            .arg("-C")
            .arg(repository.path())
            .args(["hash-object", "--stdin"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(target.as_os_str().as_bytes())
            .unwrap();
        child.wait_with_output().unwrap()
    } else {
        Command::new("git")
            .arg("-C")
            .arg(repository.path())
            .args(["hash-object", "--no-filters", "--"])
            .arg(root.join(name))
            .output()
            .unwrap()
    };
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Item {
        path: base64::engine::general_purpose::STANDARD.encode(name.as_bytes()),
        mode: mode.to_owned(),
        oid: String::from_utf8(output.stdout).unwrap().trim().to_owned(),
    }
}

fn batch(root: &Path, items: Vec<Item>) -> Batch {
    use std::os::unix::ffi::OsStrExt as _;
    Batch {
        schema: SCHEMA.to_owned(),
        nonce: "ab".repeat(32),
        repo: base64::engine::general_purpose::STANDARD.encode(root.as_os_str().as_bytes()),
        items,
    }
}

#[test]
fn real_git_sha1_sha256_regular_executable_and_link_bytes_agree() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    fs::write(root.join("plain"), b"actual bytes\n").unwrap();
    fs::write(root.join("run"), b"#!/bin/sh\n").unwrap();
    fs::set_permissions(root.join("run"), fs::Permissions::from_mode(0o755)).unwrap();
    symlink("plain", root.join("link")).unwrap();
    for sha256 in [false, true] {
        let input = batch(
            &root,
            vec![
                item(&root, "plain", "100644", sha256),
                item(&root, "run", "100755", sha256),
                item(&root, "link", "120000", sha256),
            ],
        );
        let (checked, bytes, failures) = check_batch(&input, 2).unwrap();
        assert_eq!((checked, bytes), (3, 28));
        assert!(failures.is_empty());
    }
    // Match the original reader's IXUSR test exactly, not "any execute bit".
    fs::set_permissions(root.join("plain"), fs::Permissions::from_mode(0o645)).unwrap();
    assert!(
        check_batch(
            &batch(&root, vec![item(&root, "plain", "100644", false)]),
            1
        )
        .unwrap()
        .2
        .is_empty()
    );
}

#[test]
fn unchanged_input_is_reread_and_restored_mtime_cannot_hide_changed_bytes() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    let file = root.join("body");
    let contents = vec![b'a'; 2 * 1024 * 1024 + 17];
    fs::write(&file, &contents).unwrap();
    let input = batch(&root, vec![item(&root, "body", "100644", false)]);
    let expected = (1, contents.len() as u64);
    for _ in 0..2 {
        let (checked, bytes, failures) = check_batch(&input, 1).unwrap();
        assert_eq!((checked, bytes), expected);
        assert!(failures.is_empty());
    }
    let old = filetime::FileTime::from_last_modification_time(&fs::metadata(&file).unwrap());
    let mut changed = contents.clone();
    let middle = changed.len() / 2;
    changed[middle] = b'b';
    fs::write(&file, changed).unwrap();
    filetime::set_file_mtime(&file, old).unwrap();
    assert!(!check_batch(&input, 1).unwrap().2.is_empty());
    fs::write(&file, contents).unwrap();
    let (checked, bytes, failures) = check_batch(&input, 1).unwrap();
    assert_eq!((checked, bytes), expected);
    assert!(failures.is_empty());
}

#[test]
fn bytes_written_through_a_still_live_shared_mapping_are_reread() {
    use std::os::fd::AsRawFd as _;
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    let file = root.join("body");
    fs::write(&file, b"original bytes\n").unwrap();
    let input = batch(&root, vec![item(&root, "body", "100644", false)]);
    let handle = OpenOptions::new()
        .read(true)
        .write(true)
        .open(&file)
        .unwrap();
    // SAFETY: map the exact live file length; release the same mapping below.
    let mapping = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            15,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED,
            handle.as_raw_fd(),
            0,
        )
    };
    assert_ne!(mapping, libc::MAP_FAILED);
    assert!(check_batch(&input, 1).unwrap().2.is_empty());
    // SAFETY: the first byte lies in the live writable mapping.
    unsafe {
        mapping.cast::<u8>().write(b'E');
    }
    assert!(!check_batch(&input, 1).unwrap().2.is_empty());
    // SAFETY: unmap the same original region after its observed read.
    assert_eq!(unsafe { libc::munmap(mapping, 15) }, 0);
}

#[test]
fn in_root_parent_alias_is_preserved_but_an_escaping_parent_refuses() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    fs::create_dir(root.join("real")).unwrap();
    fs::write(root.join("real/body"), b"same bytes\n").unwrap();
    symlink("real", root.join("alias")).unwrap();
    let input = batch(&root, vec![item(&root, "alias/body", "100644", false)]);
    let (checked, bytes, failures) = check_batch(&input, 1).unwrap();
    assert_eq!((checked, bytes), (1, 11));
    assert!(failures.is_empty());
    let outside = tempfile::tempdir().unwrap();
    fs::write(outside.path().join("body"), b"same bytes\n").unwrap();
    fs::remove_file(root.join("alias")).unwrap();
    symlink(outside.path(), root.join("alias")).unwrap();
    assert_eq!(
        check_batch(&input, 1).unwrap().2[0].failure.kind,
        "parent-escape"
    );
}

#[test]
fn changed_mode_type_link_and_deleted_inputs_refuse_in_original_order() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    fs::write(root.join("first"), b"first\n").unwrap();
    fs::write(root.join("second"), b"second\n").unwrap();
    symlink("first", root.join("link")).unwrap();
    let input = batch(
        &root,
        vec![
            item(&root, "first", "100644", false),
            item(&root, "second", "100644", false),
            item(&root, "link", "120000", false),
        ],
    );
    fs::set_permissions(root.join("second"), fs::Permissions::from_mode(0o755)).unwrap();
    assert_eq!(check_batch(&input, 3).unwrap().2[0].index, 1);
    fs::set_permissions(root.join("second"), fs::Permissions::from_mode(0o644)).unwrap();
    fs::remove_file(root.join("link")).unwrap();
    symlink("second", root.join("link")).unwrap();
    assert_eq!(check_batch(&input, 2).unwrap().2[0].index, 2);
    fs::remove_file(root.join("first")).unwrap();
    symlink("second", root.join("first")).unwrap();
    assert_eq!(check_batch(&input, 2).unwrap().2[0].index, 0);
    fs::remove_file(root.join("first")).unwrap();
    assert_eq!(check_batch(&input, 2).unwrap().2[0].index, 0);
}

#[test]
fn malformed_population_paths_and_unknown_fields_never_become_comparisons() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    fs::write(root.join("body"), b"bytes\n").unwrap();
    let expected = item(&root, "body", "100644", false);
    let good = serde_json::json!({"schema":SCHEMA,"nonce":"ab".repeat(32),"repo":"Lw==",
        "items":[{"path":expected.path,"mode":expected.mode,"oid":expected.oid}]});
    assert!(parse_batch(&serde_json::to_vec(&good).unwrap()).is_ok());
    for path in ["../body", "/body", ""] {
        let mut bad = good.clone();
        bad["items"][0]["path"] = base64::engine::general_purpose::STANDARD
            .encode(path.as_bytes())
            .into();
        assert!(parse_batch(&serde_json::to_vec(&bad).unwrap()).is_err());
    }
    let mut bad = good.clone();
    bad["extra"] = true.into();
    assert!(parse_batch(&serde_json::to_vec(&bad).unwrap()).is_err());
    bad = good.clone();
    bad["items"] = serde_json::json!([]);
    assert!(parse_batch(&serde_json::to_vec(&bad).unwrap()).is_err());
    bad = good.clone();
    bad["items"][0]["oid"] = "00".into();
    assert!(parse_batch(&serde_json::to_vec(&bad).unwrap()).is_err());
    assert!(frame(&mut std::io::Cursor::new(b"{}".as_slice())).is_err());
}
