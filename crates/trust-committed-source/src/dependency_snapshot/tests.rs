//! Exercise the actual packet serializer's escaped-byte and allocation bounds.
//! No fixture constructs the original graph, a native closure or semantic owner.
use std::io::Write as _;

use super::*;

#[test]
fn existing_json_bytes_fit_at_the_exact_bound_and_refuse_one_byte_below() {
    for value in [
        Value::Null,
        json!({"escaped": "\\\n\0\"", "unicode": "λ", "items": [null, true, -1]}),
        Value::String("a".repeat(64 * 1024)),
    ] {
        let expected = serde_json::to_vec(&value).unwrap();
        assert_eq!(encode_dependency_packet(&value, expected.len()).unwrap(), expected);
        assert!(encode_dependency_packet(&value, expected.len() - 1).is_err());
    }
}

#[test]
fn rejected_chunk_preserves_bytes_and_growth_cannot_exceed_the_declared_bound() {
    let mut writer = PacketWriter { bytes: Vec::new(), limit: 4097 };
    for _ in 0..4 {
        writer.write_all(&[b'a'; 1023]).unwrap();
        assert!(writer.bytes.capacity() <= writer.limit);
    }
    let before = writer.bytes.clone();
    let capacity = writer.bytes.capacity();
    assert!(writer.write_all(b"123456").is_err());
    assert_eq!(writer.bytes, before);
    assert_eq!(writer.bytes.capacity(), capacity);
    writer.write_all(b"12345").unwrap();
    assert_eq!(writer.bytes.len(), writer.limit);
    assert!(writer.bytes.capacity() <= writer.limit);
    assert!(writer.write_all(b"x").is_err());
    writer.write_all(b"").unwrap();
    assert_eq!(writer.bytes.len(), writer.limit);
    assert!(encode_dependency_packet(&Value::Null, 0).is_err());
}

// Actual local Git/file fixtures only. No semantic source, live Graph,
// native closure, manager, Seed or SDK is constructed here.
fn original() -> (tempfile::TempDir, File, PathBuf, Instant) {
    use std::os::unix::fs::PermissionsExt as _;
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path().canonicalize().unwrap();
    let repo = gix::init(&root).unwrap();
    std::fs::create_dir(root.join("nested")).unwrap();
    std::fs::set_permissions(root.join("nested"), std::fs::Permissions::from_mode(0o755)).unwrap();
    let bytes = b"[package]\nname='passive-source'\n";
    for path in ["Cargo.toml", "nested/Cargo.toml"] {
        std::fs::write(root.join(path), bytes).unwrap();
        std::fs::set_permissions(root.join(path), std::fs::Permissions::from_mode(0o644)).unwrap();
    }
    let blob = repo.write_blob(bytes).unwrap().detach();
    let entry = |name: &str, mode: gix::objs::tree::EntryKind, object| gix::objs::tree::Entry {
        mode: mode.into(),
        filename: name.into(),
        oid: object,
    };
    let nested = repo
        .write_object(&gix::objs::Tree {
            entries: vec![entry("Cargo.toml", gix::objs::tree::EntryKind::Blob, blob)],
        })
        .unwrap()
        .detach();
    let tree = repo
        .write_object(&gix::objs::Tree {
            entries: vec![
                entry("Cargo.toml", gix::objs::tree::EntryKind::Blob, blob),
                entry("nested", gix::objs::tree::EntryKind::Tree, nested),
            ],
        })
        .unwrap()
        .detach();
    let signature = gix::actor::Signature {
        name: "passive source fixture".into(),
        email: "source@example.invalid".into(),
        time: gix::date::Time { seconds: 1_600_000_000, offset: 0 },
    };
    let mut time = gix::date::parse::TimeBuf::default();
    let signature = signature.to_ref(&mut time);
    repo.commit_as(
        signature,
        signature,
        "HEAD",
        "actual source fixture",
        tree,
        std::iter::empty::<gix::ObjectId>(),
    )
    .unwrap();
    let directory = source_dir(&root).unwrap();
    (scratch, directory, root, Instant::now() + std::time::Duration::from_secs(60))
}
fn capture(directory: &File, root: &Path, end: Instant) -> CommittedDependencySnapshot {
    match CommittedDependencySnapshot::capture(directory.as_fd(), root, end) {
        Ok(snapshot) => snapshot,
        Err(refusal) => panic!("actual passive source capture refused: {}", refusal.into_parts().0),
    }
}

#[test]
fn captured_packet_and_glob_reads_come_from_actual_git_and_remain_revoked_after_restoration() {
    let (_scratch, directory, root, end) = original();
    let mut snapshot = capture(&directory, &root, end);
    snapshot.capture_glob_directories(directory.as_fd(), &[PathBuf::from("nested")], end).unwrap();
    let packet = snapshot.packet(directory.as_fd(), end).unwrap();
    let packet: Value = serde_json::from_slice(&packet).unwrap();
    assert_eq!(packet["schema"], "trust-native-dependency-source-v1");
    assert_eq!(packet["root"], root.to_str().unwrap());
    assert_eq!(packet["repositories"]["."].as_array().unwrap().len(), 3);
    assert_eq!(packet["reads"]["Cargo.toml"]["hex"], hex(b"[package]\nname='passive-source'\n"));
    assert_eq!(packet["reads"][CODE[0]]["kind"], "absent");
    assert_eq!(packet["listings"]["nested"][0]["name"], "Cargo.toml");
    std::fs::write(root.join("Cargo.toml"), b"observed source drift").unwrap();
    assert!(snapshot.check_current(directory.as_fd(), end).is_err());
    std::fs::write(root.join("Cargo.toml"), b"[package]\nname='passive-source'\n").unwrap();
    assert!(snapshot.packet(directory.as_fd(), end).is_err());
}

#[test]
fn passive_snapshot_rejects_foreign_directory_and_renewed_endpoint_without_recovery() {
    let (_scratch, directory, root, end) = original();
    let other = tempfile::tempdir().unwrap();
    let foreign = source_dir(other.path()).unwrap();
    let snapshot = capture(&directory, &root, end);
    assert!(snapshot.check_current(foreign.as_fd(), end).is_err());
    assert!(snapshot.check_current(directory.as_fd(), end).is_err());
    let snapshot = capture(&directory, &root, end);
    assert!(
        snapshot
            .check_current(directory.as_fd(), end + std::time::Duration::from_millis(1))
            .is_err()
    );
    assert!(snapshot.packet(directory.as_fd(), end).is_err());
}
