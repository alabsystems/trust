use std::io::Cursor;

use ar_archive_writer::{
    ArchiveKind, DEFAULT_OBJECT_READER, NewArchiveMember, write_archive_to_stream,
};

use super::*;

fn writer_payload(object: &[u8]) -> Vec<u8> {
    let members = [NewArchiveMember::new(object, &DEFAULT_OBJECT_READER, "unit.o".into())];
    let mut bytes = Cursor::new(Vec::new());
    write_archive_to_stream(&mut bytes, &members, ArchiveKind::Gnu, false, None).unwrap();
    bytes.into_inner()
}

#[test]
fn archive_transaction_preserves_old_output_on_mismatch_then_publishes_checked_bytes() {
    let scratch = TempDirBuilder::new()
        .prefix("trust-archive-publication-test-")
        .tempdir_in(std::env::temp_dir())
        .unwrap();
    let source = scratch.path().join("unit.o");
    let output = scratch.path().join("final.rlib");
    // Filesystem transport test, not proof/codegen evidence. CgBridge's
    // separate test replays a real Compiler object's original CIC in a child.
    let expected =
        CompilerArchiveObject::new("unit".into(), source.clone(), b"current live object".to_vec())
            .unwrap();
    fs::write(&source, &expected.bytes).unwrap();
    fs::write(&output, b"previous valid output").unwrap();
    let bad = writer_payload(b"different object");
    let result = publish_bound_archive(&output, &expected, ArchiveObjectPadding::Exact, |stage| {
        assert_ne!(stage, output);
        assert_ne!(stage.parent(), output.parent());
        assert_eq!(fs::read(&output).unwrap(), b"previous valid output");
        fs::write(stage, &bad).unwrap();
        true
    });
    assert!(result.is_err());
    assert_eq!(fs::read(&output).unwrap(), b"previous valid output");
    assert_eq!(fs::read_dir(scratch.path()).unwrap().count(), 2);
    let good = writer_payload(&expected.bytes);
    let (built, binding) =
        publish_bound_archive(&output, &expected, ArchiveObjectPadding::Exact, |stage| {
            assert_eq!(fs::read(&output).unwrap(), b"previous valid output");
            fs::write(stage, &good).unwrap();
            true
        })
        .unwrap();
    assert!(built);
    assert_eq!(fs::read(&output).unwrap(), good);
    assert_eq!(binding.archive_sha256, trust_cg_bridge::object_replay::artifact_digest(&good));
    assert_eq!(fs::read(&source).unwrap(), expected.bytes);
    assert_eq!(fs::read_dir(scratch.path()).unwrap().count(), 2);
}

#[test]
fn archive_destination_alias_refuses_before_builder_or_cleanup_can_destroy_input() {
    let scratch = TempDirBuilder::new()
        .prefix("trust-archive-alias-test-")
        .tempdir_in(std::env::temp_dir())
        .unwrap();
    let source = scratch.path().join("unit.o");
    let expected =
        CompilerArchiveObject::new("unit".into(), source.clone(), b"current live object".to_vec())
            .unwrap();
    fs::write(&source, &expected.bytes).unwrap();
    let failure = publish_bound_archive(&source, &expected, ArchiveObjectPadding::Exact, |_| {
        panic!("must refuse alias before invoking archive writer")
    });
    assert!(failure.unwrap_err().contains("aliases"));
    assert_eq!(fs::read(&source).unwrap(), expected.bytes);
    let alias = scratch.path().join("hardlink.rlib");
    fs::hard_link(&source, &alias).unwrap();
    let failure = publish_bound_archive(&alias, &expected, ArchiveObjectPadding::Exact, |_| {
        panic!("must refuse identity alias before invoking archive writer")
    });
    assert!(failure.unwrap_err().contains("aliases"));
    assert_eq!(fs::read(&source).unwrap(), expected.bytes);
}
