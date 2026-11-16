use std::io::Cursor;
use std::sync::OnceLock;

use ar_archive_writer::{
    ArchiveKind, DEFAULT_OBJECT_READER, NewArchiveMember, write_archive_to_stream,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{Linkage, Ty};

use super::*;

#[path = "../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::{DARWIN, Fixture, ModBuilder};

fn actual_unaligned_object() -> &'static [u8] {
    static OBJECT: OnceLock<Vec<u8>> = OnceLock::new();
    OBJECT.get_or_init(|| {
        // Real Compiler output, before packaging. Symbol-name lengths make
        // the Mach-O string table vary; choose a genuinely padded writer case.
        for width in 1..=8 {
            let mut b = ModBuilder::new("archive_object");
            let sig = b.sig(&[Ty::U64], Some(Ty::U64));
            b.define(
                &format!("archive_identity_{}", "x".repeat(width)),
                sig,
                Linkage::External,
                |f| f.ret(f.p(0)),
            );
            let f = Fixture::new(b.finish(), DARWIN, OptLevel::O0);
            if f.object.len() % 8 != 0 {
                return f.object;
            }
        }
        panic!("require a real non-eight-aligned Compiler object");
    })
}

fn archive(objects: &[(&str, &[u8])], kind: ArchiveKind, thin: bool) -> Vec<u8> {
    let members: Vec<_> = objects
        .iter()
        .map(|(name, bytes)| NewArchiveMember::new(*bytes, &DEFAULT_OBJECT_READER, (*name).into()))
        .collect();
    let mut bytes = Cursor::new(Vec::new());
    write_archive_to_stream(&mut bytes, &members, kind, thin, None).unwrap();
    bytes.into_inner()
}

#[test]
fn actual_pinned_writer_darwin_padding_and_gnu_exact_bytes_bind_independently() {
    let object = actual_unaligned_object();
    let darwin = archive(&[("unit.o", object)], ArchiveKind::Darwin, false);
    let bound =
        bind_archive_object(&darwin, "unit.o", object, ArchiveObjectPadding::DarwinEightByte)
            .unwrap();
    assert_eq!(bound.object(), object);
    assert_eq!(
        bound.object().as_ptr(),
        darwin[bound.binding().member_data_offset as usize..].as_ptr()
    );
    assert_eq!(bound.binding().padding_bytes, 8 - object.len() % 8);
    assert_ne!(bound.binding().member_sha256, bound.binding().object_sha256);
    assert!(bind_archive_object(&darwin, "unit.o", object, ArchiveObjectPadding::Exact).is_err());

    let gnu = archive(&[("unit.o", object)], ArchiveKind::Gnu, false);
    let exact = bind_archive_object(&gnu, "unit.o", object, ArchiveObjectPadding::Exact).unwrap();
    assert_eq!(exact.binding().padding_bytes, 0);
    assert_eq!(exact.binding().member_sha256, exact.binding().object_sha256);
    assert!(
        bind_archive_object(&gnu, "unit.o", object, ArchiveObjectPadding::DarwinEightByte).is_err()
    );
    let bsd = archive(&[("unit.o", object)], ArchiveKind::Bsd, false);
    assert!(
        bind_archive_object(&bsd, "unit.o", object, ArchiveObjectPadding::DarwinEightByte).is_err()
    );
}

#[test]
fn changed_whole_object_padding_duplicates_thin_and_later_malformed_members_refuse() {
    let object = actual_unaligned_object();
    let original = archive(&[("unit.o", object)], ArchiveKind::Darwin, false);
    let bound =
        bind_archive_object(&original, "unit.o", object, ArchiveObjectPadding::DarwinEightByte)
            .unwrap();
    let offset = bound.binding().member_data_offset as usize;
    for change in [0, object.len() - 1, object.len()] {
        let mut bytes = original.clone();
        bytes[offset + change] ^= 1;
        assert!(
            bind_archive_object(&bytes, "unit.o", object, ArchiveObjectPadding::DarwinEightByte)
                .is_err(),
            "change{change}"
        );
    }
    let duplicate = archive(&[("unit.o", object), ("unit.o", object)], ArchiveKind::Darwin, false);
    assert!(
        bind_archive_object(&duplicate, "unit.o", object, ArchiveObjectPadding::DarwinEightByte)
            .is_err()
    );
    let mut odd_tail = archive(&[("unit.o", object), ("last", b"x")], ArchiveKind::Gnu, false);
    assert_eq!(odd_tail.last(), Some(&b'\n'));
    odd_tail.pop();
    assert!(bind_archive_object(&odd_tail, "unit.o", object, ArchiveObjectPadding::Exact).is_err());
    odd_tail.push(0);
    assert!(bind_archive_object(&odd_tail, "unit.o", object, ArchiveObjectPadding::Exact).is_err());
    let thin = archive(&[("unit.o", object)], ArchiveKind::Gnu, true);
    assert!(bind_archive_object(&thin, "unit.o", object, ArchiveObjectPadding::Exact).is_err());
    let mut trailing = original.clone();
    trailing.push(b'x');
    assert!(
        bind_archive_object(&trailing, "unit.o", object, ArchiveObjectPadding::DarwinEightByte)
            .is_err()
    );
    assert!(
        bind_archive_object(
            &original[..original.len() - 1],
            "unit.o",
            object,
            ArchiveObjectPadding::DarwinEightByte
        )
        .is_err()
    );
    assert!(
        bind_archive_object(&original, "absent.o", object, ArchiveObjectPadding::DarwinEightByte)
            .is_err()
    );
}

#[test]
fn membership_reports_other_members_without_granting_whole_archive_authority() {
    let object = actual_unaligned_object();
    let other = actual_unaligned_object().to_vec();
    let bytes = archive(&[("unit.o", object), ("other.o", &other)], ArchiveKind::Darwin, false);
    let bound =
        bind_archive_object(&bytes, "unit.o", object, ArchiveObjectPadding::DarwinEightByte)
            .unwrap();
    assert_eq!(bound.binding().ordinary_members, 2);
    assert_eq!(bound.binding().member_name, "unit.o");
    assert_eq!(bound.object(), object);
}
