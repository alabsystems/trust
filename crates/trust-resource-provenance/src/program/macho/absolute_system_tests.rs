use super::*;

fn command(kind: u32, text: &str, fixed: usize) -> Vec<u8> {
    let length = (fixed + text.len() + 1).next_multiple_of(8);
    let mut bytes = vec![0u8; length];
    bytes[..4].copy_from_slice(&kind.to_le_bytes());
    bytes[4..8].copy_from_slice(&(length as u32).to_le_bytes());
    bytes[8..12].copy_from_slice(&(fixed as u32).to_le_bytes());
    bytes[fixed..fixed + text.len()].copy_from_slice(text.as_bytes());
    bytes
}

fn image(commands: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = vec![0; 32];
    for (offset, value) in [
        (0, 0xfeed_facfu32),
        (4, 0x0100_000c),
        (12, 2),
        (16, commands.len() as u32),
        (20, commands.iter().map(Vec::len).sum::<usize>() as u32),
    ] {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes.extend(commands.iter().flatten());
    bytes
}

fn loader() -> Vec<u8> {
    command(0xe, "/usr/lib/dyld", 12)
}

#[test]
fn absolute_system_imports_ignore_unused_rpaths_without_widening_metadata() {
    for path in ["@loader_path/../lib/atpkg-vendored", "/original/provider/lib", "@rpath/unused"] {
        let bytes = image(&[
            loader(),
            command(0xc, "/usr/lib/libSystem.B.dylib", 24),
            command(0x8000_001c, path, 12),
        ]);
        assert!(commands(&bytes, true).is_err());
        let observed = absolute_system_commands(&bytes).unwrap();
        assert_eq!(observed.loads, ["/usr/lib/libSystem.B.dylib"]);
        assert_eq!(observed.rpaths, [path]);
    }
}

#[test]
fn every_static_load_form_must_be_a_canonical_absolute_system_import() {
    for kind in [0xc, 0x8000_0018, 0x8000_001f, 0x20, 0x8000_0023] {
        for path in [
            "/usr/lib/libSystem.B.dylib",
            "/System/Library/Frameworks/CoreFoundation.framework/CoreFoundation",
        ] {
            assert!(absolute_system_commands(&image(&[loader(), command(kind, path, 24)])).is_ok());
        }
        for path in [
            "@rpath/foreign.dylib",
            "@loader_path/foreign.dylib",
            "/opt/foreign.dylib",
            "/usr/library/foreign",
            "/usr/lib/../foreign",
            "/usr/lib//foreign",
            "/System/Other/foreign",
            "/System/Library/./foreign",
            "relative.dylib",
        ] {
            let bytes =
                image(&[loader(), command(kind, path, 24), command(0x8000_001c, "/unused", 12)]);
            assert!(absolute_system_commands(&bytes).is_err(), "accepted {kind:x} {path}");
        }
    }
}

#[test]
fn absolute_system_imports_keep_loader_command_census_and_bounded_strings_closed() {
    let import = command(0xc, "/usr/lib/libSystem.B.dylib", 24);
    for extra in [
        command(0x27, "DYLD_INSERT_LIBRARIES=/foreign", 12),
        command(0xe, "/other/dyld", 12),
        command(0x21, "encrypted", 12),
        command(0x35, "unknown", 12),
        loader(),
        command(0x8000_001c, "/unused\nsearch", 12),
        command(0x8000_001c, &"a".repeat(MAX_PATH + 1), 12),
    ] {
        assert!(absolute_system_commands(&image(&[loader(), import.clone(), extra])).is_err());
    }
    assert!(absolute_system_commands(&image(&[import])).is_err());
    let original = image(&[loader(), command(0x8000_001c, "/unused", 12)]);
    for end in 0..original.len() {
        assert!(absolute_system_commands(&original[..end]).is_err());
    }
    for (offset, value) in
        [(0, 0xcafe_babeu32), (4, 0x0100_0007), (12, 6), (16, u32::MAX), (20, u32::MAX)]
    {
        let mut altered = original.clone();
        altered[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        assert!(absolute_system_commands(&altered).is_err());
    }
}
