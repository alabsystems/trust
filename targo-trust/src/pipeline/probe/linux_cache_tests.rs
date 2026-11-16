use super::*;

fn put(bytes: &mut [u8], at: usize, value: u32) {
    bytes[at..at + 4].copy_from_slice(&value.to_le_bytes());
}

fn fixture(rows: &[(&str, &str)]) -> Vec<u8> {
    let first = HEADER + rows.len() * ENTRY;
    let mut bytes = vec![0; first];
    bytes[..20].copy_from_slice(b"glibc-ld.so.cache1.1");
    put(&mut bytes, 20, rows.len() as u32);
    bytes[28] = 2;
    for (index, (name, path)) in rows.iter().enumerate() {
        let at = HEADER + index * ENTRY;
        put(&mut bytes, at, 0xa03);
        let key = bytes.len() as u32;
        bytes.extend_from_slice(name.as_bytes());
        bytes.push(0);
        let value = bytes.len() as u32;
        bytes.extend_from_slice(path.as_bytes());
        bytes.push(0);
        put(&mut bytes, at + 4, key);
        put(&mut bytes, at + 8, value);
    }
    let size = bytes.len() - first;
    put(&mut bytes, 24, size as u32);
    bytes
}

#[test]
fn keeps_all_cache_candidates_without_architecture_or_hwcaps_filtering() {
    let mut bytes =
        fixture(&[("libx.so", "/lib/libx.so"), ("libx.so", "/usr/local/private/libx.so")]);
    put(&mut bytes, HEADER + ENTRY, 0xffff);
    bytes[HEADER + ENTRY + 16..HEADER + ENTRY + 24].copy_from_slice(&17u64.to_le_bytes());
    let rows = entries(&bytes).expect("all possible sources, not just host preferred match");
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[1].path, "/usr/local/private/libx.so");
    assert_eq!(rows[1].flags, 0xffff);
    assert_eq!(rows[1].hwcap, 17);
}

#[test]
fn cache_rejects_old_combined_wrong_endian_or_future_formats() {
    for (at, value) in [(0, b'L'), (19, b'2'), (28, 0), (28, 3), (29, 1), (36, 1)] {
        let mut bytes = fixture(&[("libx.so", "/lib/libx.so")]);
        bytes[at] = value;
        assert!(entries(&bytes).is_err(), "accepted unsupported header at {at}");
    }
    assert!(entries(b"ld.so-1.7.0").is_err());
}

#[test]
fn cache_rejects_out_of_extent_and_unterminated_strings() {
    for (at, value) in [(20, u32::MAX), (24, u32::MAX), (HEADER + 4, 0), (HEADER + 8, u32::MAX)] {
        let mut bytes = fixture(&[("libx.so", "/lib/libx.so")]);
        put(&mut bytes, at, value);
        assert!(entries(&bytes).is_err());
    }
    let mut bytes = fixture(&[("libx.so", "/lib/libx.so")]);
    *bytes.last_mut().expect("terminator") = b'x';
    assert!(entries(&bytes).is_err());
}

#[test]
fn cache_rejects_relative_control_and_non_soname_records() {
    for (name, path) in [
        ("../x", "/lib/x"),
        ("libx.so", "relative/x"),
        ("libx.so", "/lib/../tmp/x"),
        ("libx.so", "/lib/x\n.so"),
        ("", "/lib/x"),
    ] {
        assert!(entries(&fixture(&[(name, path)])).is_err());
    }
}

#[test]
fn cache_validates_extensions_instead_of_hiding_targets_behind_them() {
    let mut bytes = fixture(&[("libx.so", "/lib/libx.so")]);
    while bytes.len() % 4 != 0 {
        bytes.push(0);
    }
    let at = bytes.len();
    bytes.resize(at + 24 + 4, 0);
    put(&mut bytes, 32, at as u32);
    put(&mut bytes, at, EXTENSION_MAGIC);
    put(&mut bytes, at + 4, 1);
    put(&mut bytes, at + 8, 0);
    put(&mut bytes, at + 16, (at + 24) as u32);
    put(&mut bytes, at + 20, 4);
    bytes[at + 24..].copy_from_slice(b"test");
    assert_eq!(entries(&bytes).expect("bounded known generator extension").len(), 1);
    for (field, value) in
        [(at, 0), (at + 4, 3), (at + 8, 2), (at + 12, 1), (at + 16, 0), (at + 20, u32::MAX)]
    {
        let mut changed = bytes.clone();
        put(&mut changed, field, value);
        assert!(entries(&changed).is_err());
    }
}

#[test]
fn cache_rejects_a_named_hwcap_without_its_indexed_extension() {
    let mut bytes = fixture(&[("libx.so", "/lib/libx.so")]);
    bytes[HEADER + 16..HEADER + 24].copy_from_slice(&(1u64 << 62).to_le_bytes());
    assert!(entries(&bytes).is_err());
}

#[test]
fn cache_count_and_byte_bounds_are_checked_before_expansion() {
    let mut bytes = fixture(&[]);
    put(&mut bytes, 20, (MAX_ENTRIES + 1) as u32);
    assert!(entries(&bytes).is_err());
    assert!(entries(&vec![0; MAX_BYTES + 1]).is_err());
    let bytes = fixture(&[("libx.so", &format!("/lib/{}", "x".repeat(4097)))]);
    assert!(entries(&bytes).is_err());
}
