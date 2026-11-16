use std::io::Cursor;

use super::*;

const BASE: u64 = 0x40_0000;
const DYNAMIC: usize = 0x200;
const STRINGS: usize = 0x300;

fn put16(bytes: &mut [u8], offset: usize, value: u16) {
    bytes[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
}
fn put32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}
fn put64(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}
fn segment(bytes: &mut [u8], index: usize, kind: u32, offset: u64, count: u64) {
    let start = 64 + index * 56;
    put32(bytes, start, kind);
    put64(bytes, start + 8, offset);
    put64(bytes, start + 16, BASE + offset);
    put64(bytes, start + 32, count);
    put64(bytes, start + 40, count);
    put64(bytes, start + 48, 1);
}
fn dynamic(bytes: &mut [u8], index: usize, tag: u64, value: u64) {
    put64(bytes, DYNAMIC + 16 * index, tag);
    put64(bytes, DYNAMIC + 16 * index + 8, value);
}
fn fixture() -> Vec<u8> {
    let mut bytes = vec![0; 0x500];
    bytes[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    // A fixed-address executable needs no PHDR-derived relocation bias.
    put16(&mut bytes, 16, 2);
    put16(&mut bytes, 18, 183);
    put32(&mut bytes, 20, 1);
    put64(&mut bytes, 32, 64);
    put16(&mut bytes, 52, 64);
    put16(&mut bytes, 54, 56);
    put16(&mut bytes, 56, 3);
    segment(&mut bytes, 0, PT_LOAD, 0, 0x500);
    let interpreter = b"/lib/ld-linux-aarch64.so.1\0";
    segment(&mut bytes, 1, PT_INTERP, 0x180, interpreter.len() as u64);
    bytes[0x180..0x180 + interpreter.len()].copy_from_slice(interpreter);
    segment(&mut bytes, 2, PT_DYNAMIC, DYNAMIC as u64, 80);
    bytes[STRINGS..STRINGS + 11].copy_from_slice(b"\0libc.so.6\0");
    dynamic(&mut bytes, 0, 1, 1);
    dynamic(&mut bytes, 1, 5, BASE + STRINGS as u64);
    dynamic(&mut bytes, 2, 10, 11);
    bytes
}
fn parse(bytes: &[u8]) -> Result<ElfMetadata, String> {
    inspect(&mut Cursor::new(bytes), bytes.len() as u64, 183, 4096)
}

fn pie_with_phdr() -> Vec<u8> {
    let mut bytes = fixture();
    bytes.copy_within(64..64 + 3 * 56, 64 + 56);
    put16(&mut bytes, 16, 3);
    put16(&mut bytes, 56, 4);
    segment(&mut bytes, 0, PT_PHDR, 64, 4 * 56);
    bytes
}

#[test]
fn reads_ordered_native_dependencies_from_program_headers() {
    let result = parse(&fixture()).expect("valid program-header-backed dynamic table");
    assert_eq!(result.machine, 183);
    assert_eq!(result.interpreter.as_deref(), Some("/lib/ld-linux-aarch64.so.1"));
    assert_eq!(result.needed, ["libc.so.6"]);
    assert!(result.dynamic);
}

#[test]
fn accepts_empty_needed_only_after_real_table_validation() {
    let mut bytes = fixture();
    dynamic(&mut bytes, 0, 14, 1);
    let result = parse(&bytes).expect("no DT_NEEDED in real terminated table");
    assert!(result.dynamic && result.needed.is_empty());
    dynamic(&mut bytes, 4, 29, 0);
    assert!(parse(&bytes).is_err(), "empty needed must not hide malformed tail");
}

#[test]
fn distinguishes_static_metadata_without_minting_a_runtime_closure() {
    let mut bytes = fixture();
    put16(&mut bytes, 56, 1);
    let result = parse(&bytes).expect("static ELF metadata");
    assert!(!result.dynamic);
    assert!(result.interpreter.is_none() && result.needed.is_empty());
}

#[test]
fn sections_do_not_replace_the_loader_program_header_source() {
    let mut bytes = fixture();
    put64(&mut bytes, 40, u64::MAX);
    put16(&mut bytes, 60, u16::MAX);
    assert_eq!(parse(&bytes).expect("irrelevant section directory").needed, ["libc.so.6"]);
    put32(&mut bytes, 64 + 2 * 56, 0);
    assert!(parse(&bytes).is_err(), "a plausible section table cannot supply PT_DYNAMIC");
}

#[test]
fn rejects_duplicate_dynamic_and_interpreter_segments() {
    for copied in [1, 2] {
        let mut bytes = fixture();
        let copy = bytes[64 + copied * 56..64 + (copied + 1) * 56].to_vec();
        bytes[64 + 3 * 56..64 + 4 * 56].copy_from_slice(&copy);
        put16(&mut bytes, 56, 4);
        assert!(parse(&bytes).is_err());
    }
}

#[test]
fn rejects_architecture_bitness_endianness_and_non_executables() {
    for (offset, value) in
        [(4, 1), (5, 2), (7, 9), (8, 1), (16, 1), (18, 62), (20, 2), (48, 1), (52, 63)]
    {
        let mut bytes = fixture();
        bytes[offset] = value;
        assert!(parse(&bytes).is_err(), "accepted changed header offset {offset}");
    }
}

#[test]
fn rejects_out_of_file_and_unbounded_program_tables_before_allocation() {
    for (offset, value) in [(32, u64::MAX), (32, 1), (64 + 8, u64::MAX), (64 + 32, u64::MAX)] {
        let mut bytes = fixture();
        put64(&mut bytes, offset, value);
        assert!(parse(&bytes).is_err());
    }
    let mut bytes = fixture();
    put16(&mut bytes, 56, (PROGRAM_HEADER_LIMIT + 1) as u16);
    assert!(parse(&bytes).is_err());
}

#[test]
fn requires_one_file_backed_dynamic_virtual_mapping() {
    let mut bytes = fixture();
    put64(&mut bytes, 64 + 2 * 56 + 16, BASE + 0x210);
    assert!(parse(&bytes).is_err(), "dynamic virtual/file addresses disagree");
    let mut bytes = fixture();
    segment(&mut bytes, 0, PT_LOAD, 0, 0x210);
    put64(&mut bytes, 64 + 40, 0x500);
    assert!(parse(&bytes).is_err(), "BSS cannot back dynamic bytes");
    let mut bytes = fixture();
    segment(&mut bytes, 3, PT_LOAD, 0, 0x500);
    put16(&mut bytes, 56, 4);
    assert!(parse(&bytes).is_err(), "overlapping LOAD mappings are ambiguous");
}

#[test]
fn rejects_dynamic_search_audit_and_filter_authority() {
    for tag in [15, 29, 0x6fff_fefa, 0x6fff_fefb, 0x6fff_fefc, 0x7fff_fffd, 0x7fff_ffff] {
        let mut bytes = fixture();
        dynamic(&mut bytes, 0, tag, 1);
        assert!(parse(&bytes).is_err(), "accepted dynamic authority tag {tag:x}");
    }
}

#[test]
fn rejects_duplicate_or_unterminated_dynamic_bindings() {
    for (tag, value) in [(5, BASE + STRINGS as u64), (10, 11)] {
        let mut bytes = fixture();
        dynamic(&mut bytes, 3, tag, value);
        assert!(parse(&bytes).is_err());
    }
    let mut bytes = fixture();
    dynamic(&mut bytes, 3, 14, 1);
    dynamic(&mut bytes, 4, 14, 1);
    assert!(parse(&bytes).is_err(), "missing dynamic terminator");
}

#[test]
fn rejects_missing_unmapped_or_oversized_string_tables() {
    for (index, tag, value) in [(1, 14, 1), (2, 14, 1), (1, 5, BASE + 0x4ff), (2, 10, u64::MAX)] {
        let mut bytes = fixture();
        dynamic(&mut bytes, index, tag, value);
        assert!(parse(&bytes).is_err());
    }
}

#[test]
fn rejects_duplicate_empty_relative_or_unterminated_sonames() {
    let mut bytes = fixture();
    dynamic(&mut bytes, 3, 1, 1);
    assert!(parse(&bytes).is_err(), "duplicate DT_NEEDED");
    for name in [b"\0\0".as_slice(), b"\0../lib.so\0", b"\0/abs/lib\0", b"\0lib\nso.6\0"] {
        let mut bytes = fixture();
        bytes[STRINGS..STRINGS + name.len()].copy_from_slice(name);
        dynamic(&mut bytes, 2, 10, name.len() as u64);
        assert!(parse(&bytes).is_err());
    }
    let mut bytes = fixture();
    bytes[STRINGS + 10] = b'x';
    assert!(parse(&bytes).is_err(), "unterminated name");
    dynamic(&mut bytes, 0, 1, 11);
    assert!(parse(&bytes).is_err(), "offset exactly beyond the table");
}

#[test]
fn rejects_ambiguous_or_non_normalized_interpreter_paths() {
    for name in [b"/lib/../bad\0".as_slice(), b"relative.so\0", b"/lib//bad\0\0", b"/lib/\nbad\0\0"]
    {
        let mut bytes = fixture();
        bytes[0x180..0x180 + name.len()].copy_from_slice(name);
        put64(&mut bytes, 64 + 56 + 32, name.len() as u64);
        assert!(parse(&bytes).is_err());
    }
}

#[test]
fn rejects_partial_and_misaligned_load_metadata() {
    let mut bytes = fixture();
    put64(&mut bytes, 64 + 2 * 56 + 32, 79);
    assert!(parse(&bytes).is_err());
    let mut bytes = fixture();
    put64(&mut bytes, 64 + 48, 3);
    assert!(parse(&bytes).is_err());
    assert!(parse(&fixture()[..63]).is_err());
}

#[test]
fn rejects_partial_load_alias_over_dynamic_or_strings() {
    for target in [DYNAMIC + 16, STRINGS + 4] {
        let mut bytes = fixture();
        segment(&mut bytes, 3, PT_LOAD, target as u64, 8);
        put16(&mut bytes, 56, 4);
        // The old parser ignored this segment: it did not cover the WHOLE
        // dynamic/string range. The GNU loader can remap its overlapping page.
        assert!(parse(&bytes).is_err(), "accepted partial metadata alias at {target:x}");
    }
}

#[test]
fn rejects_bss_shadowing_and_byte_disjoint_page_aliases() {
    let mut bytes = fixture();
    segment(&mut bytes, 3, PT_LOAD, DYNAMIC as u64, 0);
    put64(&mut bytes, 64 + 3 * 56 + 40, 32);
    put16(&mut bytes, 56, 4);
    assert!(parse(&bytes).is_err(), "BSS can overwrite the table without file bytes");
    for offset in [0x600u64, 0x1600] {
        let mut bytes = fixture();
        bytes.resize(0x2000, 0);
        segment(&mut bytes, 3, PT_LOAD, offset, 16);
        put64(&mut bytes, 64 + 3 * 56 + 16, BASE + 0x600);
        put16(&mut bytes, 56, 4);
        assert!(parse(&bytes).is_err(), "declared byte-disjoint maps still share a host page");
    }
}

#[test]
fn admits_ordered_page_disjoint_loads_with_partial_last_pages() {
    let mut bytes = fixture();
    bytes.resize(0x2200, 0);
    segment(&mut bytes, 3, PT_LOAD, 0x2000, 0x200);
    put16(&mut bytes, 56, 4);
    assert_eq!(parse(&bytes).expect("ordered page-disjoint mapping").needed, ["libc.so.6"]);
}

#[test]
fn distinguishes_actual_host_page_size_from_large_segment_alignment() {
    let mut bytes = fixture();
    bytes.resize(0x2200, 0);
    segment(&mut bytes, 3, PT_LOAD, 0x2000, 0x200);
    put16(&mut bytes, 56, 4);
    assert!(inspect(&mut Cursor::new(&bytes), bytes.len() as u64, 183, 4096).is_ok());
    assert!(
        inspect(&mut Cursor::new(&bytes), bytes.len() as u64, 183, 65536).is_err(),
        "4K-disjoint segments alias under a 64K host mapping"
    );
    assert!(inspect(&mut Cursor::new(&bytes), bytes.len() as u64, 183, 1).is_err());
}

#[test]
fn binds_the_complete_mapped_program_header_array_for_pie_and_fixed_executables() {
    assert_eq!(
        parse(&pie_with_phdr()).expect("matching PIE PHDR and kernel table").needed,
        ["libc.so.6"]
    );
    assert_eq!(
        parse(&fixture()).expect("unambiguous zero-bias ET_EXEC table").needed,
        ["libc.so.6"]
    );
    let mut dso = fixture();
    put16(&mut dso, 16, 3);
    put32(&mut dso, 64 + 56, 0);
    assert!(
        parse(&dso)
            .expect("GNU-mapped DSO does not need a main-executable PHDR")
            .interpreter
            .is_none()
    );
}

#[test]
fn rejects_pie_main_without_the_explicit_program_header_bias_binding() {
    let mut bytes = fixture();
    put16(&mut bytes, 16, 3);
    assert!(
        parse(&bytes).is_err(),
        "a directly mapped PIE is not evidence of the kernel main-map bias"
    );
}

#[test]
fn rejects_a_forged_program_header_runtime_address_or_file_extent() {
    for field in [8, 16, 32, 40] {
        let mut bytes = pie_with_phdr();
        let old = u64_at(&bytes, 64 + field).expect("PHDR field");
        put64(&mut bytes, 64 + field, old + 1);
        assert!(parse(&bytes).is_err(), "accepted changed PHDR field {field}");
    }
    let mut bytes = pie_with_phdr();
    bytes.resize(0x2200, 0);
    // A real alternate array in another disjoint LOAD must not become GNU's
    // l_phdr while normal Linux exec receives the original e_phoff table.
    let table = bytes[64..64 + 4 * 56].to_vec();
    bytes[0x2040..0x2040 + table.len()].copy_from_slice(&table);
    segment(&mut bytes, 4, PT_LOAD, 0x2000, 0x200);
    put16(&mut bytes, 56, 5);
    put64(&mut bytes, 64 + 16, BASE + 0x2040);
    put64(&mut bytes, 64 + 32, 5 * 56);
    put64(&mut bytes, 64 + 40, 5 * 56);
    assert!(
        parse(&bytes).is_err(),
        "an alternate mapped array is not the kernel program-header source"
    );
}

#[test]
fn rejects_duplicate_program_header_segments_with_otherwise_exact_extents() {
    let mut bytes = pie_with_phdr();
    put16(&mut bytes, 56, 5);
    put64(&mut bytes, 64 + 32, 5 * 56);
    put64(&mut bytes, 64 + 40, 5 * 56);
    bytes.copy_within(64..120, 64 + 4 * 56);
    assert!(parse(&bytes).is_err());
}

#[test]
fn rejects_program_headers_after_load_bias_consumers() {
    for index in [1, 2, 3] {
        let mut bytes = pie_with_phdr();
        let first = bytes[64..120].to_vec();
        bytes.copy_within(64 + index * 56..64 + (index + 1) * 56, 64);
        bytes[64 + index * 56..64 + (index + 1) * 56].copy_from_slice(&first);
        assert!(parse(&bytes).is_err(), "accepted PHDR after consumer {index}");
    }
}

#[test]
fn rejects_partial_bss_only_and_aliased_program_header_file_mappings() {
    for file_bytes in [0, 65, 64 + 3 * 56 - 1] {
        let mut bytes = fixture();
        put64(&mut bytes, 64 + 32, file_bytes);
        assert!(parse(&bytes).is_err(), "accepted incomplete PHDR backing {file_bytes}");
    }
    let mut bytes = fixture();
    bytes.resize(0x1000, 0);
    segment(&mut bytes, 3, PT_LOAD, 0, 0x500);
    put64(&mut bytes, 64 + 3 * 56 + 16, BASE + 0x2000);
    put16(&mut bytes, 56, 4);
    assert!(
        parse(&bytes).is_err(),
        "two page-disjoint LOADs still give Linux competing PHDR starts"
    );
}

#[test]
fn accepts_relocated_interpreter_strings_with_matching_file_and_runtime_bytes() {
    let name = b"/lib/ld-linux-aarch64.so.1\0";
    for (mut bytes, interpreter_index) in [(fixture(), 1), (pie_with_phdr(), 2)] {
        bytes[0x180..0x180 + name.len()].fill(b'X');
        bytes[0x380..0x380 + name.len()].copy_from_slice(name);
        let start = 64 + interpreter_index * 56;
        put64(&mut bytes, start + 8, 0x380);
        put64(&mut bytes, start + 16, BASE + 0x380);
        assert_eq!(
            parse(&bytes).expect("relocated matching interpreter").interpreter.as_deref(),
            Some("/lib/ld-linux-aarch64.so.1")
        );
    }
}

#[test]
fn rejects_mapped_interpreter_strings_with_a_different_file_source() {
    for (mut bytes, interpreter_index) in [(fixture(), 1), (pie_with_phdr(), 2)] {
        let alias = b"/lib/different-loader.so\0";
        bytes[0x380..0x380 + alias.len()].copy_from_slice(alias);
        put64(&mut bytes, 64 + interpreter_index * 56 + 16, BASE + 0x380);
        let error = parse(&bytes).expect_err("file and mapped interpreter aliases differ");
        assert!(error.contains("interpreter file and virtual mappings disagree"), "{error}");
    }
}

#[test]
fn rejects_unmapped_interpreter_runtime_addresses() {
    let mut bytes = fixture();
    // This changes only p_vaddr; the file path and every other binding remain valid.
    put64(&mut bytes, 64 + 56 + 16, BASE + 0x10000);
    let error = parse(&bytes).expect_err("unmapped interpreter runtime alias");
    assert!(error.contains("metadata has no complete file-backed load mapping"), "{error}");
}

#[test]
fn rejects_bss_only_interpreter_runtime_strings() {
    let mut bytes = fixture();
    put64(&mut bytes, 64 + 40, 0x800);
    put64(&mut bytes, 64 + 56 + 16, BASE + 0x600);
    let error = parse(&bytes).expect_err("BSS cannot supply the named interpreter bytes");
    assert!(error.contains("metadata has no complete file-backed load mapping"), "{error}");
}

#[test]
fn rejects_partially_file_backed_interpreter_runtime_strings() {
    let mut bytes = fixture();
    put64(&mut bytes, 64 + 40, 0x800);
    put64(&mut bytes, 64 + 56 + 16, BASE + 0x4f0);
    let error = parse(&bytes).expect_err("interpreter suffix would come from BSS");
    assert!(error.contains("metadata has no complete file-backed load mapping"), "{error}");
}
