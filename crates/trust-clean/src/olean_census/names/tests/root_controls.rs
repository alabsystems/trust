use super::super::super::ir;
use super::*;

fn root(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes[88..96].try_into().unwrap())
}

fn companion(base: u64, borrowed: u64) -> Vec<u8> {
    let mut bytes = Raw::new().0;
    bytes[80..88].copy_from_slice(&base.to_le_bytes());
    bytes[88..96].copy_from_slice(&borrowed.to_le_bytes());
    bytes
}

fn populated() -> Vec<u8> {
    let (bytes, name) = ir_numeric_name_fixture(7, false);
    let old_root = (root(&bytes) - BASE) as usize;
    let mut fields: Vec<_> = (0..5)
        .map(|i| {
            u64::from_le_bytes(
                bytes[old_root + 8 + 8 * i..old_root + 16 + 8 * i].try_into().unwrap(),
            )
        })
        .collect();
    let mut raw = Raw(bytes);
    let names = raw.object(tags::ARRAY, &[], 0, &[0; 16]);
    raw.set_word(names, 8, 1);
    raw.set_word(names, 16, 1);
    raw.0.extend_from_slice(&name.to_le_bytes());
    fields[1] = names;
    let root = raw.object(0, &fields, 56, &[0; 8]);
    raw.0[88..96].copy_from_slice(&root.to_le_bytes());
    raw.0
}

fn refuse(part: &[u8], dependencies: &[&[u8]]) {
    let names = witness(part, dependencies, 100);
    assert!(!names.errors.is_empty(), "unexpected complete name witness");
    assert!(names.const_names.is_empty());
    let ir = ir::observe(part, dependencies, 100, 10000);
    assert!(!ir.errors.is_empty(), "unexpected complete IR observation");
    assert_eq!(ir.report["status"], "incomplete-syntax-observation");
    assert!(ir.report["rows"].as_array().unwrap().is_empty());
}

#[test]
fn complete_prior_base_and_server_roots_keep_current_physical_rows() {
    let owner = populated();
    let private = companion(0x4000, root(&owner));
    let prior = companion(0x100, 1);
    for dependencies in [vec![], vec![owner.as_slice()], vec![prior.as_slice(), owner.as_slice()]] {
        let part = if dependencies.is_empty() { owner.as_slice() } else { private.as_slice() };
        let names = witness(part, &dependencies, 100);
        assert!(names.errors.is_empty(), "{:?}", names.errors);
        assert_eq!(names.const_names.len(), 1);
        assert_eq!(names.const_names[0].index, 0);
        let expected = ModuleName(vec![Segment::Str("IR.numeric".into()), Segment::Num(7)]);
        assert_eq!(names.const_names[0].name, Some(expected.clone()));
        let observed = ir::observe(part, &dependencies, 100, 10000);
        assert!(observed.errors.is_empty(), "{:?}", observed.errors);
        assert_eq!(observed.report["extensions"].as_array().unwrap().len(), 1);
        assert_eq!(observed.report["rows"].as_array().unwrap().len(), 1);
        assert_eq!(observed.report["rows"][0]["index"], 0);
        assert_eq!(observed.report["rows"][0]["declaration"]["name"], serde_json::json!(expected));
    }
}

#[test]
fn missing_gap_duplicate_and_interior_overlapping_root_owners_refuse() {
    let owner = populated();
    let private = companion(0x4000, root(&owner));
    refuse(&private, &[]); // An uncaptured owner/future part is never searched.
    refuse(&companion(0x4000, 0x3000), &[&owner]);
    refuse(&private, &[&owner, &owner]);
    // This second region does not contain the root pointer itself.
    let overlap = companion(root(&owner) + 16, 1);
    refuse(&private, &[&owner, &overlap]);
}

#[test]
fn roots_in_file_headers_root_slots_or_tagged_words_refuse() {
    let owner = populated();
    for pointer in [0, 1, 3, BASE, BASE + 8, BASE + 80, BASE + 88] {
        refuse(&companion(0x4000, pointer), &[&owner]);
    }
}

#[test]
fn otherwise_valid_unaligned_root_objects_refuse() {
    let owner = populated();
    let at = (root(&owner) - BASE) as usize;
    for shift in [2usize, 4, 6] {
        let mut shifted = owner.clone();
        shifted.splice(at..at, vec![0; shift]);
        let root = BASE + (at + shift) as u64;
        shifted[88..96].copy_from_slice(&root.to_le_bytes());
        // Only the root moved; all five array references remain valid.
        refuse(&companion(0x4000, root), &[&shifted]);
    }
}

#[test]
fn whole_modern_root_extent_header_and_boolean_are_required() {
    let owner = populated();
    let at = (root(&owner) - BASE) as usize;
    for mutation in 0..8 {
        let mut malformed = owner.clone();
        match mutation {
            0 => malformed.truncate(at + 49), // Boolean exists, final padding does not.
            1 => malformed[at] = 1,
            2 => malformed[at + 6] = 4,
            3 => malformed[at + 7] = 1,
            4 => malformed[at + 48] = 2,
            5 => malformed[at + 4..at + 6].copy_from_slice(&48u16.to_le_bytes()),
            6 => malformed[at + 4..at + 6].copy_from_slice(&64u16.to_le_bytes()),
            _ => malformed.truncate(at + 7),
        }
        refuse(&companion(0x4000, root(&owner)), &[&malformed]);
    }
}

#[test]
fn legacy_root_requires_all_48_bytes_without_modern_fallback() {
    let mut raw = Raw::new();
    let empty = raw.object(tags::ARRAY, &[], 0, &[0; 16]);
    let pointer = raw.object(0, &[empty; 5], 0, &[]);
    raw.0[88..96].copy_from_slice(&pointer.to_le_bytes());
    let part = companion(0x4000, pointer);
    assert!(witness(&part, &[&raw.0], 100).errors.is_empty());
    let observed = ir::observe(&part, &[&raw.0], 100, 100);
    assert!(observed.errors.is_empty(), "{:?}", observed.errors);
    assert_eq!(observed.report["module_envelope"]["layout"], "clean-legacy-five-arrays-no-scalar");
    raw.0.pop();
    refuse(&part, &[&raw.0]);
}

#[test]
fn borrowed_root_header_and_extent_reads_consume_the_ir_budget() {
    let mut raw = Raw::new();
    let empty = raw.object(tags::ARRAY, &[], 0, &[0; 16]);
    let pointer = raw.object(0, &[empty; 5], 56, &[0; 8]);
    raw.0[88..96].copy_from_slice(&pointer.to_le_bytes());
    let part = companion(0x4000, pointer);
    for budget in [0, 1, 2, 13] {
        let observed = ir::observe(&part, &[&raw.0], 100, budget);
        assert!(
            observed.errors.iter().any(|e| e.contains("object-access resource bound")),
            "{budget}: {:?}",
            observed.errors
        );
    }
    let exact = ir::observe(&part, &[&raw.0], 100, 14);
    assert!(exact.errors.is_empty(), "{:?}", exact.errors);
    assert_eq!(exact.report["remaining_object_accesses"], 0);
}
