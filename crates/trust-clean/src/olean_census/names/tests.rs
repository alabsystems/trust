use super::*;

const BASE: u64 = 0x1000;

struct Raw(Vec<u8>);
impl Raw {
    fn new() -> Self {
        let mut bytes = vec![0; 96];
        bytes[..5].copy_from_slice(b"olean");
        bytes[5] = 2;
        bytes[6] = 1;
        bytes[7..17].copy_from_slice(b"4.30.0-rc2");
        bytes[40..80].fill(b'a');
        bytes[80..88].copy_from_slice(&BASE.to_le_bytes());
        Self(bytes)
    }
    fn object(&mut self, tag: u8, fields: &[u64], size: u16, scalar: &[u8]) -> u64 {
        while self.0.len() % 8 != 0 {
            self.0.push(0);
        }
        let pointer = BASE + self.0.len() as u64;
        self.0.extend_from_slice(&[0, 0, 0, 0]);
        self.0.extend_from_slice(&size.to_le_bytes());
        self.0.extend_from_slice(&[fields.len() as u8, tag]);
        for field in fields {
            self.0.extend_from_slice(&field.to_le_bytes());
        }
        self.0.extend_from_slice(scalar);
        pointer
    }
    fn string(&mut self, text: &str) -> u64 {
        let pointer = self.object(tags::STRING, &[], 0, &[]);
        self.0.extend_from_slice(&(text.len() as u64 + 1).to_le_bytes());
        self.0.extend_from_slice(&(text.len() as u64 + 1).to_le_bytes());
        self.0.extend_from_slice(&(text.chars().count() as u64).to_le_bytes());
        self.0.extend_from_slice(text.as_bytes());
        self.0.push(0);
        pointer
    }
    fn name(&mut self, mode: NameMode, tag: u8, parent: u64, value: u64) -> u64 {
        self.object(
            tag,
            &[parent, value],
            if mode == NameMode::Lean { 32 } else { 0 },
            if mode == NameMode::Lean { &[0; 8] } else { &[] },
        )
    }
    fn str_name(&mut self, mode: NameMode, parent: u64, text: &str) -> u64 {
        let value = self.string(text);
        self.name(mode, 1, parent, value)
    }
    fn mpz(&mut self, limbs: &[u64], size: i32) -> u64 {
        let pointer = self.object(250, &[], (24 + limbs.len() * 8) as u16, &[]);
        self.0.extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.0.extend_from_slice(&size.to_le_bytes());
        self.0.extend_from_slice(&(pointer + 24).to_le_bytes());
        for limb in limbs {
            self.0.extend_from_slice(&limb.to_le_bytes());
        }
        pointer
    }
    fn view(&self, mode: NameMode) -> View<'_> {
        View { regions: vec![(BASE, &self.0)], max_rows: 20, mode }
    }
    fn set_word(&mut self, pointer: u64, offset: usize, value: u64) {
        let start = (pointer - BASE) as usize + offset;
        self.0[start..start + 8].copy_from_slice(&value.to_le_bytes());
    }
}

#[test]
fn typed_name_scalar_nat_is_unboxed_and_distinct_from_numeric_strings() {
    let mut raw = Raw::new();
    let parent = raw.str_name(NameMode::Lean, 1, "Quoted.Parent");
    for n in [0, 7, (u64::MAX >> 1)] {
        let pointer = raw.name(NameMode::Lean, 2, parent, (n << 1) | 1);
        assert_eq!(
            raw.view(NameMode::Lean).name(pointer).unwrap(),
            ModuleName(vec![Segment::Str("Quoted.Parent".into()), Segment::Num(n)])
        );
    }
    for text in ["0", "7", "07", "", "fidèle", "A.B"] {
        let pointer = raw.str_name(NameMode::Lean, parent, text);
        assert_eq!(
            raw.view(NameMode::Lean).name(pointer).unwrap().0.last(),
            Some(&Segment::Str(text.into()))
        );
    }
}

#[test]
fn typed_name_inline_mpz_retains_u64_and_refuses_larger_nat() {
    for n in [1u64 << 63, u64::MAX] {
        let mut raw = Raw::new();
        let value = raw.mpz(&[n], 1);
        let pointer = raw.name(NameMode::Lean, 2, 1, value);
        assert_eq!(
            raw.view(NameMode::Lean).name(pointer).unwrap(),
            ModuleName(vec![Segment::Num(n)])
        );
    }
    let mut raw = Raw::new();
    let value = raw.mpz(&[0, 1], 2);
    let pointer = raw.name(NameMode::Lean, 2, 1, value);
    assert!(raw.view(NameMode::Lean).name(pointer).unwrap_err().contains("exceeds the u64"));
}

#[test]
fn typed_name_mpz_rejects_sign_size_pointer_header_and_noncanonical_limbs() {
    for mutation in 0..9 {
        let mut raw = Raw::new();
        let value = raw.mpz(&[1u64 << 63], 1);
        match mutation {
            0 => raw.set_word(value, 8, (u64::from(u32::MAX) << 32) | 1),
            1 => raw.set_word(value, 8, 1),
            2 => raw.set_word(value, 8, 1u64 << 32),
            3 => raw.set_word(value, 16, value + 16),
            4 => raw.set_word(value, 24, 7),
            5 => raw.0[(value - BASE) as usize + 7] = 249,
            6 => raw.0[(value - BASE) as usize + 4] = 40,
            7 => raw.0[(value - BASE) as usize] = 1,
            _ => raw.0[(value - BASE) as usize + 6] = 1,
        }
        let pointer = raw.name(NameMode::Lean, 2, 1, value);
        assert!(raw.view(NameMode::Lean).name(pointer).is_err(), "mutation {mutation}");
    }
}

#[test]
fn typed_name_module_mode_never_falls_back_per_object() {
    let mut raw = Raw::new();
    let legacy = raw.name(NameMode::CleanLegacy, 2, 1, 7);
    let modern = raw.name(NameMode::Lean, 2, 1, 15);
    assert_eq!(
        raw.view(NameMode::CleanLegacy).name(legacy).unwrap(),
        ModuleName(vec![Segment::Num(7)])
    );
    assert!(raw.view(NameMode::Lean).name(legacy).is_err());
    assert!(raw.view(NameMode::CleanLegacy).name(modern).is_err());
    let anonymous_object = raw.object(0, &[], 0, &[]);
    assert!(raw.view(NameMode::CleanLegacy).name(anonymous_object).unwrap().0.is_empty());
    assert!(raw.view(NameMode::Lean).name(anonymous_object).is_err());
    assert!(raw.view(NameMode::Lean).name(1).unwrap().0.is_empty());
}

#[test]
fn typed_name_rejects_bad_scalar_cycle_region_and_component_budget() {
    let mut raw = Raw::new();
    let pointer = raw.name(NameMode::Lean, 2, 1, 15);
    for bad in [0, 3, 5, 0x3000] {
        assert!(raw.view(NameMode::Lean).name(bad).is_err());
    }
    raw.set_word(pointer, 8, pointer);
    assert!(raw.view(NameMode::Lean).name(pointer).unwrap_err().contains("cycle"));
    raw.set_word(pointer, 8, 1);
    let view =
        View { regions: vec![(BASE, &raw.0), (BASE, &raw.0)], max_rows: 20, mode: NameMode::Lean };
    assert!(view.name(pointer).unwrap_err().contains("2 regions"));
    let mut parent = 1;
    for _ in 0..256 {
        parent = raw.name(NameMode::Lean, 2, parent, 1);
    }
    assert_eq!(raw.view(NameMode::Lean).name(parent).unwrap().0.len(), 256);
    parent = raw.name(NameMode::Lean, 2, parent, 1);
    assert!(raw.view(NameMode::Lean).name(parent).is_err());
}

#[test]
fn typed_name_rejects_malformed_string_layout_bounds_and_utf8() {
    for mutation in 0..8 {
        let mut raw = Raw::new();
        let string = raw.string("hello");
        match mutation {
            0 => raw.set_word(string, 8, 1_048_577),
            1 => raw.set_word(string, 16, 1),
            2 => raw.set_word(string, 24, 2),
            3 => raw.0[(string - BASE) as usize + 32] = 0xff,
            4 => raw.0[(string - BASE) as usize + 37] = b'x',
            5 => raw.0[(string - BASE) as usize + 7] = 250,
            6 => raw.0[(string - BASE) as usize] = 1,
            _ => raw.set_word(string, 8, 0),
        }
        let pointer = raw.name(NameMode::Lean, 1, 1, string);
        assert!(raw.view(NameMode::Lean).name(pointer).is_err(), "mutation {mutation}");
    }
}

#[test]
fn import_flags_modern_one_hot_meanings_and_legacy_projection_stay_distinct() {
    for flags in [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]] {
        let mut raw = Raw::new();
        let name = raw.str_name(NameMode::Lean, 1, "Lean");
        let pointer = raw.object(0, &[name], 24, &[flags[0], flags[1], flags[2], 0, 0, 0, 0, 0]);
        let row = raw.view(NameMode::Lean).row(0, pointer, 0);
        assert!(row.error.is_none(), "{:?}", row.error);
        assert_eq!(row.runtime_only, None);
        assert_eq!(row.parser_first_flag_projection(), Some(flags[0] != 0));
        let json = serde_json::to_value(&row).unwrap();
        assert_eq!(
            json["import_flags"],
            serde_json::json!({"layout":"lean","import_all":flags[0]!=0,"is_exported":flags[1]!=0,"is_meta":flags[2]!=0})
        );
    }
    let mut raw = Raw::new();
    let name = raw.str_name(NameMode::CleanLegacy, 1, "Lean");
    let pointer = raw.object(0, &[name], 0, &[1, 0, 0, 0, 0, 0, 0, 0]);
    let row = raw.view(NameMode::CleanLegacy).row(0, pointer, 0);
    assert_eq!(row.runtime_only, Some(true));
    assert!(matches!(row.import_flags, Some(ImportFlags::CleanLegacy { runtime_only: true })));
    assert!(raw.view(NameMode::Lean).row(0, pointer, 0).error.is_some());
}

#[test]
fn import_flags_refuse_each_nonboolean_layout_and_missing_byte() {
    for index in 0..3 {
        let mut raw = Raw::new();
        let name = raw.str_name(NameMode::Lean, 1, "Lean");
        let mut flags = [0; 8];
        flags[index] = 2;
        let pointer = raw.object(0, &[name], 24, &flags);
        assert!(raw.view(NameMode::Lean).row(0, pointer, 0).error.is_some());
    }
    for flags in [&[][..], &[0][..], &[0, 0][..]] {
        let mut raw = Raw::new();
        let name = raw.str_name(NameMode::Lean, 1, "Lean");
        let pointer = raw.object(0, &[name], 24, flags);
        assert!(raw.view(NameMode::Lean).row(0, pointer, 0).error.is_some());
    }
}

#[test]
fn module_envelope_refuses_unknown_tag_fields_size_and_reference_count() {
    let valid = ObjectHeader { rc: 0, cs_sz: 56, other: 5, tag: 0 };
    assert_eq!(NameMode::from_module_header(valid).unwrap(), NameMode::Lean);
    assert_eq!(
        NameMode::from_module_header(ObjectHeader { cs_sz: 0, ..valid }).unwrap(),
        NameMode::CleanLegacy
    );
    for bad in [
        ObjectHeader { tag: 1, ..valid },
        ObjectHeader { other: 4, ..valid },
        ObjectHeader { cs_sz: 48, ..valid },
        ObjectHeader { rc: 1, ..valid },
    ] {
        assert!(NameMode::from_module_header(bad).is_err());
    }
}

#[test]
fn typed_name_heap_nat_requires_actual_containing_region_gmp_header() {
    let mut raw = Raw::new();
    let value = raw.mpz(&[1u64 << 63], 1);
    let pointer = raw.name(NameMode::Lean, 2, 1, value);
    assert!(raw.view(NameMode::Lean).name(pointer).is_ok());
    for flags in [0, 2, 3, 255] {
        raw.0[6] = flags;
        assert!(raw.view(NameMode::Lean).name(pointer).unwrap_err().contains("known GMP flags"));
    }
    // The same modern scalar identity does not depend on a heap Nat encoding.
    let scalar = raw.name(NameMode::Lean, 2, 1, 15);
    assert_eq!(raw.view(NameMode::Lean).name(scalar).unwrap(), ModuleName(vec![Segment::Num(7)]));
}

fn ir_numeric_name_fixture(n: u64, exceeds_u64: bool) -> (Vec<u8>, u64) {
    let mut raw = Raw::new();
    let mut extension_name = 1;
    for text in ["Lean", "IR", "declMapExt"] {
        extension_name = raw.str_name(NameMode::Lean, extension_name, text);
    }
    let parent = raw.str_name(NameMode::Lean, 1, "IR.numeric");
    let numeral = if exceeds_u64 {
        raw.mpz(&[0, 1], 2)
    } else if n > u64::MAX >> 1 {
        raw.mpz(&[n], 1)
    } else {
        (n << 1) | 1
    };
    let name = raw.name(NameMode::Lean, 2, parent, numeral);
    let empty = raw.object(tags::ARRAY, &[], 0, &[0; 16]);
    let body = raw.object(10, &[3], 16, &[]); // return erased; no fake SSA variable.
    let decl = raw.object(0, &[name, empty, 3, body, 1], 48, &[]);
    let entries = raw.object(tags::ARRAY, &[], 0, &[0; 16]);
    raw.set_word(entries, 8, 1);
    raw.set_word(entries, 16, 1);
    raw.0.extend_from_slice(&decl.to_le_bytes());
    let extension = raw.object(0, &[extension_name, entries], 24, &[]);
    let extensions = raw.object(tags::ARRAY, &[], 0, &[0; 16]);
    raw.set_word(extensions, 8, 1);
    raw.set_word(extensions, 16, 1);
    raw.0.extend_from_slice(&extension.to_le_bytes());
    let root = raw.object(0, &[empty, empty, empty, empty, extensions], 56, &[0; 8]);
    raw.0[88..96].copy_from_slice(&root.to_le_bytes());
    (raw.0, name)
}

#[test]
fn ir_name_adapter_uses_same_scalar_and_heap_numeric_identity() {
    for n in [0, 7, 1u64 << 63, u64::MAX] {
        let (bytes, _) = ir_numeric_name_fixture(n, false);
        let observed = super::super::ir::observe(&bytes, &[], 100, 10000);
        assert!(observed.errors.is_empty(), "{:?}", observed.errors);
        assert_eq!(
            observed.report["rows"][0]["declaration"]["name"],
            serde_json::json!(ModuleName(vec![Segment::Str("IR.numeric".into()), Segment::Num(n)]))
        );
        assert_eq!(observed.report["effects_and_lowering"], "unmeasured");
    }
}

#[test]
fn ir_name_adapter_refuses_overflow_and_malformed_modern_name_without_dropping_row() {
    let (too_wide, _) = ir_numeric_name_fixture(0, true);
    let (mut malformed, name) = ir_numeric_name_fixture(7, false);
    malformed[(name - BASE) as usize + 4] = 0; // forbidden legacy object fallback.
    for bytes in [too_wide, malformed] {
        let observed = super::super::ir::observe(&bytes, &[], 100, 10000);
        assert!(!observed.errors.is_empty());
        assert_eq!(observed.report["rows"].as_array().unwrap().len(), 1);
        assert_eq!(observed.report["rows"][0]["status"], "unmeasured");
        assert!(observed.report["rows"][0]["error"].is_string());
    }
}

#[test]
fn ir_shared_name_reader_charges_access_budget_and_retains_failure() {
    let (bytes, _) = ir_numeric_name_fixture(1u64 << 63, false);
    let complete = super::super::ir::observe(&bytes, &[], 100, 10000);
    assert!(complete.errors.is_empty());
    let used = 10000 - complete.report["remaining_object_accesses"].as_u64().unwrap() as usize;
    assert!(used > 1);
    let limited = super::super::ir::observe(&bytes, &[], 100, used - 1);
    assert!(!limited.errors.is_empty());
    assert_eq!(limited.report["status"], "incomplete-syntax-observation");
    assert_eq!(super::super::ir::observe(&bytes, &[], 100, used).errors, Vec::<String>::new());
}

#[test]
fn legacy_name_component_bound_does_not_count_allocated_anonymous_parent() {
    let mut raw = Raw::new();
    let mut parent = raw.object(0, &[], 0, &[]);
    for _ in 0..256 {
        parent = raw.name(NameMode::CleanLegacy, 2, parent, 0);
    }
    assert_eq!(raw.view(NameMode::CleanLegacy).name(parent).unwrap().0.len(), 256);
    parent = raw.name(NameMode::CleanLegacy, 2, parent, 0);
    assert!(raw.view(NameMode::CleanLegacy).name(parent).is_err());
}

#[test]
fn named_inventory_array_requires_measured_tag_header_and_capacity() {
    for mutation in 0..4 {
        let mut raw = Raw::new();
        let array = raw.object(tags::ARRAY, &[], 0, &[0; 24]);
        assert!(raw.view(NameMode::Lean).array(array).unwrap().is_empty());
        let offset = (array - BASE) as usize;
        match mutation {
            0 => raw.0[offset + 7] = tags::STRUCT_ARRAY,
            1 => raw.0[offset] = 1,
            2 => raw.0[offset + 6] = 1,
            _ => raw.set_word(array, 8, 1), // logical length exceeds capacity0.
        }
        assert!(raw.view(NameMode::Lean).array(array).is_err(), "mutation {mutation}");
    }
}

mod root_controls;
