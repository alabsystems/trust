// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Bounded, read-only context for a rejected call or operand's exact struct-type IDs.
//!
//! This formats in-memory producer facts, not a valid module or proof artifact.
//! It never validates, repairs, serializes, admits, or republishes the module.
//! Struct rows join by unique explicit ID, never position or name. Unknown
//! layout/offsets stay unknown. Non-struct nominal tables are explicitly not
//! expanded; names, fields, inline types and graph traversal have visible limits.

use std::collections::BTreeSet;

use trust_ir::{FatPtrKind, Module, Ty};
use trust_ir_build::ValidationError;

const MAX_STRUCT_DEPTH: usize = 8;
const MAX_STRUCT_NODES: usize = 32;
const MAX_STRUCT_TABLE_ROWS: usize = 8192;
const MAX_TYPE_DEPTH: usize = 8;
const MAX_TYPE_VISITS: usize = 256;
const MAX_FIELDS: usize = 16;
const MAX_TUPLE_ELEMENTS: usize = 16;
const MAX_NAME_CHARS: usize = 128;
const MAX_OUTPUT_BYTES: usize = 8192;
const OUTPUT_TRUNCATION: &str = " [truncated:output]]";

/// Only the validator's exact canonical spelling identifies a diagnostic root.
fn canonical_struct_id(spelling: &str) -> Option<u32> {
    let digits = spelling.strip_prefix("struct.")?;
    if digits.is_empty() || digits.len() > 10 || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let id: u32 = digits.parse().ok()?;
    (digits == id.to_string()).then_some(id)
}

/// Append diagnostic context only; the original typed error remains untouched.
pub(super) fn for_error(module: &Module, error: &ValidationError) -> String {
    let (expected, actual) = match error {
        ValidationError::CallArgTypeMismatch { expected, actual, .. }
        | ValidationError::OperandTypeMismatch { expected, actual, .. } => (expected, actual),
        _ => return String::new(),
    };
    let roots =
        [("expected", canonical_struct_id(expected)), ("actual", canonical_struct_id(actual))];
    if roots.iter().all(|(_, root)| root.is_none()) {
        return String::new();
    }
    let mut context = Context {
        module,
        text: LimitedText::default(),
        active_structs: BTreeSet::new(),
        seen_structs: BTreeSet::new(),
        active_types: BTreeSet::new(),
        struct_nodes: 0,
        type_visits: 0,
    };
    context
        .text
        .push(" [type-context diagnostic-only proof_authority=false source_refinement=false");
    context.text.push(&format!(
        " limits(struct-depth={MAX_STRUCT_DEPTH},struct-nodes={MAX_STRUCT_NODES},struct-table-rows={MAX_STRUCT_TABLE_ROWS},type-depth={MAX_TYPE_DEPTH},type-visits={MAX_TYPE_VISITS},fields={MAX_FIELDS},tuple-elements={MAX_TUPLE_ELEMENTS},name-chars={MAX_NAME_CHARS},output-bytes={MAX_OUTPUT_BYTES})"
    ));
    for (role, root) in roots {
        context.text.push(&format!(" {role}="));
        match root {
            Some(id) => context.struct_row(id, 0),
            None => context.text.push("not-a-canonical-struct-root"),
        }
    }
    context.text.push("]");
    context.text.value
}

#[derive(Default)]
struct LimitedText {
    value: String,
    exhausted: bool,
}

impl LimitedText {
    fn push(&mut self, value: &str) {
        if self.exhausted {
            return;
        }
        let available = MAX_OUTPUT_BYTES - OUTPUT_TRUNCATION.len() - self.value.len();
        if value.len() <= available {
            self.value.push_str(value);
        } else {
            let mut boundary = available;
            while !value.is_char_boundary(boundary) {
                boundary -= 1;
            }
            self.value.push_str(&value[..boundary]);
            self.value.push_str(OUTPUT_TRUNCATION);
            self.exhausted = true;
        }
    }

    fn quoted(&mut self, value: &str) {
        self.push("\"");
        let mut chars = value.chars();
        for character in chars.by_ref().take(MAX_NAME_CHARS) {
            if self.exhausted {
                return;
            }
            for escaped in character.escape_debug() {
                self.push(escaped.encode_utf8(&mut [0; 4]));
            }
        }
        self.push("\"");
        if chars.next().is_some() {
            self.push("[truncated:name]");
        }
    }

    fn optional(&mut self, label: &str, value: Option<u64>) {
        self.push(label);
        match value {
            Some(value) => self.push(&value.to_string()),
            None => self.push("unknown"),
        }
    }
}

struct Context<'module> {
    module: &'module Module,
    text: LimitedText,
    active_structs: BTreeSet<u32>,
    seen_structs: BTreeSet<u32>,
    active_types: BTreeSet<u32>,
    struct_nodes: usize,
    type_visits: usize,
}

impl Context<'_> {
    fn struct_row(&mut self, id: u32, depth: usize) {
        self.text.push(&format!("Struct({id})"));
        if self.text.exhausted {
            return;
        }
        if self.active_structs.contains(&id) {
            self.text.push("[cycle:struct-id]");
            return;
        }
        if self.seen_structs.contains(&id) {
            self.text.push("[shared:already-described]");
            return;
        }
        if depth >= MAX_STRUCT_DEPTH {
            self.text.push("[truncated:struct-depth]");
            return;
        }
        if self.struct_nodes >= MAX_STRUCT_NODES {
            self.text.push("[truncated:struct-nodes]");
            return;
        }
        let module = self.module;
        if module.structs.len() > MAX_STRUCT_TABLE_ROWS {
            self.text.push("[truncated:struct-table-scan]");
            return;
        }
        let mut rows = module.structs.iter().filter(|row| row.id.index() == id);
        let Some(row) = rows.next() else {
            self.text.push("[missing:struct-id]");
            return;
        };
        if rows.next().is_some() {
            self.text.push("[ambiguous:duplicate-struct-id]");
            return;
        }
        self.struct_nodes += 1;
        self.seen_structs.insert(id);
        self.active_structs.insert(id);
        self.text.push("{name=");
        self.text.quoted(&row.name);
        self.text.optional(",size=", row.size);
        self.text.optional(",align=", row.align);
        self.text.push(&format!(",repr={:?},field-count={}", row.repr, row.fields.len()));
        for (index, field) in row.fields.iter().take(MAX_FIELDS).enumerate() {
            if self.text.exhausted {
                break;
            }
            self.text.push(&format!(",field[{index}]{{name="));
            self.text.quoted(&field.name);
            self.text.optional(",offset=", field.offset);
            self.text.push(",ty=");
            self.ty(&field.ty, depth + 1, 0);
            self.text.push("}");
        }
        if row.fields.len() > MAX_FIELDS {
            self.text.push(",[truncated:fields]");
        }
        self.text.push("}");
        self.active_structs.remove(&id);
    }

    fn table_ty(&mut self, id: u32, struct_depth: usize, type_depth: usize) {
        self.text.push(&format!("TyId({id})"));
        if self.active_types.contains(&id) {
            self.text.push("[cycle:type-id]");
            return;
        }
        let module = self.module;
        let Some(ty) = module.types.get(id as usize) else {
            self.text.push("[missing:type-id]");
            return;
        };
        self.active_types.insert(id);
        self.text.push("{");
        self.ty(ty, struct_depth, type_depth + 1);
        self.text.push("}");
        self.active_types.remove(&id);
    }

    fn ty(&mut self, ty: &Ty, struct_depth: usize, depth: usize) {
        if self.text.exhausted {
            return;
        }
        if depth >= MAX_TYPE_DEPTH {
            self.text.push("[truncated:type-depth]");
            return;
        }
        if self.type_visits >= MAX_TYPE_VISITS {
            self.text.push("[truncated:type-visits]");
            return;
        }
        self.type_visits += 1;
        // Exhaustive over this exact Trust-IR pin. Never recursively Debug an
        // unbounded inline type or cast a nominal Usize/Isize into U64/I64.
        match ty {
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Storage(_) => self.text.push(&format!("{ty:?}")),
            // Level R (trust-ir amendment S): a module type has no extension.
            Ty::Ext(e) => e.unreachable(),
            Ty::Struct(id) => self.struct_row(id.index(), struct_depth),
            Ty::Array(id, length) => {
                self.text.push(&format!("Array(length={length},element="));
                self.table_ty(id.index(), struct_depth, depth);
                self.text.push(")");
            }
            Ty::Tuple(elements) => {
                self.text.push(&format!("Tuple(count={})[", elements.len()));
                for (index, element) in elements.iter().take(MAX_TUPLE_ELEMENTS).enumerate() {
                    if self.text.exhausted {
                        break;
                    }
                    self.text.push(&format!("{index}="));
                    self.ty(element, struct_depth, depth + 1);
                    self.text.push(",");
                }
                if elements.len() > MAX_TUPLE_ELEMENTS {
                    self.text.push("[truncated:tuple-elements]");
                }
                self.text.push("]");
            }
            Ty::Vector(element, lanes) => {
                self.text.push(&format!("Vector(lanes={lanes},element="));
                self.ty(element, struct_depth, depth + 1);
                self.text.push(")");
            }
            // trust-ir v67's tensor carrier, by name, with its element type inline.
            Ty::Tensor(element, rank) => {
                self.text.push(&format!("Tensor(rank={rank},element="));
                self.ty(element, struct_depth, depth + 1);
                self.text.push(")");
            }
            Ty::Ref(inner) => self.wrapper("Ref", inner, struct_depth, depth),
            Ty::RefMut(inner) => self.wrapper("RefMut", inner, struct_depth, depth),
            Ty::PtrConst(inner) => self.wrapper("PtrConst", inner, struct_depth, depth),
            Ty::PtrMut(inner) => self.wrapper("PtrMut", inner, struct_depth, depth),
            Ty::Rc(inner) => self.wrapper("Rc", inner, struct_depth, depth),
            Ty::FatPtr(FatPtrKind::Slice(id)) => {
                self.text.push("FatPtr(Slice(");
                self.table_ty(id.index(), struct_depth, depth);
                self.text.push("))");
            }
            Ty::FatPtr(
                kind @ (FatPtrKind::Str
                | FatPtrKind::ContainerLen
                | FatPtrKind::ContainerVtable
                | FatPtrKind::TraitObject { .. }),
            ) => self.text.push(&format!("FatPtr({kind:?})")),
            Ty::Set(id, repr) => {
                self.text.push(&format!("Set(repr={repr:?},element="));
                self.table_ty(id.index(), struct_depth, depth);
                self.text.push(")");
            }
            Ty::Sequence(id) => {
                self.text.push("Sequence(");
                self.table_ty(id.index(), struct_depth, depth);
                self.text.push(")");
            }
            Ty::Refine(id, predicate) => {
                self.text.push(&format!("Refine(predicate-id={},base=", predicate.index()));
                self.table_ty(id.index(), struct_depth, depth);
                self.text.push(",predicate-table=not-expanded)");
            }
            Ty::Enum(id) => self.text.push(&format!("Enum({})[table=not-expanded]", id.index())),
            Ty::Func(id) => self.text.push(&format!("Func({})[table=not-expanded]", id.index())),
            Ty::FnItem(id) => {
                self.text.push(&format!("FnItem({})[function=not-expanded]", id.index()))
            }
            Ty::Record(id) => {
                self.text.push(&format!("Record({})[table=not-expanded]", id.index()))
            }
            Ty::Closure(id) => {
                self.text.push(&format!("Closure({})[table=not-expanded]", id.index()))
            }
            Ty::Dialect(value) => {
                self.text.push("Dialect(namespace=");
                self.text.quoted(&value.namespace);
                self.text.push(",name=");
                self.text.quoted(&value.name);
                self.text.push(&format!(",version={})", value.version));
            }
            Ty::Handle(value) => {
                self.text.push("Handle(runtime=");
                self.text.quoted(&value.runtime);
                self.text.push(",name=");
                self.text.quoted(&value.name);
                self.text.push(")");
            }
        }
    }

    fn wrapper(&mut self, tag: &str, inner: &Ty, struct_depth: usize, depth: usize) {
        self.text.push(tag);
        self.text.push("(");
        self.ty(inner, struct_depth, depth + 1);
        self.text.push(")");
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::{FieldDef, StructDef, StructId, StructRepr, TyId};

    use super::*;

    fn row(id: u32, name: &str, fields: Vec<Ty>) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: name.to_string(),
            fields: fields
                .into_iter()
                .enumerate()
                .map(|(index, ty)| FieldDef { name: format!("field{index}"), ty, offset: None })
                .collect(),
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        }
    }

    fn error(expected: &str, actual: &str) -> ValidationError {
        ValidationError::CallArgTypeMismatch {
            block: 1,
            callee: "push".to_string(),
            arg_index: 1,
            expected: expected.to_string(),
            actual: actual.to_string(),
            caller_producer: Some("trust".to_string()),
            callee_producer: Some("trust".to_string()),
        }
    }

    fn context(rows: Vec<StructDef>, expected: &str, actual: &str) -> String {
        let mut module = Module::new("diagnostic-test");
        module.structs = rows;
        for_error(&module, &error(expected, actual))
    }

    #[test]
    fn storage_geometry_diagnostic_keeps_exact_fields_and_no_authority() {
        let geometry = trust_ir::StorageLayout::new(u64::MAX, 1);
        let output =
            context(vec![row(0, "StorageOwner", vec![Ty::Storage(geometry)])], "struct.0", "ptr");
        assert!(
            output.contains(
                "Storage(StorageLayout { size_bytes: 18446744073709551615, align_bytes: 1 })"
            ),
            "{output}"
        );
        assert!(output.contains("proof_authority=false"));
        assert!(output.contains("source_refinement=false"));
        assert!(output.len() <= MAX_OUTPUT_BYTES);
    }

    #[test]
    fn a_tensor_field_is_rendered_by_name_with_no_authority() {
        let output = context(
            vec![row(0, "Weights", vec![Ty::Tensor(Box::new(Ty::I32), 2)])],
            "struct.0",
            "ptr",
        );
        assert!(output.contains("Tensor(rank=2,element=I32)"), "{output}");
        assert!(output.contains("proof_authority=false"));
        assert!(output.len() <= MAX_OUTPUT_BYTES);
    }

    #[test]
    fn function_item_diagnostics_keep_nominal_ids_and_no_authority() {
        let output = context(
            vec![row(0, "Items", vec![Ty::FnItem(trust_ir::FuncId::new(7))])],
            "struct.0",
            "ptr",
        );
        assert!(output.contains("FnItem(7)[function=not-expanded]"), "{output}");
        assert!(output.contains("proof_authority=false"));
        assert!(output.contains("source_refinement=false"));
        assert!(output.len() <= MAX_OUTPUT_BYTES);
    }

    #[test]
    fn a_function_item_field_is_rendered_by_name_with_no_authority() {
        let output = context(
            vec![row(0, "Item", vec![Ty::FnItem(trust_ir::FuncId::new(7))])],
            "struct.0",
            "ptr",
        );
        assert!(output.contains("FnItem(7)[function=not-expanded]"), "{output}");
        assert!(output.contains("proof_authority=false"));
        assert!(output.len() <= MAX_OUTPUT_BYTES);
    }

    #[test]
    fn only_exact_canonical_struct_ids_join() {
        for bad in [
            "",
            "struct.",
            "struct.+1",
            "struct.-1",
            "struct.01",
            " struct.1",
            "struct.1 ",
            "struct.1x",
            "Struct(1)",
            "struct.4294967296",
            "struct.١",
        ] {
            assert_eq!(canonical_struct_id(bad), None, "{bad}");
        }
        assert_eq!(canonical_struct_id("struct.0"), Some(0));
        assert_eq!(canonical_struct_id("struct.4294967295"), Some(u32::MAX));
        assert!(context(vec![row(1, "S", vec![Ty::U32])], "struct.01", "ptr").is_empty());
    }

    #[test]
    fn explicit_ids_not_position_or_name_select_the_row() {
        let text = context(
            vec![row(9, "same", vec![Ty::Usize]), row(1, "same", vec![Ty::U64])],
            "struct.1",
            "struct.9",
        );
        assert!(text.contains("expected=Struct(1){name=\"same\""));
        assert!(text.contains("actual=Struct(9){name=\"same\""));
        assert!(text.contains("ty=U64"));
        assert!(text.contains("ty=Usize"));
        assert!(text.contains("proof_authority=false source_refinement=false"));
    }

    #[test]
    fn missing_and_duplicate_ids_never_choose_a_claimant() {
        let text = context(
            vec![row(1, "first", vec![Ty::U32]), row(1, "second", vec![Ty::U64])],
            "struct.1",
            "struct.99",
        );
        assert!(text.contains("Struct(1)[ambiguous:duplicate-struct-id]"));
        assert!(text.contains("Struct(99)[missing:struct-id]"));
        assert!(!text.contains("first"));
        assert!(!text.contains("second"));
    }

    #[test]
    fn oversize_struct_table_is_not_partially_joined() {
        let mut rows = vec![row(9, "early-claimant", vec![Ty::U32]); MAX_STRUCT_TABLE_ROWS + 1];
        rows[MAX_STRUCT_TABLE_ROWS] = row(9, "late-claimant", vec![Ty::U64]);
        let text = context(rows, "struct.9", "ptr");
        assert!(text.contains("[truncated:struct-table-scan]"));
        assert!(!text.contains("early-claimant"));
        assert!(!text.contains("late-claimant"));
    }

    #[test]
    fn faithful_and_unit_sibling_facts_preserve_unknown_layouts() {
        let mut faithful = row(9, "S", vec![Ty::U32, Ty::Struct(StructId::new(8))]);
        faithful.size = Some(32);
        faithful.align = Some(8);
        faithful.fields[0].offset = Some(24);
        faithful.fields[1].offset = Some(0);
        let degraded = row(10, "S", vec![Ty::U32, Ty::Unit]);
        let text = context(
            vec![faithful, degraded, row(8, "Vec", vec![Ty::Ptr, Ty::Usize])],
            "struct.9",
            "struct.10",
        );
        assert!(text.contains("size=32,align=8"));
        assert!(text.contains("offset=24,ty=U32"));
        assert!(text.contains("offset=0,ty=Struct(8)"));
        assert!(text.contains("Struct(10){name=\"S\",size=unknown,align=unknown"));
        assert!(text.contains("offset=unknown,ty=Unit"));
    }

    #[test]
    fn missing_nested_struct_id_and_array_type_id_are_explicit() {
        let text = context(
            vec![row(1, "S", vec![Ty::Struct(StructId::new(9)), Ty::Array(TyId::new(7), 0)])],
            "struct.1",
            "ptr",
        );
        assert!(text.contains("Struct(9)[missing:struct-id]"));
        assert!(text.contains("Array(length=0,element=TyId(7)[missing:type-id])"));
    }

    #[test]
    fn cycles_and_shared_subgraphs_are_different() {
        let text = context(
            vec![
                row(1, "root", vec![Ty::Struct(StructId::new(2)), Ty::Struct(StructId::new(2))]),
                row(2, "child", vec![Ty::Struct(StructId::new(1))]),
            ],
            "struct.1",
            "struct.2",
        );
        assert!(text.contains("Struct(1)[cycle:struct-id]"));
        assert!(text.contains("Struct(2)[shared:already-described]"));
        assert!(text.len() <= MAX_OUTPUT_BYTES);
    }

    #[test]
    fn type_table_cycle_does_not_recurse_forever() {
        let mut module = Module::new("type-cycle");
        module.structs.push(row(1, "S", vec![Ty::Array(TyId::new(0), 3)]));
        module.types.push(Ty::Sequence(TyId::new(0)));
        let text = for_error(&module, &error("struct.1", "ptr"));
        assert!(text.contains("TyId(0)[cycle:type-id]"));
    }

    #[test]
    fn field_tuple_and_name_limits_are_visible() {
        let fields = vec![Ty::Tuple(vec![Ty::U32; MAX_TUPLE_ELEMENTS + 1]); MAX_FIELDS + 1];
        let text =
            context(vec![row(1, &"é".repeat(MAX_NAME_CHARS + 1), fields)], "struct.1", "ptr");
        assert!(text.contains("[truncated:name]"));
        assert!(text.contains("[truncated:tuple-elements]"));
        assert!(text.contains("[truncated:fields]"));
        assert!(text.contains("field-count=17"));
        assert!(text.len() <= MAX_OUTPUT_BYTES);
    }

    #[test]
    fn struct_depth_limit_is_explicit() {
        let rows = (0..=MAX_STRUCT_DEPTH as u32)
            .map(|id| row(id, "S", vec![Ty::Struct(StructId::new(id + 1))]))
            .collect();
        assert!(context(rows, "struct.0", "ptr").contains("[truncated:struct-depth]"));
    }

    #[test]
    fn struct_node_fuel_is_explicit() {
        let mut fields = Vec::new();
        let mut rows = Vec::new();
        for id in 1..=MAX_FIELDS as u32 {
            fields.push(Ty::Struct(StructId::new(id)));
            rows.push(row(
                id,
                "S",
                vec![Ty::Struct(StructId::new(id + 100)), Ty::Struct(StructId::new(id + 200))],
            ));
            rows.push(row(id + 100, "leaf", vec![]));
            rows.push(row(id + 200, "leaf", vec![]));
        }
        rows.push(row(0, "root", fields));
        assert!(context(rows, "struct.0", "ptr").contains("[truncated:struct-nodes]"));
    }

    #[test]
    fn type_depth_and_visit_fuel_are_explicit() {
        let mut ty = Ty::U32;
        for _ in 0..MAX_TYPE_DEPTH {
            ty = Ty::Ref(Box::new(ty));
        }
        assert!(
            context(vec![row(1, "S", vec![ty])], "struct.1", "ptr")
                .contains("[truncated:type-depth]")
        );
        let fields = vec![Ty::Tuple(vec![Ty::U32; MAX_TUPLE_ELEMENTS]); MAX_FIELDS];
        assert!(
            context(vec![row(1, "S", fields)], "struct.1", "ptr")
                .contains("[truncated:type-visits]")
        );
    }

    #[test]
    fn output_bound_preserves_utf8_and_explicit_truncation() {
        let mut text = LimitedText::default();
        text.push("proof_authority=false ");
        for _ in 0..MAX_OUTPUT_BYTES {
            text.quoted("😀😀😀😀");
        }
        assert!(text.value.len() <= MAX_OUTPUT_BYTES);
        assert!(text.value.ends_with(OUTPUT_TRUNCATION));
        assert!(text.value.starts_with("proof_authority=false"));
    }

    #[test]
    fn non_type_errors_and_module_contents_are_unchanged() {
        let mut module = Module::new("unchanged");
        module.structs.push(row(1, "S", vec![Ty::U32]));
        let before = module.clone();
        let non_call_type_error = ValidationError::CallArgCountMismatch {
            block: 1,
            callee: "push".to_string(),
            expected: 2,
            actual: 1,
            caller_producer: None,
            callee_producer: None,
        };
        assert!(for_error(&module, &non_call_type_error).is_empty());
        let typed = error("struct.1", "ptr");
        let rendered = format!("{typed:?}");
        assert!(!for_error(&module, &typed).is_empty());
        assert_eq!(rendered, format!("{typed:?}"));
        assert_eq!(before, module);
    }
}

#[cfg(test)]
#[path = "validation_type_context_caller_tests.rs"]
mod caller_tests;
