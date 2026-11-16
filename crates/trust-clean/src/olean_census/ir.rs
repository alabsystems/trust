//! Bounded raw Lean compiler-IR syntax observation. Diagnostic only. No environment construction, declaration admission,
//! lowering or executable authority. Nested AST observations are not semantics.
use std::cell::Cell;
use std::collections::BTreeSet;

use clean_olean::header::{HEADER_SIZE, HEADER_SIZE_V2, OleanHeader};
use clean_olean::region::{CompactedRegion, ObjectHeader, is_ptr, tags};
use serde_json::{Value, json};

use super::names::{NameAccess, NameMode, module_mode, read_name};

mod bindings;
mod literals;
type R<T> = Result<T, String>;
const LIMIT: usize = 10_000;

#[cfg(test)]
mod numeric_controls {
    use super::*;

    #[test]
    fn null_nat_is_not_a_valid_zero_index() {
        let view = View {
            regions: vec![],
            budget: Cell::new(100),
            array_limit: 100,
            name_mode: NameMode::Lean,
        };
        assert!(view.nat(0).is_err());
        assert!(view.nat(2).is_err());
        assert_eq!(view.nat(1).unwrap(), json!(0));
        assert_eq!(view.nat(3).unwrap(), json!(1));
    }

    #[test]
    fn null_ir_type_is_not_float() {
        let view = View {
            regions: vec![],
            budget: Cell::new(100),
            array_limit: 100,
            name_mode: NameMode::Lean,
        };
        assert!(view.ty(0, 0).is_err());
        assert_eq!(view.ty(1, 0).unwrap(), json!("float"));
        assert_eq!(view.ty(3, 0).unwrap(), json!("uint8"));
    }

    #[test]
    fn null_parameter_id_is_not_var_zero() {
        let base = 0x1000;
        let mut bytes = vec![0u8; 32];
        bytes[4..6].copy_from_slice(&32u16.to_le_bytes());
        bytes[6] = 2;
        bytes[16..24].copy_from_slice(&1u64.to_le_bytes());
        let observe = |bytes: &[u8]| {
            View {
                regions: vec![("current", base, bytes)],
                budget: Cell::new(100),
                array_limit: 100,
                name_mode: NameMode::Lean,
            }
            .param(base)
        };
        assert!(observe(&bytes).is_err());
        bytes[8..16].copy_from_slice(&1u64.to_le_bytes());
        assert_eq!(observe(&bytes).unwrap(), json!({"x":0,"borrow":false,"ty":"float"}));
        bytes[8..16].copy_from_slice(&3u64.to_le_bytes());
        assert_eq!(observe(&bytes).unwrap()["x"], json!(1));
        bytes[24] = 2;
        assert!(observe(&bytes).is_err());
    }
}

#[cfg(test)]
mod snapshot_controls {
    use super::*;

    fn object(fields: u8) -> Vec<u8> {
        let mut bytes = vec![0; 8 + usize::from(fields) * 8];
        bytes[6] = fields;
        for i in 0..fields {
            let offset = 8 + usize::from(i) * 8;
            bytes[offset..offset + 8].copy_from_slice(&(2 * u64::from(i) + 1).to_le_bytes());
        }
        bytes
    }

    #[test]
    fn checked_snapshot_charges_header_and_each_field_without_free_recursive_reads() {
        let bytes = object(4);
        let view = View {
            regions: vec![("test", 0x1000, &bytes)],
            budget: Cell::new(5),
            array_limit: 100,
            name_mode: NameMode::Lean,
        };
        let header = view.header(0x1000).unwrap();
        let fields = view.checked_fields(0x1000, header, 0, 4).unwrap();
        assert_eq!(fields, [1, 3, 5, 7]);
        assert_eq!(view.budget.get(), 0);
        assert_eq!(fields.get(3), Some(&7));
        assert_eq!(view.header(0x1000).unwrap_err(), "object-access resource bound");
    }

    #[test]
    fn shared_ast_children_still_consume_their_own_traversal_accesses() {
        let mut bytes = object(4);
        bytes[7] = 1; // jdecl: both children point to the same ret node.
        for (index, word) in [1u64, 0x1028, 0x1040, 0x1040].into_iter().enumerate() {
            bytes[8 + index * 8..16 + index * 8].copy_from_slice(&word.to_le_bytes());
        }
        bytes.resize(80, 0);
        bytes[47] = tags::ARRAY; // Empty parameter array at offset 40.
        bytes[70] = 1;
        bytes[71] = 10; // ret at offset 64.
        bytes[72..80].copy_from_slice(&3u64.to_le_bytes()); // erased argument.
        let view = View {
            regions: vec![("test", 0x1000, &bytes)],
            budget: Cell::new(11),
            array_limit: 100,
            name_mode: NameMode::Lean,
        };
        assert_eq!(view.ast(0x1000, 0).unwrap_err(), "object-access resource bound");
        view.budget.set(12);
        let decoded = view.ast(0x1000, 0).unwrap();
        assert_eq!(decoded["args"][2], decoded["args"][3]);
        assert_eq!(view.budget.get(), 0);
    }

    #[test]
    fn checked_snapshot_refuses_malformed_layout_and_truncated_fields() {
        let mut bytes = object(4);
        let view = View {
            regions: vec![("test", 0x1000, &bytes)],
            budget: Cell::new(10),
            array_limit: 100,
            name_mode: NameMode::Lean,
        };
        assert!(view.checked_fields(0x1000, view.header(0x1000).unwrap(), 1, 4).is_err());
        assert_eq!(view.budget.get(), 9);
        drop(view);
        bytes.truncate(bytes.len() - 1);
        let view = View {
            regions: vec![("test", 0x1000, &bytes)],
            budget: Cell::new(10),
            array_limit: 100,
            name_mode: NameMode::Lean,
        };
        assert!(view.checked_fields(0x1000, view.header(0x1000).unwrap(), 0, 4).is_err());
    }
}

/// Retain rows and errors separately: a malformed sibling never discards a
/// decoded declaration, nor can a decoded declaration hide an unmeasured row.
pub(super) struct Observation {
    pub report: Value,
    pub errors: Vec<String>,
}

pub(super) fn observe(
    part: &[u8],
    dependencies: &[&[u8]],
    array_limit: usize,
    accesses: usize,
) -> Observation {
    let mut report = json!({"status":"unmeasured", "authority":"diagnostic-only",
        "rows":[], "extensions":[], "effects_and_lowering":"unmeasured",
        "limits":{"array_rows":array_limit.min(LIMIT),"object_accesses_per_part":accesses,
            "ast_depth":256,"name_components":256,"type_depth":64,"string_bytes":1_048_576,
            "numeric_literal_limbs":literals::MAX_LITERAL_LIMBS},
        "population":"captured part only; external implementations and transitive runtime closure unmeasured"});
    let mut errors = Vec::new();
    let result = (|| -> R<()> {
        let header = OleanHeader::parse(part).map_err(|e| e.to_string())?;
        let mut regions = Vec::new();
        for bytes in dependencies {
            let dependency = OleanHeader::parse(bytes).map_err(|e| e.to_string())?;
            regions.push(("dependency", dependency.base_addr, *bytes));
        }
        regions.push(("current", header.base_addr, part));
        let own = CompactedRegion::new(part, header.base_addr);
        let root = own
            .read_u64_at(if header.version == 1 { HEADER_SIZE } else { HEADER_SIZE_V2 })
            .map_err(|e| e.to_string())?;
        // Only format-independent accesses occur before the captured root
        // selects the Name mode. They consume the same observation budget.
        let mut view = View {
            regions,
            budget: Cell::new(accesses),
            array_limit: array_limit.min(LIMIT),
            name_mode: NameMode::Lean,
        };
        view.name_mode =
            module_mode(&view, root, view.regions.iter().map(|(_, base, bytes)| (*base, *bytes)))?;
        // Pinned Lean ModuleData is tag0, five boxed arrays and an isModule
        // scalar byte. Clean's older exporter writes the same five arrays but
        // cs_sz=0 and no scalar; disclose that distinct diagnostic shape.
        view.layout(root, 0, 5)?;
        report["module_envelope"] = match view.header(root)?.cs_sz {
            56 => {
                json!({"layout":"lean-module-data-five-arrays-bool", "is_module":view.boolean(root,48)?})
            }
            0 => json!({"layout":"clean-legacy-five-arrays-no-scalar", "is_module":"unmeasured"}),
            size => return Err(format!("unknown ModuleData constructor size {size}")),
        };
        let extensions = view.array(view.word(root, 40)?)?;
        let expected = json!([{"kind":"str","value":"Lean"},{"kind":"str","value":"IR"},{"kind":"str","value":"declMapExt"}]);
        let mut extension_rows = Vec::new();
        let mut rows = Vec::new();
        for (extension_index, pointer) in extensions.into_iter().enumerate() {
            let mut extension = json!({"index":extension_index,"status":"unmeasured"});
            let decoded = (|| -> R<()> {
                view.layout(pointer, 0, 2)?;
                let name = view.name(view.word(pointer, 8)?)?;
                extension["name"] = name.clone();
                extension["runtime_ir_extension"] = json!(name == expected);
                // Do not interpret unrelated extension payloads as IR.
                let entries = view.array(view.word(pointer, 16)?)?;
                extension["entry_count"] = json!(entries.len());
                if name == expected {
                    for (index, pointer) in entries.into_iter().enumerate() {
                        let mut row = json!({"extension_index":extension_index,"index":index,
                            "pointer":pointer,"status":"unmeasured"});
                        match view.decl(pointer) {
                            Ok(declaration) => {
                                let bindings = bindings::audit(&declaration);
                                if bindings["status"] != "identifier-bindings-resolved-only" {
                                    errors.push(format!("IR extension {extension_index} row {index}: unresolved identifier bindings"));
                                }
                                row["identifier_bindings"] = bindings;
                                row["declaration"] = declaration;
                                row["status"] = json!("decoded-syntax-only");
                            }
                            Err(error) => {
                                errors.push(format!(
                                    "IR extension {extension_index} row {index}: {error}"
                                ));
                                row["error"] = json!(error);
                                row["raw_reference"] = match view.raw(pointer) {
                                    Ok(raw) => raw,
                                    Err(error) => json!({"error":error}),
                                };
                            }
                        }
                        rows.push(row);
                    }
                }
                extension["status"] = json!("observed-extension-envelope");
                Ok(())
            })();
            if let Err(error) = decoded {
                errors.push(format!("extension {extension_index}: {error}"));
                extension["error"] = json!(error);
            }
            extension_rows.push(extension);
        }
        report["rows"] = json!(rows);
        report["extensions"] = json!(extension_rows);
        report["remaining_object_accesses"] = json!(view.budget.get());
        Ok(())
    })();
    if let Err(error) = result {
        errors.push(error);
    }
    report["status"] = json!(if errors.is_empty() {
        "observed-syntax-only"
    } else {
        "incomplete-syntax-observation"
    });
    report["errors"] = json!(errors);
    Observation { report, errors }
}

fn node(kind: &str, args: Vec<Value>) -> Value {
    json!({"kind":kind,"args":args})
}
struct View<'a> {
    regions: Vec<(&'a str, u64, &'a [u8])>,
    budget: Cell<usize>,
    array_limit: usize,
    name_mode: NameMode,
}
impl NameAccess for View<'_> {
    fn header(&self, pointer: u64) -> R<ObjectHeader> {
        View::header(self, pointer)
    }
    fn word(&self, pointer: u64, relative: usize) -> R<u64> {
        View::word(self, pointer, relative)
    }
    fn bytes(&self, pointer: u64, relative: usize, size: usize) -> R<&[u8]> {
        let (_, offset, bytes, _) = self.at(pointer)?;
        let begin = offset.checked_add(relative).ok_or("Name byte offset overflow")?;
        let end = begin.checked_add(size).ok_or("Name byte range overflow")?;
        bytes.get(begin..end).ok_or_else(|| "Name bytes outside captured region".into())
    }
    fn gmp_bignums(&self, pointer: u64) -> R<bool> {
        let (_, _, bytes, _) = self.at(pointer)?;
        let header = OleanHeader::parse(bytes).map_err(|e| e.to_string())?;
        Ok(header.version == 2 && header.flags == 1)
    }
}
impl View<'_> {
    fn at(&self, p: u64) -> R<(CompactedRegion<'_>, usize, &[u8], &str)> {
        let remaining = self.budget.get().checked_sub(1).ok_or("object-access resource bound")?;
        self.budget.set(remaining);
        if !is_ptr(p) {
            return Err(format!("not a pointer: {p:#x}"));
        }
        let found: Vec<_> = self
            .regions
            .iter()
            .filter(|(_, base, bytes)| {
                base.checked_add(bytes.len() as u64).is_some_and(|end| p >= *base && p < end)
            })
            .collect();
        if found.len() != 1 {
            return Err(format!("pointer {p:#x} resolves to {} regions", found.len()));
        }
        let (name, base, bytes) = found[0];
        let region = CompactedRegion::new(bytes, *base);
        let offset = region.ptr_to_offset(p).map_err(|e| e.to_string())?;
        Ok((region, offset, bytes, name))
    }
    fn word(&self, p: u64, n: usize) -> R<u64> {
        let (r, o, _, _) = self.at(p)?;
        r.read_u64_at(o.checked_add(n).ok_or("word offset overflow")?).map_err(|e| e.to_string())
    }
    fn header(&self, p: u64) -> R<ObjectHeader> {
        let (r, o, _, _) = self.at(p)?;
        let header = r.read_header_at(o).map_err(|e| e.to_string())?;
        if header.rc != 0 {
            return Err("nonzero reference count in compacted object".into());
        }
        Ok(header)
    }
    // A local snapshot avoids rereading the same boxed fields immediately
    // after validating them. It is not an AST/object cache: every recursive
    // decode still resolves its header and charges every captured field read.
    fn checked_fields(&self, p: u64, h: ObjectHeader, tag: u8, fields: u8) -> R<Vec<u64>> {
        if (h.tag, h.other) != (tag, fields) {
            return Err(format!(
                "unexpected layout {} / {}, expected {tag} / {fields}",
                h.tag, h.other
            ));
        }
        (0..fields).map(|i| self.word(p, 8 + usize::from(i) * 8)).collect()
    }
    fn layout(&self, p: u64, tag: u8, fields: u8) -> R<()> {
        self.checked_fields(p, self.header(p)?, tag, fields).map(|_| ())
    }
    fn raw(&self, p: u64) -> R<Value> {
        if !is_ptr(p) {
            return Ok(json!({"representation":"scalar", "word":p}));
        }
        let (r, o, bytes, part) = self.at(p)?;
        let h = r.read_header_at(o).map_err(|e| e.to_string())?;
        let end = o.checked_add(8 + usize::from(h.other) * 8).ok_or("raw object overflow")?;
        let prefix = bytes.get(o..end).ok_or("raw field prefix out of bounds")?;
        Ok(json!({"representation":"object", "part":part, "offset":o, "tag":h.tag,
            "boxed_fields":h.other,"header_size_field":h.cs_sz,"header_and_boxed_field_bytes":prefix,
            "transitive_payload":"retained in complete artifact bytes; NOT decoded by this raw reference"}))
    }
    fn array(&self, p: u64) -> R<Vec<u64>> {
        let h = self.header(p)?;
        // Tag247 is reserved in the pinned runtime, not an established
        // alternate representation of its boxed Array (tag246).
        if h.tag != tags::ARRAY {
            return Err("not array".into());
        }
        let len = usize::try_from(self.word(p, 8)?).map_err(|_| "array length overflow")?;
        let cap = self.word(p, 16)?;
        if len > self.array_limit || len as u64 > cap {
            return Err(format!(
                "array length {len}, capacity {cap}, observation bound {}",
                self.array_limit
            ));
        }
        (0..len).map(|i| self.word(p, 24 + i * 8)).collect()
    }
    fn name(&self, p: u64) -> R<Value> {
        Ok(json!(read_name(self, self.name_mode, p)?))
    }
    fn option_name(&self, p: u64) -> R<Value> {
        if p == 1 {
            return Ok(Value::Null);
        }
        self.layout(p, 1, 1)?;
        self.name(self.word(p, 8)?)
    }
    fn nat(&self, p: u64) -> R<Value> {
        if p == 0 || is_ptr(p) {
            return Err("large Nat / non-scalar index outside bounded representation".into());
        }
        Ok(json!(p >> 1))
    }
    fn boolean(&self, p: u64, offset: usize) -> R<Value> {
        let (_, at, bytes, _) = self.at(p)?;
        Ok(json!(match bytes.get(at.checked_add(offset).ok_or("Bool offset overflow")?) {
            Some(0) => false,
            Some(1) => true,
            _ => return Err("noncanonical Bool scalar".into()),
        }))
    }
    fn string(&self, p: u64) -> R<Value> {
        let (r, at, bytes, _) = self.at(p)?;
        if r.read_header_at(at).map_err(|e| e.to_string())?.tag != tags::STRING {
            return Err("not String".into());
        }
        let len = usize::try_from(self.word(p, 8)?).map_err(|_| "String overflow")?;
        if len > 1_048_576 {
            return Err("String resource bound".into());
        }
        let begin = at.checked_add(32).ok_or("String offset overflow")?;
        let end = begin.checked_add(len).ok_or("String offset overflow")?;
        let raw = bytes
            .get(begin..end)
            .ok_or("String out of region")?
            .strip_suffix(&[0])
            .ok_or("String missing terminator")?;
        Ok(json!(std::str::from_utf8(raw).map_err(|e| e.to_string())?))
    }
    fn arg(&self, p: u64) -> R<Value> {
        if p == 3 {
            return Ok(node("erased", vec![]));
        }
        self.layout(p, 0, 1)?;
        Ok(node("var", vec![self.nat(self.word(p, 8)?)?]))
    }
    fn args(&self, p: u64) -> R<Value> {
        Ok(json!(self.array(p)?.into_iter().map(|a| self.arg(a)).collect::<R<Vec<_>>>()?))
    }
    fn ctor(&self, p: u64) -> R<Value> {
        self.layout(p, 0, 5)?;
        Ok(json!({"name":self.name(self.word(p,8)?)?,
            "cidx":self.nat(self.word(p,16)?)?,"size":self.nat(self.word(p,24)?)?,
            "usize":self.nat(self.word(p,32)?)?,"ssize":self.nat(self.word(p,40)?)?}))
    }
    fn literal(&self, p: u64) -> R<Value> {
        let h = self.header(p)?;
        self.layout(p, h.tag, 1)?;
        match h.tag {
            0 => Ok(node("num", vec![self.literal_nat(self.word(p, 8)?)?])),
            1 => Ok(node("str", vec![self.string(self.word(p, 8)?)?])),
            _ => Err("unknown LitVal variant".into()),
        }
    }
    fn expr(&self, p: u64) -> R<Value> {
        let h = self.header(p)?;
        let fields = match h.tag {
            0 | 1 | 3 | 4 | 6 | 7 | 8 | 9 => 2,
            2 | 5 => 3,
            10 | 11 | 12 => 1,
            _ => return Err("unknown Expr variant".into()),
        };
        let boxed = self.checked_fields(p, h, h.tag, fields)?;
        let w = |i: usize| -> R<u64> {
            boxed.get(i).copied().ok_or_else(|| "boxed field outside checked snapshot".into())
        };
        let n = |i: usize| w(i).and_then(|v| self.nat(v));
        let (kind, args) = match h.tag {
            0 => ("ctor", vec![self.ctor(w(0)?)?, self.args(w(1)?)?]),
            1 => ("reset", vec![n(0)?, n(1)?]),
            2 => ("reuse", vec![n(0)?, self.ctor(w(1)?)?, self.boolean(p, 32)?, self.args(w(2)?)?]),
            3 => ("proj", vec![n(0)?, n(1)?]),
            4 => ("uproj", vec![n(0)?, n(1)?]),
            5 => ("sproj", vec![n(0)?, n(1)?, n(2)?]),
            6 => ("fap", vec![self.name(w(0)?)?, self.args(w(1)?)?]),
            7 => ("pap", vec![self.name(w(0)?)?, self.args(w(1)?)?]),
            8 => ("ap", vec![n(0)?, self.args(w(1)?)?]),
            9 => ("box", vec![self.ty(w(0)?, 0)?, n(1)?]),
            10 => ("unbox", vec![n(0)?]),
            11 => ("lit", vec![self.literal(w(0)?)?]),
            12 => ("isShared", vec![n(0)?]),
            _ => return Err("unknown variant after layout check".into()),
        };
        Ok(node(kind, args))
    }
    fn alt(&self, p: u64, depth: usize) -> R<Value> {
        if depth >= 256 {
            return Err("nested AST depth bound".into());
        }
        let h = self.header(p)?;
        match h.tag {
            0 => {
                self.layout(p, 0, 2)?;
                Ok(node(
                    "ctor",
                    vec![self.ctor(self.word(p, 8)?)?, self.ast(self.word(p, 16)?, depth + 1)?],
                ))
            }
            1 => {
                self.layout(p, 1, 1)?;
                Ok(node("default", vec![self.ast(self.word(p, 8)?, depth + 1)?]))
            }
            _ => Err("unknown Alt variant".into()),
        }
    }
    fn ast(&self, p: u64, depth: usize) -> R<Value> {
        if depth >= 256 {
            return Err("nested AST depth bound".into());
        }
        if p == 25 {
            return Ok(node("unreachable", vec![]));
        }
        let h = self.header(p)?;
        let fields = match h.tag {
            0 | 1 | 2 | 4 | 9 => 4,
            3 | 6 | 7 => 3,
            5 => 6,
            8 | 11 => 2,
            10 => 1,
            _ => return Err("unknown FnBody variant".into()),
        };
        let boxed = self.checked_fields(p, h, h.tag, fields)?;
        let w = |i: usize| -> R<u64> {
            boxed.get(i).copied().ok_or_else(|| "boxed field outside checked snapshot".into())
        };
        let n = |i: usize| w(i).and_then(|v| self.nat(v));
        let b = |i: usize| w(i).and_then(|v| self.ast(v, depth + 1));
        let (kind, args) = match h.tag {
            0 => ("vdecl", vec![n(0)?, self.ty(w(1)?, 0)?, self.expr(w(2)?)?, b(3)?]),
            1 => (
                "jdecl",
                vec![
                    n(0)?,
                    json!(
                        self.array(w(1)?)?
                            .into_iter()
                            .map(|p| self.param(p))
                            .collect::<R<Vec<_>>>()?
                    ),
                    b(2)?,
                    b(3)?,
                ],
            ),
            2 => ("set", vec![n(0)?, n(1)?, self.arg(w(2)?)?, b(3)?]),
            3 => ("setTag", vec![n(0)?, n(1)?, b(2)?]),
            4 => ("uset", vec![n(0)?, n(1)?, n(2)?, b(3)?]),
            5 => ("sset", vec![n(0)?, n(1)?, n(2)?, n(3)?, self.ty(w(4)?, 0)?, b(5)?]),
            6 => ("inc", vec![n(0)?, n(1)?, self.boolean(p, 32)?, self.boolean(p, 33)?, b(2)?]),
            7 => ("dec", vec![n(0)?, n(1)?, self.boolean(p, 32)?, self.boolean(p, 33)?, b(2)?]),
            8 => ("del", vec![n(0)?, b(1)?]),
            9 => (
                "case",
                vec![
                    self.name(w(0)?)?,
                    n(1)?,
                    self.ty(w(2)?, 0)?,
                    json!(
                        self.array(w(3)?)?
                            .into_iter()
                            .map(|p| self.alt(p, depth + 1))
                            .collect::<R<Vec<_>>>()?
                    ),
                ],
            ),
            10 => ("ret", vec![self.arg(w(0)?)?]),
            11 => ("jmp", vec![n(0)?, self.args(w(1)?)?]),
            _ => return Err("unknown variant after layout check".into()),
        };
        Ok(node(kind, args))
    }
    fn extern_attribute(&self, mut p: u64) -> R<Value> {
        let mut entries = Vec::new();
        let mut seen = BTreeSet::new();
        while p != 1 {
            if entries.len() >= self.array_limit || !seen.insert(p) {
                return Err("ExternEntry list cycle/resource bound".into());
            }
            self.layout(p, 1, 2)?;
            let value = self.word(p, 8)?;
            let entry = if value == 7 {
                node("opaque", vec![])
            } else {
                let h = self.header(value)?;
                match h.tag {
                    0 => {
                        self.layout(value, 0, 1)?;
                        node("adhoc", vec![self.name(self.word(value, 8)?)?])
                    }
                    1 | 2 => {
                        self.layout(value, h.tag, 2)?;
                        node(
                            if h.tag == 1 { "inline" } else { "standard" },
                            vec![
                                self.name(self.word(value, 8)?)?,
                                self.string(self.word(value, 16)?)?,
                            ],
                        )
                    }
                    _ => return Err("unknown ExternEntry variant".into()),
                }
            };
            entries.push(entry);
            p = self.word(p, 16)?;
        }
        Ok(json!(entries))
    }
    fn ty(&self, p: u64, depth: usize) -> R<Value> {
        if depth >= 64 {
            return Err("IRType depth bound".into());
        }
        const TYPES: [&str; 14] = [
            "float", "uint8", "uint16", "uint32", "uint64", "usize", "erased", "object", "tobject",
            "float32", "struct", "union", "tagged", "void",
        ];
        if p == 0 {
            return Err("null IRType scalar".into());
        }
        if !is_ptr(p) {
            let tag = usize::try_from(p >> 1).map_err(|_| "IRType scalar overflow")?;
            if tag >= 14 || tag == 10 || tag == 11 {
                return Err(format!("unknown scalar IRType {p}"));
            }
            return Ok(json!(TYPES[tag]));
        }
        let h = self.header(p)?;
        if ![10, 11].contains(&h.tag) || h.other != 2 {
            return Err("unknown IRType object variant".into());
        }
        let n = self.word(p, 8)?;
        let name = if h.tag == 10 { self.option_name(n)? } else { self.name(n)? };
        let types = self
            .array(self.word(p, 16)?)?
            .into_iter()
            .map(|v| self.ty(v, depth + 1))
            .collect::<R<Vec<_>>>()?;
        Ok(json!({"kind":TYPES[h.tag as usize],"name":name,"types":types}))
    }
    fn param(&self, p: u64) -> R<Value> {
        self.layout(p, 0, 2)?;
        let x = self.word(p, 8)?;
        if x == 0 || is_ptr(x) {
            return Err("large or noncanonical VarId Nat unmeasured".into());
        }
        let (_, o, bytes, _) = self.at(p)?;
        let borrow = match bytes.get(o + 24) {
            Some(0) => false,
            Some(1) => true,
            _ => return Err("invalid Param borrow scalar".into()),
        };
        Ok(json!({"x":x>>1,"borrow":borrow,"ty":self.ty(self.word(p,16)?,0)?}))
    }
    fn body(&self, p: u64) -> R<Value> {
        const KINDS: [(&str, u8); 13] = [
            ("vdecl", 4),
            ("jdecl", 4),
            ("set", 4),
            ("setTag", 3),
            ("uset", 4),
            ("sset", 6),
            ("inc", 3),
            ("dec", 3),
            ("del", 2),
            ("case", 4),
            ("ret", 1),
            ("jmp", 2),
            ("unreachable", 0),
        ];
        if p == 25 {
            return Ok(json!("unreachable"));
        }
        let h = self.header(p)?;
        let (kind, fields) =
            *KINDS.get(h.tag as usize).ok_or("unknown top-level FnBody variant")?;
        if h.tag == 12 {
            return Err("noncanonical nullary FnBody representation".into());
        }
        self.layout(p, h.tag, fields)?;
        Ok(json!(kind))
    }
    fn decl(&self, p: u64) -> R<Value> {
        let h = self.header(p)?;
        let expected = match h.tag {
            0 => 5,
            1 => 4,
            _ => return Err(format!("unknown Decl variant {}", h.tag)),
        };
        let boxed = self.checked_fields(p, h, h.tag, expected)?;
        let w = |i: usize| -> R<u64> {
            boxed.get(i).copied().ok_or_else(|| "boxed field outside checked snapshot".into())
        };
        let fields = boxed.iter().copied().map(|p| self.raw(p)).collect::<R<Vec<_>>>()?;
        let params =
            self.array(w(1)?)?.into_iter().map(|p| self.param(p)).collect::<R<Vec<_>>>()?;
        let mut row = json!({"name":self.name(w(0)?)?,"params":params,
            "result_type":self.ty(w(2)?,0)?,"kind":if h.tag==0{"fdecl"}else{"extern"},
            "body_present":h.tag==0,"body_top_kind":null,"sorry_dep":null,
            "all_decl_fields":fields,"nested_body_ast":"decoded-syntax-only","effects_and_lowering":"unmeasured",
            "body_ast":null,"extern_attribute":null});
        if h.tag == 0 {
            row["body_top_kind"] = self.body(w(3)?)?;
            row["sorry_dep"] = self.option_name(w(4)?)?;
            row["body_ast"] = self.ast(w(3)?, 0)?;
        } else {
            row["extern_attribute"] = self.extern_attribute(w(3)?)?;
            row["extern_attribute_semantics"] =
                json!("decoded syntax, external implementation unmeasured");
        }
        Ok(row)
    }
}
