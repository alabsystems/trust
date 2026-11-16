//! Read-only identity witnesses, not a second expression parser or a loader.
//!
//! Clean's current ParsedModule renders Name.str/Name.num into dotted strings.
//! That loses quoted-dot and numeric-string distinctions. This bounded walker
//! uses its checked region accessors and retains the original Name constructors.
//! Full expressions remain the existing Clean parser's responsibility. A future
//! public typed-name API should replace this adapter, not broaden its authority.

use std::collections::BTreeSet;

use clean_olean::header::{HEADER_SIZE, HEADER_SIZE_V2, OleanHeader};
use clean_olean::region::{CompactedRegion, ObjectHeader, is_ptr, tags};
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "kebab-case")]
pub enum Segment {
    Str(String),
    Num(u64),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ModuleName(pub Vec<Segment>);

impl ModuleName {
    pub fn projection(&self) -> String {
        self.0
            .iter()
            .map(|part| match part {
                Segment::Str(value) => value.clone(),
                Segment::Num(value) => value.to_string(),
            })
            .collect::<Vec<_>>()
            .join(".")
    }
}

/// Format is selected from the enclosing ModuleData, never by falling back
/// from a malformed modern Name object to a legacy interpretation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NameMode {
    Lean,
    CleanLegacy,
}

impl NameMode {
    pub(super) fn from_module_header(header: ObjectHeader) -> Result<Self, String> {
        if (header.rc, header.tag, header.other) != (0, 0, 5) {
            return Err("unsupported ModuleData tag/fields/reference count".into());
        }
        match header.cs_sz {
            56 => Ok(Self::Lean),
            0 => Ok(Self::CleanLegacy),
            size => Err(format!("unknown ModuleData constructor size {size}")),
        }
    }
}

/// Each caller retains its own checked region resolution and access budget.
/// In particular, IR observation must not bypass its budget through this reader.
pub(super) trait NameAccess {
    fn header(&self, pointer: u64) -> Result<ObjectHeader, String>;
    fn word(&self, pointer: u64, relative: usize) -> Result<u64, String>;
    fn bytes(&self, pointer: u64, relative: usize, size: usize) -> Result<&[u8], String>;
    fn gmp_bignums(&self, pointer: u64) -> Result<bool, String>;
}

/// Select the format from one whole captured ModuleData object. A companion
/// may borrow a prior root; its physical rows still belong to the current part.
/// Header and extent reads use the caller's accessor, including IR's budget.
pub(super) fn module_mode<'a>(
    access: &impl NameAccess,
    root: u64,
    regions: impl IntoIterator<Item = (u64, &'a [u8])>,
) -> Result<NameMode, String> {
    if !is_ptr(root) || root % 8 != 0 {
        return Err("invalid or unaligned ModuleData root pointer".into());
    }
    let regions = regions
        .into_iter()
        .map(|(base, bytes)| {
            let end = base.checked_add(bytes.len() as u64).ok_or("region address overflow")?;
            Ok((base, end, bytes))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let owners: Vec<_> =
        regions.iter().filter(|(base, end, _)| root >= *base && root < *end).collect();
    if owners.len() != 1 {
        return Err(format!("ModuleData root has {} captured owners", owners.len()));
    }
    let (base, end, bytes) = *owners[0];
    let owner_header = OleanHeader::parse(bytes).map_err(|e| e.to_string())?;
    let header_size = if owner_header.version == 1 { HEADER_SIZE } else { HEADER_SIZE_V2 };
    let objects = base.checked_add((header_size + 8) as u64).ok_or("object start overflow")?;
    if root < objects {
        return Err("ModuleData root is in a captured header or root-pointer slot".into());
    }
    let mode = NameMode::from_module_header(access.header(root)?)?;
    let extent = if mode == NameMode::Lean { 56 } else { 48 };
    let root_end = root.checked_add(extent).ok_or("ModuleData extent overflow")?;
    if root_end > end {
        return Err("ModuleData extends beyond its captured owner".into());
    }
    if regions.iter().filter(|(base, end, _)| *base < root_end && *end > root).count() != 1 {
        return Err("ModuleData extent overlaps captured regions".into());
    }
    let bytes = access.bytes(root, 0, extent as usize)?;
    if mode == NameMode::Lean && !matches!(bytes[48], 0 | 1) {
        return Err("noncanonical ModuleData isModule Boolean".into());
    }
    Ok(mode)
}

fn name_nat(access: &impl NameAccess, word: u64) -> Result<u64, String> {
    if word & 1 == 1 {
        return Ok(word >> 1);
    }
    if !access.gmp_bignums(word)? {
        return Err("heap Name.num Nat requires a captured v2 region with known GMP flags".into());
    }
    // The pinned Lean runtime compacts an MPZ into an inline limb array.
    // This deliberately does not use the legacy parser's low-limb projection.
    let header = access.header(word)?;
    if (header.rc, header.tag, header.other) != (0, 250, 0) {
        return Err("Name.num Nat is neither a tagged scalar nor a supported MPZ".into());
    }
    let counts = access.bytes(word, 8, 8)?;
    let allocated = i32::from_le_bytes(counts[..4].try_into().unwrap());
    let size = i32::from_le_bytes(counts[4..].try_into().unwrap());
    if size > 1 {
        return Err("Name.num Nat exceeds the u64 typed-name representation".into());
    }
    if header.cs_sz != 32 || allocated != 1 || size != 1 {
        return Err("unsupported/noncanonical Name.num MPZ layout or sign".into());
    }
    if access.word(word, 16)? != word.checked_add(24).ok_or("MPZ limb pointer overflow")? {
        return Err("Name.num MPZ limbs are not the captured inline payload".into());
    }
    let value = access.word(word, 24)?;
    if value <= u64::MAX >> 1 {
        return Err("noncanonical heap Name.num Nat fits a tagged scalar".into());
    }
    Ok(value)
}

pub(super) fn read_name(
    access: &impl NameAccess,
    mode: NameMode,
    mut pointer: u64,
) -> Result<ModuleName, String> {
    let mut seen = BTreeSet::new();
    let mut parts = Vec::new();
    while pointer != 1 {
        if !seen.insert(pointer) {
            return Err("Name cycle or 256-component bound".into());
        }
        let header = access.header(pointer)?;
        if mode == NameMode::CleanLegacy
            && (header.rc, header.tag, header.other, header.cs_sz) == (0, 0, 0, 0)
        {
            break;
        }
        if parts.len() >= 256 {
            return Err("Name cycle or 256-component bound".into());
        }
        let size = if mode == NameMode::Lean { 32 } else { 0 };
        if header.rc != 0 || header.other != 2 || header.cs_sz != size {
            return Err("unsupported typed Name layout for the ModuleData format".into());
        }
        // Validate the whole modern constructor, including its retained hash
        // scalar. The hash is not used to establish identity.
        if mode == NameMode::Lean {
            access.word(pointer, 24)?;
        }
        let value = access.word(pointer, 16)?;
        match header.tag {
            1 => {
                let string = access.header(value)?;
                if (string.rc, string.tag, string.other) != (0, tags::STRING, 0) {
                    return Err("Name.str component is not a captured String".into());
                }
                let size = usize::try_from(access.word(value, 8)?)
                    .map_err(|_| "Name string size overflow")?;
                if size == 0 || size > 1_048_576 {
                    return Err("Name string byte bound".into());
                }
                let capacity = access.word(value, 16)?;
                if size as u64 > capacity {
                    return Err("Name string size exceeds capacity".into());
                }
                let raw = access
                    .bytes(value, 32, size)?
                    .strip_suffix(&[0])
                    .ok_or("Name string has no null terminator")?;
                let text = std::str::from_utf8(raw).map_err(|e| e.to_string())?;
                if access.word(value, 24)? != text.chars().count() as u64 {
                    return Err("Name string character count disagrees with UTF-8 payload".into());
                }
                parts.push(Segment::Str(text.into()));
            }
            2 => parts.push(Segment::Num(match mode {
                NameMode::Lean => name_nat(access, value)?,
                NameMode::CleanLegacy => value,
            })),
            tag => return Err(format!("unsupported Name constructor tag {tag}")),
        }
        pointer = access.word(pointer, 8)?;
    }
    parts.reverse();
    Ok(ModuleName(parts))
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "layout", rename_all = "kebab-case")]
pub enum ImportFlags {
    Lean { import_all: bool, is_exported: bool, is_meta: bool },
    CleanLegacy { runtime_only: bool },
}

#[derive(Clone, Debug, Serialize)]
pub struct NameRow {
    pub index: usize,
    pub name: Option<ModuleName>,
    pub error: Option<String>,
    pub constant_tag: Option<u8>,
    pub runtime_only: Option<bool>,
    pub import_flags: Option<ImportFlags>,
}

impl NameRow {
    /// Clean's existing ParsedImport calls the first scalar `runtime_only`
    /// even for modern Lean bytes. Compare that lossy projection as a byte
    /// witness, not as an assertion about modern import semantics.
    pub fn parser_first_flag_projection(&self) -> Option<bool> {
        self.import_flags.as_ref().map(|flags| match flags {
            ImportFlags::Lean { import_all, .. } => *import_all,
            ImportFlags::CleanLegacy { runtime_only } => *runtime_only,
        })
    }
}

#[derive(Default, Debug, Serialize)]
pub struct Witness {
    pub imports: Vec<NameRow>,
    pub const_names: Vec<NameRow>,
    pub constants: Vec<NameRow>,
    pub extra_const_names: Vec<NameRow>,
    pub errors: Vec<String>,
}

struct View<'a> {
    regions: Vec<(u64, &'a [u8])>,
    max_rows: usize,
    mode: NameMode,
}

impl NameAccess for View<'_> {
    fn header(&self, pointer: u64) -> Result<ObjectHeader, String> {
        let (region, offset, _) = self.locate(pointer)?;
        region.read_header_at(offset).map_err(|e| e.to_string())
    }
    fn word(&self, pointer: u64, relative: usize) -> Result<u64, String> {
        View::word(self, pointer, relative)
    }
    fn bytes(&self, pointer: u64, relative: usize, size: usize) -> Result<&[u8], String> {
        let (_, offset, bytes) = self.locate(pointer)?;
        let begin = offset.checked_add(relative).ok_or("byte offset overflow")?;
        let end = begin.checked_add(size).ok_or("byte range overflow")?;
        bytes.get(begin..end).ok_or_else(|| "bytes outside captured region".into())
    }
    fn gmp_bignums(&self, pointer: u64) -> Result<bool, String> {
        let (_, _, bytes) = self.locate(pointer)?;
        let header = OleanHeader::parse(bytes).map_err(|e| e.to_string())?;
        Ok(header.version == 2 && header.flags == 1)
    }
}

impl View<'_> {
    fn locate(&self, pointer: u64) -> Result<(CompactedRegion<'_>, usize, &[u8]), String> {
        if !is_ptr(pointer) {
            return Err(format!("expected object pointer, got {pointer:#x}"));
        }
        let matches: Vec<_> = self
            .regions
            .iter()
            .filter(|(base, bytes)| {
                base.checked_add(bytes.len() as u64)
                    .is_some_and(|end| pointer >= *base && pointer < end)
            })
            .collect();
        if matches.len() != 1 {
            return Err(format!("pointer {pointer:#x} has {} regions", matches.len()));
        }
        let (base, bytes) = matches[0];
        let region = CompactedRegion::new(bytes, *base);
        let offset = region.ptr_to_offset(pointer).map_err(|e| e.to_string())?;
        Ok((region, offset, bytes))
    }

    fn word(&self, object: u64, relative: usize) -> Result<u64, String> {
        let (region, offset, _) = self.locate(object)?;
        let at = offset.checked_add(relative).ok_or("field offset overflow")?;
        region.read_u64_at(at).map_err(|e| e.to_string())
    }

    fn name(&self, pointer: u64) -> Result<ModuleName, String> {
        read_name(self, self.mode, pointer)
    }

    fn array(&self, pointer: u64) -> Result<Vec<u64>, String> {
        let (region, offset, bytes) = self.locate(pointer)?;
        let header = region.read_header_at(offset).map_err(|e| e.to_string())?;
        if (header.rc, header.tag, header.other) != (0, tags::ARRAY, 0) {
            return Err("expected captured object-array header".into());
        }
        let size = usize::try_from(self.word(pointer, 8)?).map_err(|_| "array size overflow")?;
        if size as u64 > self.word(pointer, 16)? {
            return Err("array size exceeds capacity".into());
        }
        if size > self.max_rows {
            return Err(format!("array size {size} exceeds row bound {}", self.max_rows));
        }
        let count_bytes = size.checked_mul(8).ok_or("array multiplication overflow")?;
        let end = offset
            .checked_add(24)
            .and_then(|n| n.checked_add(count_bytes))
            .ok_or("array end overflow")?;
        if end > bytes.len() {
            return Err("array outside captured region".into());
        }
        (0..size).map(|i| self.word(pointer, 24 + i * 8)).collect()
    }

    fn row(&self, index: usize, pointer: u64, field: usize) -> NameRow {
        let mut row = NameRow {
            index,
            name: None,
            error: None,
            constant_tag: None,
            runtime_only: None,
            import_flags: None,
        };
        let result = (|| {
            let name_pointer = match field {
                0 => {
                    let (region, offset, bytes) = self.locate(pointer)?;
                    let header = region.read_header_at(offset).map_err(|e| e.to_string())?;
                    let expected_size = if self.mode == NameMode::Lean { 24 } else { 0 };
                    if (header.rc, header.tag, header.other, header.cs_sz)
                        != (0, 0, 1, expected_size)
                    {
                        return Err("unsupported Import layout for the ModuleData format".into());
                    }
                    let at = offset
                        .checked_add(8 + usize::from(header.other) * 8)
                        .ok_or("import flag offset overflow")?;
                    let flag = |index: usize| match bytes.get(at + index) {
                        Some(0) => Ok(false),
                        Some(1) => Ok(true),
                        _ => Err("missing/noncanonical Import Boolean scalar".to_string()),
                    };
                    row.import_flags = Some(match self.mode {
                        NameMode::Lean => ImportFlags::Lean {
                            import_all: flag(0)?,
                            is_exported: flag(1)?,
                            is_meta: flag(2)?,
                        },
                        NameMode::CleanLegacy => {
                            let runtime_only = flag(0)?;
                            row.runtime_only = Some(runtime_only);
                            ImportFlags::CleanLegacy { runtime_only }
                        }
                    });
                    self.word(pointer, 8)?
                }
                2 => {
                    let (region, offset, _) = self.locate(pointer)?;
                    let tag = region.read_header_at(offset).map_err(|e| e.to_string())?.tag;
                    row.constant_tag = Some(tag);
                    if tag > 7 {
                        return Err(format!("unsupported ConstantInfo tag {tag}"));
                    }
                    let val = self.word(pointer, 8)?;
                    let cv = self.word(val, 8)?;
                    if is_ptr(cv) { self.word(cv, 8)? } else { cv }
                }
                _ => pointer,
            };
            self.name(name_pointer)
        })();
        match result {
            Ok(name) => row.name = Some(name),
            Err(error) => row.error = Some(error),
        }
        row
    }
}

pub fn witness(part: &[u8], dependencies: &[&[u8]], max_rows: usize) -> Witness {
    let mut result = Witness::default();
    let inspected = (|| -> Result<(), String> {
        let header = OleanHeader::parse(part).map_err(|e| e.to_string())?;
        let mut regions = Vec::new();
        for bytes in dependencies.iter().copied().chain(std::iter::once(part)) {
            let header = OleanHeader::parse(bytes).map_err(|e| e.to_string())?;
            header.base_addr.checked_add(bytes.len() as u64).ok_or("region address overflow")?;
            regions.push((header.base_addr, bytes));
        }
        let own = CompactedRegion::new(part, header.base_addr);
        let header_size = if header.version == 1 { HEADER_SIZE } else { HEADER_SIZE_V2 };
        let root = own.read_u64_at(header_size).map_err(|e| e.to_string())?;
        // Header/byte access is format-independent; no Name is read before
        // selecting the mode from the uniquely owned complete root object.
        let mut view = View { regions, max_rows, mode: NameMode::Lean };
        view.mode = module_mode(&view, root, view.regions.iter().copied())?;
        for field in 0..4 {
            match view.word(root, 8 + field * 8).and_then(|pointer| view.array(pointer)) {
                Ok(pointers) => {
                    let rows = pointers
                        .into_iter()
                        .enumerate()
                        .map(|(i, p)| view.row(i, p, field))
                        .collect();
                    match field {
                        0 => result.imports = rows,
                        1 => result.const_names = rows,
                        2 => result.constants = rows,
                        _ => result.extra_const_names = rows,
                    }
                }
                Err(error) => result.errors.push(format!("module field {field}: {error}")),
            }
        }
        Ok(())
    })();
    if let Err(error) = inspected {
        result.errors.push(error);
    }
    result
}

#[cfg(test)]
mod tests;
