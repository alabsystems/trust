//! Bounded ELF64 metadata for Linux daemon runtime admission.
//!
//! Program headers, rather than section names or `ldd`, identify the dynamic
//! table. This module never executes an input, resolves a SONAME or grants a
//! runtime capability. Callers must bind the real system loader, resolve and
//! hash each dependency, and re-observe the candidate before launch.

use std::io::{Read, Seek, SeekFrom};

const METADATA_LIMIT: usize = 4 * 1024 * 1024;
const STRING_TABLE_LIMIT: usize = 1024 * 1024;
const PROGRAM_HEADER_LIMIT: usize = 1024;
const NEEDED_LIMIT: usize = 256;
const NAME_LIMIT: usize = 4096;
const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_INTERP: u32 = 3;
const PT_PHDR: u32 = 6;

#[derive(Debug, Eq, PartialEq)]
pub(super) struct ElfMetadata {
    pub(super) machine: u16,
    pub(super) interpreter: Option<String>,
    pub(super) needed: Vec<String>,
    pub(super) dynamic: bool,
}

#[derive(Clone, Copy)]
struct Segment {
    kind: u32,
    offset: u64,
    address: u64,
    file_bytes: u64,
    memory_bytes: u64,
}

struct Reader<'a, R> {
    input: &'a mut R,
    file_bytes: u64,
    metadata_bytes: usize,
}

fn bad(message: &str) -> String {
    format!("Linux runtime ELF: {message}")
}

fn extent(offset: u64, bytes: u64) -> Result<u64, String> {
    offset.checked_add(bytes).ok_or_else(|| bad("extent overflow"))
}

impl<R: Read + Seek> Reader<'_, R> {
    fn bytes(&mut self, offset: u64, bytes: usize) -> Result<Vec<u8>, String> {
        if extent(offset, bytes as u64)? > self.file_bytes {
            return Err(bad("metadata extends beyond the exact file"));
        }
        self.metadata_bytes = self
            .metadata_bytes
            .checked_add(bytes)
            .filter(|&count| count <= METADATA_LIMIT)
            .ok_or_else(|| bad("metadata read limit exceeded"))?;
        let mut output = Vec::new();
        output.try_reserve_exact(bytes).map_err(|error| bad(&format!("allocation: {error}")))?;
        output.resize(bytes, 0);
        self.input.seek(SeekFrom::Start(offset)).map_err(|error| bad(&error.to_string()))?;
        self.input.read_exact(&mut output).map_err(|error| bad(&error.to_string()))?;
        Ok(output)
    }
}

fn u16_at(bytes: &[u8], offset: usize) -> Result<u16, String> {
    let field = bytes.get(offset..offset + 2).ok_or_else(|| bad("truncated u16 field"))?;
    Ok(u16::from_le_bytes([field[0], field[1]]))
}

fn u32_at(bytes: &[u8], offset: usize) -> Result<u32, String> {
    let field = bytes.get(offset..offset + 4).ok_or_else(|| bad("truncated u32 field"))?;
    Ok(u32::from_le_bytes([field[0], field[1], field[2], field[3]]))
}

fn u64_at(bytes: &[u8], offset: usize) -> Result<u64, String> {
    let field = bytes.get(offset..offset + 8).ok_or_else(|| bad("truncated u64 field"))?;
    let mut value = [0; 8];
    value.copy_from_slice(field);
    Ok(u64::from_le_bytes(value))
}

fn single_segment(segments: &[Segment], kind: u32) -> Result<Option<Segment>, String> {
    let mut found = None;
    for segment in segments.iter().filter(|segment| segment.kind == kind) {
        if found.replace(*segment).is_some() {
            return Err(bad("duplicate interpreter, dynamic or program-header segment"));
        }
    }
    Ok(found)
}

fn file_mapping(segments: &[Segment], address: u64, bytes: u64) -> Result<u64, String> {
    let end = extent(address, bytes)?;
    let mut result = None;
    for segment in segments.iter().filter(|segment| segment.kind == PT_LOAD) {
        if segment.address <= address && end <= extent(segment.address, segment.file_bytes)? {
            let offset = extent(segment.offset, address - segment.address)?;
            if result.replace(offset).is_some() {
                return Err(bad("metadata has ambiguous file-backed load mappings"));
            }
        }
    }
    result.ok_or_else(|| bad("metadata has no complete file-backed load mapping"))
}

/// GNU maps and zero-fills whole host pages, not just declared byte ranges:
/// https://sourceware.org/git/?p=glibc.git;a=blob;f=elf/dl-map-segments.h;hb=glibc-2.39
/// Reject overlapping layouts instead of guessing which metadata bytes win.
/// This includes partial file aliases, BSS and different maps sharing a page.
fn validate_load_mappings(segments: &[Segment], page_bytes: u64) -> Result<(), String> {
    if !matches!(page_bytes, 4096 | 16384 | 65536) {
        return Err(bad("unsupported host base page size"));
    }
    let mask = page_bytes - 1;
    let mut previous_end = None;
    for segment in segments.iter().filter(|segment| segment.kind == PT_LOAD) {
        if (segment.address & mask) != (segment.offset & mask) {
            return Err(bad("load mapping disagrees with the host page alignment"));
        }
        let start = segment.address & !mask;
        let raw_end = extent(segment.address, segment.memory_bytes)?;
        let end = extent(raw_end, mask)? & !mask;
        if previous_end.is_some_and(|previous| start < previous) {
            return Err(bad("overlapping or out-of-order page-rounded load mappings"));
        }
        previous_end = Some(end);
    }
    Ok(())
}

pub(super) fn host_page_bytes() -> Result<u64, String> {
    // SAFETY: sysconf with the defined _SC_PAGESIZE selector only queries the
    // process's host page size; it takes no pointer and has no caller invariants.
    let page_bytes = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    u64::try_from(page_bytes)
        .ok()
        .filter(|&value| matches!(value, 4096 | 16384 | 65536))
        .ok_or_else(|| bad("host page size is unavailable or unsupported"))
}

fn read_segments<R: Read + Seek>(
    reader: &mut Reader<'_, R>,
    header: &[u8],
) -> Result<Vec<Segment>, String> {
    let offset = u64_at(header, 32)?;
    let count = usize::from(u16_at(header, 56)?);
    if offset < 64 || u16_at(header, 54)? != 56 || count == 0 || count > PROGRAM_HEADER_LIMIT {
        return Err(bad("unsupported or unbounded program header table"));
    }
    let table = reader.bytes(offset, count * 56)?;
    let mut segments = Vec::new();
    segments.try_reserve_exact(count).map_err(|error| bad(&error.to_string()))?;
    for row in table.chunks_exact(56) {
        let segment = Segment {
            kind: u32_at(row, 0)?,
            offset: u64_at(row, 8)?,
            address: u64_at(row, 16)?,
            file_bytes: u64_at(row, 32)?,
            memory_bytes: u64_at(row, 40)?,
        };
        if extent(segment.offset, segment.file_bytes)? > reader.file_bytes {
            return Err(bad("program header has an out-of-file extent"));
        }
        if matches!(segment.kind, PT_LOAD | PT_DYNAMIC | PT_INTERP | PT_PHDR) {
            if segment.file_bytes > segment.memory_bytes {
                return Err(bad("file-backed segment exceeds its memory extent"));
            }
            extent(segment.address, segment.memory_bytes)?;
            let alignment = u64_at(row, 48)?;
            if alignment > 1
                && (!alignment.is_power_of_two()
                    || segment.address % alignment != segment.offset % alignment)
            {
                return Err(bad("segment alignment does not bind its file mapping"));
            }
        }
        segments.push(segment);
    }
    if !segments.iter().any(|segment| segment.kind == PT_LOAD) {
        return Err(bad("executable has no loadable segment"));
    }
    Ok(segments)
}

/// Normal Linux exec supplies the mapped file table through AT_PHDR, whereas
/// GNU's direct loader takes l_phdr from PT_PHDR when it exists. Both must
/// identify the exact same complete file-backed array before either runtime
/// can derive load bias or choose dynamic metadata from it.
/// Linux 6.8 fs/binfmt_elf.c and GNU 2.39 elf/{dl-load,rtld}.c define these paths.
fn validate_program_headers(segments: &[Segment], header: &[u8]) -> Result<(), String> {
    let offset = u64_at(header, 32)?;
    let bytes = u64::from(u16_at(header, 56)?) * 56;
    let end = extent(offset, bytes)?;
    let mut address = None;
    // Linux chooses from every LOAD containing the START of e_phoff. Requiring
    // only one complete mapping would miss a later partial competing mapping.
    for segment in segments.iter().filter(|segment| segment.kind == PT_LOAD) {
        let file_end = extent(segment.offset, segment.file_bytes)?;
        if segment.offset <= offset && offset < file_end {
            if end > file_end {
                return Err(bad("program header table is only partially file-backed"));
            }
            let mapped = extent(segment.address, offset - segment.offset)?;
            if address.replace(mapped).is_some() {
                return Err(bad("program header table has multiple runtime file mappings"));
            }
        }
    }
    let address =
        address.ok_or_else(|| bad("program header table has no complete runtime file mapping"))?;
    if file_mapping(segments, address, bytes)? != offset {
        return Err(bad("program header table file and runtime bytes disagree"));
    }
    let phdr = single_segment(segments, PT_PHDR)?;
    if let Some(phdr) = phdr {
        if phdr.offset != offset
            || phdr.address != address
            || phdr.file_bytes != bytes
            || phdr.memory_bytes != bytes
        {
            return Err(bad("PT_PHDR does not bind the exact mapped program header table"));
        }
        // GNU scans in order and uses the current bias for DYNAMIC and INTERP.
        // The ABI places PHDR before LOAD; also reject earlier bias consumers.
        let mut seen = false;
        for segment in segments {
            if segment.kind == PT_PHDR {
                seen = true;
            }
            if !seen && matches!(segment.kind, PT_LOAD | PT_DYNAMIC | PT_INTERP) {
                return Err(bad("PT_PHDR follows a load-bias consumer"));
            }
        }
    } else if u16_at(header, 16)? == 3 && segments.iter().any(|segment| segment.kind == PT_INTERP) {
        // An ET_EXEC has zero bias; a DSO is mapped by GNU itself. A PIE main
        // executable instead needs PHDR to derive its kernel-provided bias.
        return Err(bad("PIE candidate has no explicit matching PT_PHDR load-bias binding"));
    }
    Ok(())
}

fn interpreter<R: Read + Seek>(
    reader: &mut Reader<'_, R>,
    segments: &[Segment],
    segment: Option<Segment>,
) -> Result<Option<String>, String> {
    let Some(segment) = segment else { return Ok(None) };
    let bytes =
        usize::try_from(segment.file_bytes).map_err(|_| bad("interpreter length overflow"))?;
    if !(2..=NAME_LIMIT).contains(&bytes) {
        return Err(bad("interpreter length is outside the bound"));
    }
    // Linux reads the named interpreter at p_offset; GNU's main-map alias uses
    // load_bias + p_vaddr. Bind the entire terminated string to the same file
    // bytes before either path can contribute runtime interpreter authority.
    if file_mapping(segments, segment.address, segment.file_bytes)? != segment.offset {
        return Err(bad("interpreter file and virtual mappings disagree"));
    }
    let bytes = reader.bytes(segment.offset, bytes)?;
    if bytes.last() != Some(&0) || bytes[..bytes.len() - 1].contains(&0) {
        return Err(bad("interpreter is not exactly one terminated path"));
    }
    let value = std::str::from_utf8(&bytes[..bytes.len() - 1])
        .map_err(|_| bad("interpreter path is not UTF-8"))?;
    if !value.starts_with('/')
        || value.contains("//")
        || value.chars().any(char::is_control)
        || value.split('/').skip(1).any(|part| part.is_empty() || part == "." || part == "..")
    {
        return Err(bad("interpreter is not an absolute normalized path"));
    }
    Ok(Some(value.to_owned()))
}

pub(super) fn valid_soname(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= NAME_LIMIT
        && name != "."
        && name != ".."
        && name.bytes().all(|byte| byte.is_ascii_alphanumeric() || b"._+-".contains(&byte))
}

fn dynamic_needed<R: Read + Seek>(
    reader: &mut Reader<'_, R>,
    segments: &[Segment],
    dynamic: Segment,
) -> Result<Vec<String>, String> {
    if dynamic.file_bytes == 0 || dynamic.file_bytes % 16 != 0 {
        return Err(bad("empty or partial dynamic table"));
    }
    if file_mapping(segments, dynamic.address, dynamic.file_bytes)? != dynamic.offset {
        return Err(bad("dynamic table file and virtual mappings disagree"));
    }
    let count =
        usize::try_from(dynamic.file_bytes).map_err(|_| bad("dynamic table length overflow"))?;
    let table = reader.bytes(dynamic.offset, count)?;
    let mut strings = None;
    let mut string_bytes = None;
    let mut needed = Vec::new();
    let mut terminated = false;
    for row in table.chunks_exact(16) {
        let tag = u64_at(row, 0)?;
        let value = u64_at(row, 8)?;
        if terminated {
            if tag != 0 || value != 0 {
                return Err(bad("nonzero metadata follows the dynamic terminator"));
            }
            continue;
        }
        match tag {
            0 => terminated = true,
            1 => {
                if needed.len() == NEEDED_LIMIT {
                    return Err(bad("dependency count exceeds the bound"));
                }
                needed.push(value);
            }
            5 => {
                if strings.replace(value).is_some() {
                    return Err(bad("duplicate string table"));
                }
            }
            10 => {
                if string_bytes.replace(value).is_some() {
                    return Err(bad("duplicate string extent"));
                }
            }
            // RPATH, RUNPATH, CONFIG, DEPAUDIT, AUDIT, AUXILIARY, FILTER.
            15 | 29 | 0x6fff_fefa | 0x6fff_fefb | 0x6fff_fefc | 0x7fff_fffd | 0x7fff_ffff => {
                return Err(bad("embedded search, configuration, audit or filter authority"));
            }
            _ => {}
        }
    }
    if !terminated {
        return Err(bad("unterminated dynamic table"));
    }
    match (strings, string_bytes) {
        (None, None) if needed.is_empty() => return Ok(Vec::new()),
        (Some(_), Some(_)) => {}
        _ => return Err(bad("incomplete dynamic string table binding")),
    }
    let address = strings.ok_or_else(|| bad("missing string table"))?;
    let bytes = string_bytes.ok_or_else(|| bad("missing string extent"))?;
    if bytes == 0 || bytes > STRING_TABLE_LIMIT as u64 {
        return Err(bad("dynamic string extent exceeds the bound"));
    }
    let offset = file_mapping(segments, address, bytes)?;
    let table = reader.bytes(offset, bytes as usize)?;
    let mut names = Vec::new();
    for index in needed {
        let index = usize::try_from(index).map_err(|_| bad("dependency name offset overflow"))?;
        let tail =
            table.get(index..).ok_or_else(|| bad("dependency name offset is outside the table"))?;
        let end = tail
            .iter()
            .take(NAME_LIMIT + 1)
            .position(|&byte| byte == 0)
            .ok_or_else(|| bad("dependency name is not terminated within the bound"))?;
        let name = std::str::from_utf8(&tail[..end]).map_err(|_| bad("dependency is not ASCII"))?;
        if !valid_soname(name) || names.iter().any(|existing| existing == name) {
            return Err(bad("dependency is duplicate or is not a bare SONAME"));
        }
        names.push(name.to_owned());
    }
    Ok(names)
}

pub(super) fn inspect<R: Read + Seek>(
    input: &mut R,
    file_bytes: u64,
    expected_machine: u16,
    page_bytes: u64,
) -> Result<ElfMetadata, String> {
    if !matches!(expected_machine, 62 | 183) {
        return Err(bad("host machine is unsupported"));
    }
    let mut reader = Reader { input, file_bytes, metadata_bytes: 0 };
    let header = reader.bytes(0, 64)?;
    if header[..7] != *b"\x7fELF\x02\x01\x01"
        || !matches!(header[7], 0 | 3)
        || header[8..16].iter().any(|&byte| byte != 0)
        || !matches!(u16_at(&header, 16)?, 2 | 3)
        || u32_at(&header, 20)? != 1
        || u32_at(&header, 48)? != 0
        || u16_at(&header, 52)? != 64
    {
        return Err(bad("unsupported ELF64 little-endian executable header"));
    }
    let machine = u16_at(&header, 18)?;
    if machine != expected_machine {
        return Err(bad("native machine mismatch"));
    }
    let segments = read_segments(&mut reader, &header)?;
    validate_load_mappings(&segments, page_bytes)?;
    validate_program_headers(&segments, &header)?;
    let interpreter = interpreter(&mut reader, &segments, single_segment(&segments, PT_INTERP)?)?;
    let dynamic = single_segment(&segments, PT_DYNAMIC)?;
    let needed = match dynamic {
        Some(dynamic) => dynamic_needed(&mut reader, &segments, dynamic)?,
        None => Vec::new(),
    };
    if interpreter.is_some() && dynamic.is_none() {
        return Err(bad("interpreter is present without a dynamic table"));
    }
    Ok(ElfMetadata { machine, interpreter, needed, dynamic: dynamic.is_some() })
}

#[cfg(test)]
#[path = "linux_elf_tests.rs"]
mod tests;
