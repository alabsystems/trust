//! A conservative raw GNU cache reader, not a resolver.
//!
//! Format source: GNU glibc 2.39 sysdeps/generic/dl-cache.h and
//! elf/dl-cache.c (https://sourceware.org/git/?p=glibc.git;a=tree;hb=glibc-2.39).
//! All entries are kept regardless of architecture flags or hwcap priority.
//! Old/combined caches and unknown extensions refuse instead of becoming an
//! incomplete inventory. No native `ldconfig` or `ldd` is executed.

use std::collections::BTreeSet;

use super::super::linux_elf;
use super::CacheEntry;

pub(super) const MAX_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_ENTRIES: usize = 16_384;
const MAX_STRINGS: usize = 4 * 1024 * 1024;
const HEADER: usize = 48;
const ENTRY: usize = 24;
const EXTENSION_MAGIC: u32 = 0xeaa4_2174;

fn word(bytes: &[u8], at: usize) -> Result<u32, String> {
    let row = bytes.get(at..at + 4).ok_or("GNU cache truncated word")?;
    Ok(u32::from_le_bytes([row[0], row[1], row[2], row[3]]))
}

fn wide(bytes: &[u8], at: usize) -> Result<u64, String> {
    let row = bytes.get(at..at + 8).ok_or("GNU cache truncated wide word")?;
    let mut value = [0; 8];
    value.copy_from_slice(row);
    Ok(u64::from_le_bytes(value))
}

fn text(bytes: &[u8], at: usize, first: usize, end: usize) -> Result<String, String> {
    if at < first || at >= end {
        return Err("GNU cache string is outside its declared table".into());
    }
    let tail = bytes.get(at..end).ok_or("GNU cache string extent is invalid")?;
    let count = tail
        .iter()
        .take(4097)
        .position(|&byte| byte == 0)
        .ok_or("GNU cache string is not terminated within its bound")?;
    std::str::from_utf8(&tail[..count])
        .map(str::to_owned)
        .map_err(|_| "GNU cache string is not UTF-8".into())
}

fn extensions(bytes: &[u8], first: usize, end: usize) -> Result<usize, String> {
    let at = word(bytes, 32)? as usize;
    if at == 0 {
        if bytes.len() != end {
            return Err("GNU cache has unbound trailing bytes".into());
        }
        return Ok(0);
    }
    if at < end
        || at % 4 != 0
        || bytes.get(end..at).is_none_or(|gap| gap.iter().any(|&b| b != 0))
        || word(bytes, at)? != EXTENSION_MAGIC
    {
        return Err("GNU cache has an invalid extension directory".into());
    }
    let count = word(bytes, at + 4)? as usize;
    if count > 2 {
        return Err("GNU cache has unknown or repeated extension types".into());
    }
    let descriptors_end = at
        .checked_add(8 + count * 16)
        .filter(|&n| n <= bytes.len())
        .ok_or("GNU cache extension descriptors exceed the file")?;
    let mut seen = BTreeSet::new();
    let mut extents = Vec::new();
    let mut hwcaps = 0;
    for index in 0..count {
        let row = at + 8 + index * 16;
        let tag = word(bytes, row)?;
        let offset = word(bytes, row + 8)? as usize;
        let size = word(bytes, row + 12)? as usize;
        let stop = offset
            .checked_add(size)
            .filter(|&n| n <= bytes.len())
            .ok_or("GNU cache extension data exceeds the file")?;
        if tag > 1
            || !seen.insert(tag)
            || word(bytes, row + 4)? != 0
            || offset < descriptors_end
            || extents.iter().any(|&(a, b)| offset < b && a < stop)
        {
            return Err("GNU cache extension is unknown, overlapping or ambiguous".into());
        }
        extents.push((offset, stop));
        if tag == 1 {
            if offset % 4 != 0 || size == 0 || size % 4 != 0 || size / 4 > 256 {
                return Err("GNU cache hwcaps extension exceeds its supported shape".into());
            }
            let mut names = BTreeSet::new();
            for at in (offset..stop).step_by(4) {
                let name = text(bytes, word(bytes, at)? as usize, first, end)?;
                if !linux_elf::valid_soname(&name) || !names.insert(name) {
                    return Err("GNU cache hwcaps extension has an invalid or repeated name".into());
                }
            }
            hwcaps = size / 4;
        }
    }
    Ok(hwcaps)
}

pub(super) fn entries(bytes: &[u8]) -> Result<Vec<CacheEntry>, String> {
    if bytes.len() < HEADER
        || bytes.len() > MAX_BYTES
        || !bytes.starts_with(b"glibc-ld.so.cache1.1")
        || bytes[28] != 2
        || bytes[29..32].iter().any(|&b| b != 0)
        || bytes[36..48].iter().any(|&b| b != 0)
    {
        return Err("GNU cache requires the bounded little-endian new 1.1 format".into());
    }
    let count = word(bytes, 20)? as usize;
    let string_bytes = word(bytes, 24)? as usize;
    if count > MAX_ENTRIES || string_bytes > MAX_STRINGS {
        return Err("GNU cache entry/string count exceeds its admission bound".into());
    }
    let first = HEADER + count * ENTRY;
    let end = first
        .checked_add(string_bytes)
        .filter(|&n| n <= bytes.len())
        .ok_or("GNU cache entry or string table exceeds the file")?;
    let hwcaps = extensions(bytes, first, end)?;
    let mut result = Vec::new();
    result.try_reserve_exact(count).map_err(|error| error.to_string())?;
    let mut copied = 0usize;
    for index in 0..count {
        let at = HEADER + index * ENTRY;
        let name = text(bytes, word(bytes, at + 4)? as usize, first, end)?;
        let path = text(bytes, word(bytes, at + 8)? as usize, first, end)?;
        let hwcap = wide(bytes, at + 16)?;
        if !linux_elf::valid_soname(&name)
            || !super::normalized_path(&path)
            || word(bytes, at + 12)? != 0
        {
            return Err("GNU cache has an unsupported SONAME, path or OS-version field".into());
        }
        // Validate named hwcap references without filtering out any entry.
        if ((hwcap >> 32) & !0x3ff) == (1 << 30) && (hwcap as u32 as usize) >= hwcaps {
            return Err("GNU cache has an unbound named-hwcap index".into());
        }
        copied = copied
            .checked_add(name.len() + path.len())
            .filter(|&n| n <= MAX_BYTES)
            .ok_or("GNU cache expanded string inventory exceeds its bound")?;
        result.push(CacheEntry { name, path, flags: word(bytes, at)?, hwcap });
    }
    Ok(result)
}

#[cfg(test)]
#[path = "linux_cache_tests.rs"]
mod tests;
