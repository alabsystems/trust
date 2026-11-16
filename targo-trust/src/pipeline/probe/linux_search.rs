//! The pinned loader reports its own compiled default directories and all
//! glibc-hwcaps names. We protect all reported names, including inactive ones.
//! GNU 2.39 elf/dl-diagnostics.c and elf/dl-hwcaps.c specify these fields and
//! show that, with an empty environment and no command-line override, the
//! search suffixes are precisely those names plus the base directory.

use std::collections::{BTreeMap, BTreeSet};

use super::super::linux_elf;
use super::{AuthorityKind, CacheEntry, LoaderSearch, SearchDirectoryEntry};

pub(super) const MAX_PATHS: usize = 32_768;
pub(super) const MAX_NODES: usize = 128;
pub(super) const MAX_TOTAL_NODES: usize = 262_144;
pub(super) const MAX_AUTHORITY_TEXT: usize = 32 * 1024 * 1024;

fn quoted(value: &str) -> Result<&str, String> {
    let value = value
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .ok_or("GNU loader search diagnostics require a quoted string")?;
    if value.len() > 4096
        || value.bytes().any(|b| !(0x20..=0x7e).contains(&b) || b == b'"' || b == b'\\')
    {
        return Err("GNU loader search diagnostics contain unsupported escaping or bytes".into());
    }
    Ok(value)
}

fn system_directory(path: &str) -> bool {
    matches!(path, "/lib" | "/lib64" | "/usr/lib" | "/usr/lib64") || super::system_path(path)
}

pub(super) fn validate_loader(search: &LoaderSearch) -> Result<(), String> {
    // 2.39 has no legacy combinatorial hwcap search; the cited source
    // establishes completeness for this version. Unknown versions fail closed.
    if search.glibc_version != "2.39"
        || search.system_directories.is_empty()
        || search.system_directories.len() > 32
        || search.hwcaps_subdirectories.len() > 32
    {
        return Err("GNU loader search semantics are not an admitted bounded version".into());
    }
    let mut dirs = BTreeSet::new();
    for directory in &search.system_directories {
        if !super::normalized_path(directory)
            || !system_directory(directory)
            || !dirs.insert(directory)
        {
            return Err("GNU loader has a duplicate or unsupported default directory".into());
        }
    }
    let mut caps = BTreeSet::new();
    for cap in &search.hwcaps_subdirectories {
        if !linux_elf::valid_soname(cap) || !caps.insert(cap) {
            return Err("GNU loader has a duplicate or invalid hwcaps subdirectory".into());
        }
    }
    Ok(())
}

pub(super) fn diagnostics(output: &str, interpreter: &str) -> Result<LoaderSearch, String> {
    let mut bound = BTreeMap::new();
    let mut directories = Vec::new();
    for line in output.lines() {
        let (key, value) =
            line.split_once('=').ok_or("GNU loader diagnostics have a malformed record")?;
        if let Some(index) =
            key.strip_prefix("path.system_dirs[0x").and_then(|s| s.strip_suffix(']'))
        {
            let index = usize::from_str_radix(index, 16)
                .map_err(|_| "invalid GNU system-directory index")?;
            let path =
                quoted(value)?.strip_suffix('/').ok_or("GNU system directory lacks its suffix")?;
            if index != directories.len() || directories.len() == 32 {
                return Err("GNU system directory indices are repeated, sparse or unbounded".into());
            }
            directories.push(path.to_owned());
        } else if matches!(
            key,
            "dl_hwcaps_subdirs"
                | "dl_hwcaps_subdirs_active"
                | "path.sysconfdir"
                | "path.rtld"
                | "version.version"
        ) {
            if bound.insert(key, value).is_some() {
                return Err("GNU loader repeats a search-configuration field".into());
            }
        } else if key == "path.prefix" {
            if !super::normalized_path(quoted(value)?) {
                return Err("GNU loader has a non-normalized installation prefix".into());
            }
        } else if key.starts_with("path.") || key.starts_with("dl_hwcaps") {
            return Err("GNU loader has an unknown search-configuration field".into());
        }
    }
    let get = |key| bound.get(key).copied().ok_or_else(|| format!("GNU loader omitted {key}"));
    if quoted(get("path.sysconfdir")?)? != "/etc" || quoted(get("path.rtld")?)? != interpreter {
        return Err("GNU loader does not use the admitted interpreter/cache configuration".into());
    }
    let caps = quoted(get("dl_hwcaps_subdirs")?)?;
    let caps =
        if caps.is_empty() { Vec::new() } else { caps.split(':').map(str::to_owned).collect() };
    let mask = get("dl_hwcaps_subdirs_active")?
        .strip_prefix("0x")
        .and_then(|s| u64::from_str_radix(s, 16).ok())
        .ok_or("GNU hwcaps mask is not bounded hex")?;
    if caps.len() > 32 || mask >> caps.len() != 0 {
        return Err("GNU hwcaps mask exceeds the named suffixes".into());
    }
    let search = LoaderSearch {
        glibc_version: quoted(get("version.version")?)?.to_owned(),
        system_directories: directories,
        hwcaps_subdirectories: caps,
    };
    validate_loader(&search)?;
    Ok(search)
}

pub(super) fn requests(
    search: &LoaderSearch,
    interpreter: &str,
    entries: &[CacheEntry],
    directory_entries: &[SearchDirectoryEntry],
    names: &[String],
) -> Result<Vec<(String, AuthorityKind)>, String> {
    validate_loader(search)?;
    if !matches!(interpreter, "/lib/ld-linux-aarch64.so.1" | "/lib64/ld-linux-x86-64.so.2") {
        return Err("GNU runtime has no admitted original interpreter path".into());
    }
    if entries.len() > super::cache::MAX_ENTRIES
        || directory_entries.len() > 16_384
        || names.len() > 256
    {
        return Err("GNU resolution inventory exceeds its admission bound".into());
    }
    let mut requests = BTreeMap::new();
    let mut text_bytes = 0usize;
    let mut add = |path: String, kind| -> Result<(), String> {
        if !super::normalized_path(&path) {
            return Err("GNU resolution source is not absolute and normalized".into());
        }
        let size = path.len();
        if let Some(previous) = requests.insert(path, kind) {
            if previous != kind {
                return Err("GNU resolution source has conflicting file/directory roles".into());
            }
        } else {
            text_bytes = text_bytes
                .checked_add(size)
                .filter(|&n| n <= MAX_AUTHORITY_TEXT)
                .ok_or("GNU resolution path text exceeds its bound")?;
        }
        if requests.len() > MAX_PATHS {
            return Err("GNU resolution source count exceeds its bound".into());
        }
        Ok(())
    };
    add("/etc/ld.so.cache".into(), AuthorityKind::Object)?;
    add("/etc/ld.so.preload".into(), AuthorityKind::Object)?;
    // Normal exec follows this named path in the kernel. Diagnostics and --list
    // use its canonical target, so protecting only cached/default DSO sources
    // would leave intermediate interpreter symlink targets outside admission.
    add(interpreter.to_owned(), AuthorityKind::Object)?;
    let mut cached_text = 0usize;
    for entry in entries {
        if !linux_elf::valid_soname(&entry.name) {
            return Err("GNU cache has an invalid dependency name".into());
        }
        cached_text = cached_text
            .checked_add(entry.name.len() + entry.path.len())
            .filter(|&n| n <= super::cache::MAX_BYTES)
            .ok_or("GNU cached target text exceeds its bound")?;
        add(entry.path.clone(), AuthorityKind::Object)?;
    }
    let directories = directories(search)?;
    let mut previous = None;
    for entry in directory_entries {
        let key = (&entry.directory, &entry.name);
        if !directories.contains(&entry.directory)
            || !linux_elf::valid_soname(&entry.name)
            || entry.kind == AuthorityKind::Symlink
            || previous.is_some_and(|old| old >= key)
        {
            return Err("GNU default directory census is duplicate, unordered or foreign".into());
        }
        previous = Some(key);
        add(format!("{}/{}", entry.directory, entry.name), entry.kind)?;
    }
    for directory in directories {
        add(directory.clone(), AuthorityKind::Directory)?;
        for name in names {
            if !linux_elf::valid_soname(name) {
                return Err("GNU default search has an invalid dependency name".into());
            }
            add(format!("{directory}/{name}"), AuthorityKind::Object)?;
        }
    }
    Ok(requests.into_iter().collect())
}

pub(super) fn directories(search: &LoaderSearch) -> Result<Vec<String>, String> {
    validate_loader(search)?;
    let mut result = BTreeSet::new();
    for directory in &search.system_directories {
        result.insert(directory.clone());
        for cap in &search.hwcaps_subdirectories {
            result.insert(format!("{directory}/glibc-hwcaps/{cap}"));
        }
    }
    Ok(result.into_iter().collect())
}

#[cfg(test)]
#[path = "linux_search_tests.rs"]
mod tests;
