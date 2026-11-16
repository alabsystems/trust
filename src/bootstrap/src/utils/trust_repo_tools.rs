//! Trust: content identities for native tools, external LLVM and their loaders.
//!
//! System libraries in Apple's sealed shared cache are named by the OS build;
//! non-system libraries must resolve to readable, content-bound files. This is
//! local build reuse, not a claim of hermetic or verified execution.

use std::collections::{BTreeSet, VecDeque};
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;

use sha2::{Digest, Sha256};

use crate::utils::trust_repo_cache as cache;

pub(crate) fn tool_digest(path: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    for path in loader_closure([path.to_owned()])? {
        cache::add(&mut hash, cache::tree_digest(&path)?);
    }
    Ok(cache::finish(hash))
}

pub(crate) fn installation_digest(root: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    cache::add(&mut hash, cache::installation_tree_digest(root)?);
    let mut binaries = Vec::new();
    for directory in [root.join("lib"), root.join("bin")] {
        if !directory.is_dir() {
            continue;
        }
        for entry in walkdir::WalkDir::new(directory) {
            let entry = entry.map_err(|e| e.to_string())?;
            if entry.path().is_file() && is_object(entry.path())? {
                binaries.push(entry.path().to_owned());
            }
        }
    }
    for path in loader_closure(binaries)? {
        if !path.starts_with(root) {
            cache::add(&mut hash, cache::tree_digest(&path)?);
        }
    }
    Ok(cache::finish(hash))
}

/// Bind every installed namespace entry and the selected host tool's required
/// loader closure. A developer installation also ships foreign-target support
/// objects; their bytes remain inputs without asserting they are loaded here.
pub(crate) fn selected_tool_installation_digest(
    root: &Path,
    tool: &Path,
) -> Result<String, String> {
    let mut hash = Sha256::new();
    cache::add(&mut hash, b"trust.selected-tool-installation/v1");
    cache::add(&mut hash, tool.as_os_str().as_encoded_bytes());
    cache::add(&mut hash, cache::installation_tree_digest(root)?);
    cache::add(&mut hash, tool_digest(tool)?);
    Ok(cache::finish(hash))
}

pub(crate) fn query(program: &Path, arguments: &[&str]) -> Result<String, String> {
    crate::utils::exec::require_standalone_process("native tool query")
        .map_err(|error| error.to_string())?;
    let output = Command::new(program).args(arguments).output().map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(format!("cannot bind native tool query {} {arguments:?}", program.display()));
    }
    String::from_utf8(output.stdout).map(|text| text.trim().to_owned()).map_err(|e| e.to_string())
}

fn is_object(path: &Path) -> Result<bool, String> {
    let mut magic = [0_u8; 4];
    let mut file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let count = file.read(&mut magic).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(count == 4
        && matches!(
            magic,
            [0x7f, b'E', b'L', b'F']
                | [0xfe, 0xed, 0xfa, 0xce]
                | [0xce, 0xfa, 0xed, 0xfe]
                | [0xfe, 0xed, 0xfa, 0xcf]
                | [0xcf, 0xfa, 0xed, 0xfe]
                | [0xca, 0xfe, 0xba, 0xbe]
                | [0xbe, 0xba, 0xfe, 0xca]
                | [0xca, 0xfe, 0xba, 0xbf]
                | [0xbf, 0xba, 0xfe, 0xca]
        ))
}

fn loader_closure(roots: impl IntoIterator<Item = PathBuf>) -> Result<BTreeSet<PathBuf>, String> {
    let mut pending = VecDeque::from_iter(roots);
    let mut files = BTreeSet::new();
    while let Some(path) = pending.pop_front() {
        let path = std::fs::canonicalize(&path).map_err(|e| {
            format!("cannot resolve required native tool/loader {}: {e}", path.display())
        })?;
        if !files.insert(path.clone()) {
            continue;
        }
        if files.len() > 10000 {
            return Err("native tool loader closure exceeds its bound".into());
        }
        if !is_object(&path)? {
            continue;
        }
        let before = cache::file_digest(&path)?;
        #[cfg(target_os = "macos")]
        let dependencies = macos_dependencies(&path)?;
        #[cfg(target_os = "linux")]
        let dependencies = linux_dependencies(&path)?;
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let dependencies: Vec<PathBuf> =
            return Err("native loader input closure is unsupported on this host".into());
        if cache::file_digest(&path)? != before {
            return Err(format!("{} changed during loader inspection", path.display()));
        }
        pending.extend(dependencies);
    }
    Ok(files)
}

#[cfg(target_os = "macos")]
fn macos_dependencies(binary: &Path) -> Result<Vec<PathBuf>, String> {
    let name = binary.to_str().ok_or("non-UTF-8 native tool path")?;
    let dependencies = query(Path::new("/usr/bin/otool"), &["-L", name])?;
    let commands = query(Path::new("/usr/bin/otool"), &["-l", name])?;
    let parent = binary.parent().ok_or("native tool has no directory")?;
    let mut rpaths = Vec::new();
    let mut in_rpath = false;
    for line in commands.lines().map(str::trim) {
        if line == "cmd LC_RPATH" {
            in_rpath = true;
        } else if in_rpath && line.starts_with("path ") {
            let path = line.strip_prefix("path ").unwrap().split(" (offset ").next().unwrap();
            rpaths.push(expand_loader_path(path, parent)?);
            in_rpath = false;
        }
    }
    let mut paths = Vec::new();
    for dependency in dependencies
        .lines()
        .map(str::trim)
        .filter_map(|line| line.split_once(" (compatibility version ").map(|(name, _)| name))
    {
        // These are supplied by the sealed OS/shared cache and named by sw_vers.
        if dependency.starts_with("/usr/lib/") || dependency.starts_with("/System/Library/") {
            continue;
        }
        if let Some(suffix) = dependency.strip_prefix("@rpath/") {
            let mut found = false;
            for root in &rpaths {
                let path = root.join(suffix);
                if path.is_file() {
                    paths.push(path);
                    found = true;
                }
            }
            // A consumer's install-relative library path is also a loader input.
            for root in [parent.to_owned(), parent.join("../lib")] {
                let path = root.join(suffix);
                if path.is_file() {
                    paths.push(path);
                    found = true;
                }
            }
            if !found {
                return Err(format!("cannot bind {dependency} loaded by {}", binary.display()));
            }
        } else {
            paths.push(expand_loader_path(dependency, parent)?);
        }
    }
    Ok(paths)
}

#[cfg(target_os = "macos")]
fn expand_loader_path(value: &str, parent: &Path) -> Result<PathBuf, String> {
    if matches!(value, "@loader_path" | "@executable_path") {
        Ok(parent.to_owned())
    } else if let Some(suffix) =
        value.strip_prefix("@loader_path/").or_else(|| value.strip_prefix("@executable_path/"))
    {
        Ok(parent.join(suffix))
    } else if Path::new(value).is_absolute() {
        Ok(PathBuf::from(value))
    } else {
        Err(format!("unresolved native tool loader path {value}"))
    }
}

#[cfg(target_os = "linux")]
fn linux_dependencies(binary: &Path) -> Result<Vec<PathBuf>, String> {
    crate::utils::exec::require_standalone_process("native tool loader query")
        .map_err(|error| error.to_string())?;
    let name = binary.to_str().ok_or("non-UTF-8 native tool path")?;
    let output = Command::new("ldd").arg(name).output().map_err(|e| e.to_string())?;
    let text = format!(
        "{}\n{}",
        String::from_utf8(output.stdout).map_err(|e| e.to_string())?,
        String::from_utf8(output.stderr).map_err(|e| e.to_string())?
    );
    if text.contains("not found") {
        return Err(format!("unresolved loader dependency in {name}"));
    }
    if text.contains("statically linked") || text.contains("not a dynamic executable") {
        return Ok(Vec::new());
    }
    if !output.status.success() {
        return Err(format!("cannot inspect native loader dependencies of {name}"));
    }
    Ok(text.split_whitespace().filter(|part| part.starts_with('/')).map(PathBuf::from).collect())
}

#[cfg(test)]
mod tests;
