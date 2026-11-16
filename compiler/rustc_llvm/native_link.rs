//! Trust: classify the exact files selected by llvm-config, rather than library-name prefixes.
//!
//! Shared by the LLVM build script and Bootstrap's native development component.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

/// Only the exact native inventory is exposed to Rust's library search. An
/// external LLVM prefix can also contain a private libc++/ABI/unwind runtime;
/// exporting its entire directory silently changes the platform C++ provider.
#[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
pub(crate) struct StaticSearch {
    pub(crate) directory: PathBuf,
    source_directories: BTreeSet<PathBuf>,
}

impl StaticSearch {
    #[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
    pub(crate) fn replaces(&self, directory: &Path) -> bool {
        directory.canonicalize().is_ok_and(|path| self.source_directories.contains(&path))
    }
}

#[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
pub(crate) fn isolate_static_search(
    libraries: &BTreeMap<String, NativeLibrary>,
    output: &Path,
) -> Result<StaticSearch, String> {
    if libraries.is_empty() || libraries.values().any(|lib| lib.kind != LinkKind::Static) {
        return Err("isolated LLVM search requires a nonempty static file inventory".to_owned());
    }
    let mut sources = Vec::with_capacity(libraries.len());
    let mut source_directories = BTreeSet::new();
    let mut filenames = BTreeSet::new();
    for library in libraries.values() {
        let source = library.path.canonicalize().map_err(|error| error.to_string())?;
        if !source.is_file() {
            return Err(format!("selected LLVM archive is not a file: {}", source.display()));
        }
        let declared_parent = library
            .path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        source_directories
            .insert(declared_parent.canonicalize().map_err(|error| error.to_string())?);
        source_directories.insert(source.parent().unwrap().to_owned());
        let filename = library.path.file_name().ok_or("archive filename absent")?;
        if !filenames.insert(filename) {
            return Err("selected LLVM archives have colliding filenames".to_owned());
        }
        sources.push((source, filename));
    }
    // Cargo owns OUT_DIR. Create a fresh child rather than reusing a directory
    // which could retain unselected files from a previous recipe or provider.
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let mut directory = None;
    for _ in 0..64 {
        let candidate = output.join(format!(
            "llvm-static-search-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        match std::fs::create_dir(&candidate) {
            Ok(()) => {
                directory = Some(candidate);
                break;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.to_string()),
        }
    }
    let directory = directory.ok_or("could not reserve a fresh LLVM archive search directory")?;
    for (source, filename) in sources {
        let destination = directory.join(filename);
        // Prefer a hard link, retaining exact archive bytes without duplicating
        // a large LLVM installation. A cross-volume input is copied instead.
        if std::fs::hard_link(&source, &destination).is_err() {
            let mut input = std::fs::File::open(&source).map_err(|error| error.to_string())?;
            let mut output = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&destination)
                .map_err(|error| error.to_string())?;
            std::io::copy(&mut input, &mut output).map_err(|error| error.to_string())?;
        }
    }
    Ok(StaticSearch { directory, source_directories })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LinkKind {
    Static,
    Dynamic,
}

impl LinkKind {
    #[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
    pub(crate) fn rustc_name(self) -> &'static str {
        match self {
            Self::Static => "static",
            Self::Dynamic => "dylib",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NativeLibrary {
    pub(crate) name: String,
    pub(crate) path: PathBuf,
    pub(crate) kind: LinkKind,
}

pub(crate) fn excluded_library(name: &str) -> bool {
    name == "LLVMLineEditor" || name == "z3" || name.starts_with("z3.")
}

pub(crate) fn library_file(
    path: &Path,
    target: &str,
    shared: bool,
) -> Result<NativeLibrary, String> {
    let file = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("LLVM native library has no UTF-8 filename: {}", path.display()))?;
    let (name, kind) = if let Some(name) = file.strip_suffix(".dll.a") {
        if !target.contains("windows") || !shared {
            return Err(format!("LLVM import archive contradicts the selected link mode: {file}"));
        }
        (name.strip_prefix("lib").unwrap_or(name), LinkKind::Dynamic)
    } else if let Some(name) = file.strip_suffix(".a") {
        (name.strip_prefix("lib").unwrap_or(name), LinkKind::Static)
    } else if let Some(name) = file.strip_suffix(".lib") {
        if !target.contains("windows") {
            return Err(format!("LLVM .lib is unsupported for target {target}: {file}"));
        }
        // A Windows import library is also .lib; the selected llvm-config
        // mode, rather than that suffix, distinguishes it from a static archive.
        (name, if shared { LinkKind::Dynamic } else { LinkKind::Static })
    } else if let Some(name) = file.strip_suffix(".dylib") {
        (name.strip_prefix("lib").unwrap_or(name), LinkKind::Dynamic)
    } else if let Some((name, version)) = file.split_once(".so") {
        if !version.is_empty()
            && !(version.starts_with('.')
                && version[1..]
                    .split('.')
                    .all(|part| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit())))
        {
            return Err(format!("unrecognized LLVM shared-library filename: {file}"));
        }
        (name.strip_prefix("lib").unwrap_or(name), LinkKind::Dynamic)
    } else {
        return Err(format!("unrecognized LLVM native library: {}", path.display()));
    };
    if name.is_empty() || name.contains(['/', '\\']) {
        return Err(format!("invalid LLVM native library name: {file}"));
    }
    if !shared && kind == LinkKind::Dynamic && !excluded_library(name) {
        return Err(format!("LLVM static link selected a shared library: {}", path.display()));
    }
    if !excluded_library(name) && !path.is_file() {
        return Err(format!("selected LLVM native library is missing: {}", path.display()));
    }
    Ok(NativeLibrary { name: name.to_owned(), path: path.to_owned(), kind })
}

#[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
pub(crate) fn selected_libraries(
    files: impl IntoIterator<Item = PathBuf>,
    target: &str,
    shared: bool,
) -> Result<BTreeMap<String, NativeLibrary>, String> {
    let mut libraries: BTreeMap<String, NativeLibrary> = BTreeMap::new();
    for path in files {
        let library = library_file(&path, target, shared)?;
        if excluded_library(&library.name) {
            continue;
        }
        if let Some(previous) = libraries.get(&library.name) {
            if previous.kind != library.kind
                || previous.path.canonicalize().map_err(|error| error.to_string())?
                    != library.path.canonicalize().map_err(|error| error.to_string())?
            {
                return Err(format!(
                    "ambiguous LLVM native library {}: {} and {}",
                    library.name,
                    previous.path.display(),
                    library.path.display(),
                ));
            }
        } else {
            libraries.insert(library.name.clone(), library);
        }
    }
    Ok(libraries)
}

// Trust: crossed builds can run a HOST llvm-config. Its file inventory is
// not authority for target files; retain their existing target-link policy.
// Shared builds retain their platform-specific import/runtime policy too.
#[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
pub(crate) fn native_inventory(
    files: impl FnOnce() -> Vec<PathBuf>,
    target: &str,
    shared: bool,
    is_crossed: bool,
) -> Result<Option<BTreeMap<String, NativeLibrary>>, String> {
    if is_crossed || shared {
        return Ok(None);
    }
    selected_libraries(files(), target, shared).map(Some)
}

// Trust: a --libs token must be authorized by the same-mode --libfiles
// inventory. An explicit path must name that exact file, not merely its stem.
#[allow(dead_code, reason = "Trust: used by the shared build-script owner")]
pub(crate) fn selected_library<'a>(
    token: &str,
    libraries: &'a BTreeMap<String, NativeLibrary>,
    target: &str,
    shared: bool,
) -> Result<Option<&'a NativeLibrary>, String> {
    let explicit = if Path::new(token).is_absolute() {
        Some(library_file(Path::new(token), target, shared)?)
    } else {
        None
    };
    let name = if let Some(library) = &explicit {
        library.name.as_str()
    } else if let Some(name) = token.strip_prefix("-l") {
        name
    } else if target.contains("windows") {
        token.strip_suffix(".lib").ok_or_else(|| format!("invalid LLVM link token: {token}"))?
    } else {
        return Err(format!("invalid LLVM link token: {token}"));
    };
    if excluded_library(name) {
        return Ok(None);
    }
    let selected = libraries.get(name).ok_or_else(|| {
        format!("LLVM library {name} is absent from the matching --libfiles inventory")
    })?;
    if let Some(explicit) = explicit {
        if explicit.path.canonicalize().map_err(|error| error.to_string())?
            != selected.path.canonicalize().map_err(|error| error.to_string())?
        {
            return Err(format!("LLVM link path disagrees with --libfiles: {token}"));
        }
    }
    Ok(Some(selected))
}

// Trust: Darwin's SDK supplies z/xml2/m, but not LLVM's optional zstd. A
// static LLVM SDK must not leak a host package's dylib requirement to users.
/// System zstd can be a bare name or an absolute build-machine archive in
/// llvm-config. Keep usable archives; relocate only genuinely missing ones
/// through the separately validated pkg-config provider. Unknown/malformed
/// paths never become absence.
#[derive(Default)]
#[allow(
    dead_code,
    reason = "Trust: used by the compiler build-script consumer of this shared module"
)]
pub(crate) struct ZstdInput {
    pub(crate) provider_tokens: BTreeSet<String>,
    pub(crate) watch_paths: Vec<PathBuf>,
}

#[allow(
    dead_code,
    reason = "Trust: used by the compiler build-script consumer of this shared module"
)]
pub(crate) fn system_zstd_input<S: AsRef<str>>(
    libraries: impl IntoIterator<Item = S>,
) -> Result<ZstdInput, String> {
    let mut input = ZstdInput::default();
    for library in libraries {
        let token = library.as_ref();
        if token == "-lzstd" {
            input.provider_tokens.insert(token.to_owned());
            continue;
        }
        let path = Path::new(token);
        if !path.is_absolute() || path.file_name() != Some(std::ffi::OsStr::new("libzstd.a")) {
            continue;
        }
        match std::fs::metadata(path) {
            Ok(metadata) if metadata.is_file() => watch_declared_path(path, &mut input.watch_paths),
            Ok(_) => return Err(format!("LLVM zstd input is not a regular archive: {token}")),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                // A dangling leaf/ancestor alias is malformed, not relocation.
                // Watch the first existing directory rather than an absent
                // file, which would make Cargo rerun this script forever.
                let mut watch = None;
                for ancestor in path.ancestors() {
                    match std::fs::metadata(ancestor) {
                        Ok(metadata) if metadata.is_dir() => {
                            watch = Some(ancestor);
                            break;
                        }
                        Ok(_) => {
                            return Err(format!(
                                "invalid LLVM zstd ancestor: {}",
                                ancestor.display()
                            ));
                        }
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                            match std::fs::symlink_metadata(ancestor) {
                                Ok(_) => {
                                    return Err(format!(
                                        "dangling LLVM zstd input: {}",
                                        ancestor.display()
                                    ));
                                }
                                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                                Err(error) => return Err(error.to_string()),
                            }
                        }
                        Err(error) => return Err(error.to_string()),
                    }
                }
                let watch = watch.ok_or("LLVM zstd input has no observable ancestor")?;
                watch_declared_path(watch, &mut input.watch_paths);
                input.provider_tokens.insert(token.to_owned());
            }
            Err(error) => return Err(error.to_string()),
        }
    }
    Ok(input)
}

// Resolve its archive through declared pkg-config metadata, never a guessed
// package-manager prefix. Refuse any additional dependency we do not carry.
#[derive(Clone, Debug)]
pub(crate) struct StaticZstd {
    pub(crate) library: NativeLibrary,
    pub(crate) metadata: PathBuf,
    pub(crate) provider: PathBuf,
    #[allow(dead_code, reason = "Trust: used by Bootstrap's native input receipt")]
    pub(crate) version: String,
    pub(crate) watch_paths: Vec<PathBuf>,
}

pub(crate) fn static_zstd(program: &Path, target: &str) -> Result<StaticZstd, String> {
    static_zstd_bound(program, target, None)
}

/// Resolve only metadata from the explicitly declared native dependency directory.
pub(crate) fn static_zstd_in(
    program: &Path,
    target: &str,
    directory: &Path,
) -> Result<StaticZstd, String> {
    if !directory.is_absolute() || !directory.is_dir() {
        return Err("libzstd metadata input must be an absolute existing directory".to_owned());
    }
    static_zstd_bound(program, target, Some(directory))
}

fn static_zstd_bound(
    program: &Path,
    target: &str,
    directory: Option<&Path>,
) -> Result<StaticZstd, String> {
    let canonical_directory =
        directory.map(Path::canonicalize).transpose().map_err(|e| e.to_string())?;
    let declared_provider = if program.is_absolute() || program.components().count() > 1 {
        program.to_owned()
    } else {
        std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
            .map(|directory| directory.join(program))
            .find(|candidate| candidate.is_file())
            .ok_or_else(|| format!("could not locate pkg-config provider {}", program.display()))?
    };
    let provider = declared_provider.canonicalize().map_err(|error| error.to_string())?;
    let mut resolved = static_zstd_with(&provider, target, |args| {
        let mut command = Command::new(&provider);
        if let Some(directory) = directory {
            let mut argument = std::ffi::OsString::from("--with-path=");
            argument.push(directory);
            command.arg(argument);
        }
        let output = command
            .args(args)
            .output()
            .map_err(|error| format!("could not query {}: {error}", provider.display()))?;
        if !output.status.success() {
            return Err(format!(
                "{} {args:?} failed: {}",
                provider.display(),
                String::from_utf8_lossy(&output.stderr).trim(),
            ));
        }
        String::from_utf8(output.stdout).map_err(|error| error.to_string())
    })?;
    if let Some(directory) = canonical_directory {
        validate_metadata_directory(&resolved.metadata, &directory)?;
        watch_declared_path(directory.as_path(), &mut resolved.watch_paths);
    }
    if let Some(directory) = directory {
        watch_declared_path(directory, &mut resolved.watch_paths);
    }
    watch_declared_path(&declared_provider, &mut resolved.watch_paths);
    Ok(resolved)
}

fn validate_metadata_directory(metadata: &Path, directory: &Path) -> Result<(), String> {
    if metadata.parent() != Some(directory) {
        return Err("libzstd metadata escaped the declared dependency directory".to_owned());
    }
    Ok(())
}

// Trust: watching only canonical old package files misses an upgrade that
// retargets the declared package alias. Watch the parent of each such symlink
// too, so Cargo re-resolves the provider instead of retaining stale inputs.
fn watch_declared_path(path: &Path, paths: &mut Vec<PathBuf>) {
    paths.push(path.to_owned());
    for ancestor in path.ancestors() {
        if std::fs::symlink_metadata(ancestor)
            .is_ok_and(|metadata| metadata.file_type().is_symlink())
        {
            if let Some(parent) = ancestor.parent() {
                paths.push(parent.to_owned());
            }
        }
    }
}

fn static_zstd_with(
    provider: &Path,
    target: &str,
    mut query: impl FnMut(&[&str]) -> Result<String, String>,
) -> Result<StaticZstd, String> {
    let libdir = query(&["--variable=libdir", "libzstd"])?;
    let libdir = Path::new(libdir.trim());
    if !libdir.is_absolute() {
        return Err("libzstd pkg-config libdir must be absolute".to_owned());
    }
    let mut watch_paths = Vec::new();
    watch_declared_path(libdir, &mut watch_paths);
    watch_declared_path(&libdir.join("libzstd.a"), &mut watch_paths);
    let declared_libdir = libdir.to_owned();
    let libdir = libdir.canonicalize().map_err(|error| error.to_string())?;
    // pkgconf escapes its built-in pcfiledir variable even though ordinary
    // variable values are raw. Ask for the actual selected metadata filename;
    // interpreting an escaped directory would invent a different pathname.
    let metadata = query(&["--path", "libzstd"])?;
    let metadata = metadata.trim();
    if metadata.chars().any(char::is_control) {
        return Err("libzstd metadata filename contains control characters".to_owned());
    }
    let metadata = PathBuf::from(metadata);
    if !metadata.is_absolute()
        || metadata.file_name() != Some(std::ffi::OsStr::new("libzstd.pc"))
        || !metadata.is_file()
    {
        return Err("libzstd pkg-config source metadata is missing".to_owned());
    }
    watch_declared_path(&metadata, &mut watch_paths);
    let metadata = metadata.canonicalize().map_err(|error| error.to_string())?;
    let version = query(&["--modversion", "libzstd"])?;
    let version = version.trim().to_owned();
    if version.is_empty() || version.chars().any(char::is_control) {
        return Err("libzstd pkg-config version is malformed".to_owned());
    }
    // Select paths from whole variable responses. Some managed providers do
    // not shell-escape spaces in --libs, so that string cannot name archives.
    let libraries = query(&["--libs-only-l", "--static", "libzstd"])?;
    let libraries = shlex::split(&libraries).ok_or("malformed libzstd library metadata")?;
    if libraries.len() != 1 || libraries[0] != "-lzstd" {
        return Err("libzstd static metadata has additional or missing libraries".to_owned());
    }
    // Ask for the complete flags before splitting them. Providers can split a
    // raw path containing spaces incorrectly in their --libs-only-L/other
    // views. The declared whole libdir remains the boundary; every remaining
    // token still passes the same strict dependency/flag validation below.
    let flags =
        zstd_link_flags(&query(&["--libs", "--static", "libzstd"])?, &declared_libdir, &libdir)?;
    validate_zstd_flags(&flags, &libdir)?;
    let library = library_file(&libdir.join("libzstd.a"), target, false)?;
    watch_paths.extend([library.path.clone(), metadata.clone(), provider.to_owned()]);
    Ok(StaticZstd { library, metadata, provider: provider.to_owned(), version, watch_paths })
}

fn zstd_link_flags(raw: &str, declared: &Path, canonical: &Path) -> Result<Vec<String>, String> {
    let raw = raw.trim();
    // A declared symlink can prefix its longer canonical pathname. Try the
    // longest known whole operand before interpreting its remainder as flags.
    let mut searches = [declared, canonical].map(|directory| format!("-L{}", directory.display()));
    searches.sort_by_key(|search| std::cmp::Reverse(search.len()));
    for search in searches {
        if let Some(tail) = raw.strip_prefix(&search) {
            if tail.starts_with(char::is_whitespace) {
                let mut flags = vec![search];
                flags.extend(shlex::split(tail).ok_or("malformed libzstd linker metadata")?);
                return Ok(flags);
            }
        }
    }
    shlex::split(raw).ok_or_else(|| "malformed libzstd linker metadata".to_owned())
}

fn validate_zstd_flags(flags: &[String], libdir: &Path) -> Result<(), String> {
    let mut self_link = false;
    let mut flags = flags.iter();
    while let Some(flag) = flags.next() {
        if flag == "-lzstd" {
            self_link = true;
        } else if let Some(directory) = flag.strip_prefix("-L") {
            let directory = if directory.is_empty() {
                flags.next().ok_or("libzstd metadata has an incomplete -L flag")?.as_str()
            } else {
                directory
            };
            if Path::new(directory).canonicalize().map_err(|error| error.to_string())? != libdir {
                return Err(
                    "libzstd metadata names an undeclared native search directory".to_owned()
                );
            }
        } else {
            return Err(format!(
                "libzstd static metadata has an additional dependency/flag {flag:?}; \
                 the SDK native closure must explicitly carry it",
            ));
        }
    }
    if !self_link {
        return Err("libzstd static metadata did not select -lzstd".to_owned());
    }
    Ok(())
}

#[cfg(test)]
#[path = "native_link/tests.rs"]
mod tests;
