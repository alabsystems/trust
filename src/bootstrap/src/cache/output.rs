//! Retained normal Bootstrap configuration; location DATA is never exclusion.
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CString, OsStr};
use std::fs::{File, Metadata, OpenOptions};
use std::io;
use std::os::fd::{AsRawFd as _, FromRawFd as _};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{FileExt as _, MetadataExt as _, OpenOptionsExt as _};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use crate::core::config::Config;

const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_FILES: usize = 64;
fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct Stamp {
    identity: (u64, u64),
    mode: u32,
    owner: (u32, u32),
    links: u64,
    size: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl Stamp {
    fn read(meta: &Metadata) -> io::Result<Self> {
        if !meta.is_dir() && !meta.is_file() {
            return Err(invalid("configuration namespace is not regular"));
        }
        Ok(Self {
            identity: (meta.dev(), meta.ino()),
            mode: meta.mode(),
            owner: (meta.uid(), meta.gid()),
            links: meta.nlink(),
            size: meta.len(),
            modified: (meta.mtime(), meta.mtime_nsec()),
            changed: (meta.ctime(), meta.ctime_nsec()),
        })
    }
}
struct Directory {
    file: Arc<File>,
    before: Stamp,
}
struct Input {
    path: PathBuf,
    file: File,
    before: Stamp,
    bytes: Vec<u8>,
}

/// A non-cloneable selection retaining the exact files parsed, with no path-to-
/// guard constructor, deserializer, execution or build-completion authority.
pub struct SelectedOutput {
    root: PathBuf,
    output: PathBuf,
    directories: BTreeMap<PathBuf, Directory>,
    inputs: Vec<Input>,
    absent: Vec<PathBuf>,
    mapping: BTreeMap<PathBuf, Stamp>,
}
impl SelectedOutput {
    pub fn capture(root: &Path) -> Result<Self, String> {
        if std::env::var_os("RUST_BOOTSTRAP_CONFIG").is_some() {
            return Err("cache pruning refuses an ambient Bootstrap config selector; use this repository's normal config".into());
        }
        Self::capture_inner(root).map_err(|e| format!("Bootstrap output selection: {e}"))
    }
    fn capture_inner(root: &Path) -> io::Result<Self> {
        let root = root.canonicalize()?;
        let file = Arc::new(open_root(&root)?);
        let before = Stamp::read(&file.metadata()?)?;
        let mut selected = Self {
            root,
            output: PathBuf::new(),
            directories: BTreeMap::from([(PathBuf::new(), Directory { file, before })]),
            inputs: Vec::new(),
            absent: Vec::new(),
            mapping: BTreeMap::new(),
        };
        let mut fields = Fields::default();
        // Native prune selects the explicit repository's normal root config,
        // matching x.py's root working directory, never an unrelated cwd file.
        for name in ["bootstrap.toml", "config.toml"] {
            if absent(selected.root_file(), OsStr::new(name))? {
                selected.absent.push(PathBuf::from(name));
                continue;
            }
            // A missing include/profile is an error, never a default fallback.
            fields = selected.config(Path::new(name), &mut BTreeSet::new())?;
            break;
        }
        if let Some(profile) = fields.profile.clone() {
            let profile = if profile == "user" { "dist" } else { &profile };
            if profile.is_empty()
                || !profile.bytes().all(|b| b.is_ascii_alphanumeric() || b"_-".contains(&b))
            {
                return Err(invalid("configuration profile is not a Bootstrap profile name"));
            }
            fields.inherit(selected.config(
                &PathBuf::from(format!("src/bootstrap/defaults/bootstrap.{profile}.toml")),
                &mut BTreeSet::new(),
            )?);
        }
        let configured = PathBuf::from(fields.output.unwrap_or_else(|| "build".into()));
        let relative = if configured.is_absolute() {
            configured
                .strip_prefix(&selected.root)
                .map_err(|_| invalid("configured output is outside the original repository"))?
                .to_owned()
        } else {
            configured
        };
        normal(&relative)?;
        selected.output = selected.root.join(&relative);
        let mut path = PathBuf::new();
        let mut directory = Arc::clone(selected.root_file());
        for part in relative.components() {
            let Component::Normal(name) = part else { unreachable!() };
            path.push(name);
            let next = Arc::new(open(&directory, name, true)?);
            selected.mapping.insert(path.clone(), Stamp::read(&next.metadata()?)?);
            directory = next;
        }
        if selected
            .inputs
            .iter()
            .any(|input| selected.root.join(&input.path).starts_with(&selected.output))
        {
            return Err(invalid("configured output contains a retained config input"));
        }
        selected.check()?;
        Ok(selected)
    }
    fn root_file(&self) -> &Arc<File> {
        &self.directories.get(Path::new("")).expect("retained root").file
    }
    fn parent(&mut self, path: &Path) -> io::Result<Arc<File>> {
        let mut at = PathBuf::new();
        let mut directory = Arc::clone(self.root_file());
        for part in path.components() {
            let Component::Normal(name) = part else {
                return Err(invalid("non-normal configuration path"));
            };
            at.push(name);
            let file = Arc::new(open(&directory, name, true)?);
            let before = Stamp::read(&file.metadata()?)?;
            if let Some(prior) = self.directories.get(&at) {
                if before != prior.before {
                    return Err(invalid("configuration parent changed"));
                }
            } else {
                self.directories.insert(at.clone(), Directory { file: Arc::clone(&file), before });
            }
            directory = file;
        }
        Ok(directory)
    }
    fn config(&mut self, path: &Path, active: &mut BTreeSet<PathBuf>) -> io::Result<Fields> {
        normal(path)?;
        if self.inputs.len() >= MAX_FILES || !active.insert(path.to_owned()) {
            return Err(invalid("configuration include population/cycle bound exceeded"));
        }
        let parent = self.parent(path.parent().unwrap_or(Path::new("")))?;
        let file = open(&parent, path.file_name().expect("normal leaf"), false)?;
        let before = Stamp::read(&file.metadata()?)?;
        if !file.metadata()?.is_file() || before.links != 1 {
            return Err(invalid("Bootstrap config must be one original regular file"));
        }
        let bytes = read(&file)?;
        if before != Stamp::read(&file.metadata()?)? {
            return Err(invalid("config changed while reading"));
        }
        let (output, includes, profile) =
            Config::cache_output_fields(std::str::from_utf8(&bytes).map_err(io::Error::other)?)
                .map_err(io::Error::other)?;
        self.inputs.push(Input { path: path.to_owned(), file, before, bytes });
        let mut fields = Fields { output, profile };
        // SAME Bootstrap order: own fields, last include first, profile last.
        for include in includes.iter().rev() {
            if include.is_absolute() {
                return Err(invalid("cache config includes must remain repository-relative"));
            }
            fields.inherit(
                self.config(&path.parent().unwrap_or(Path::new("")).join(include), active)?,
            );
        }
        active.remove(path);
        Ok(fields)
    }
    pub fn root(&self) -> &Path {
        &self.root
    }
    pub fn output(&self) -> &Path {
        &self.output
    }
    pub fn check_current(&self) -> Result<(), String> {
        self.check().map_err(|e| format!("Bootstrap output selection changed: {e}"))
    }
    fn check(&self) -> io::Result<()> {
        let root = self.root_file();
        let original = &self.directories.get(Path::new("")).expect("retained root").before;
        if Stamp::read(&open_root(&self.root)?.metadata()?)?.identity != original.identity {
            return Err(invalid("original repository name changed"));
        }
        for (path, held) in &self.directories {
            let now = Stamp::read(&walk(root, path)?.metadata()?)?;
            // A configless default retains actual root identity + explicit
            // name absences. Real configs retain complete parent origins.
            if (!self.inputs.is_empty()
                && (now != held.before || Stamp::read(&held.file.metadata()?)? != held.before))
                || now.identity != held.before.identity
            {
                return Err(invalid("original config parent changed"));
            }
        }
        for path in &self.absent {
            if !absent(root, path.as_os_str())? {
                return Err(invalid("higher-priority config appeared"));
            }
        }
        for input in &self.inputs {
            let parent = walk(root, input.path.parent().unwrap_or(Path::new("")))?;
            let named = open(&parent, input.path.file_name().expect("normal leaf"), false)?;
            if Stamp::read(&input.file.metadata()?)? != input.before
                || Stamp::read(&named.metadata()?)? != input.before
                || read(&input.file)? != input.bytes
                || read(&named)? != input.bytes
            {
                return Err(invalid("original config bytes or name changed"));
            }
        }
        for (path, prior) in &self.mapping {
            if Stamp::read(&walk(root, path)?.metadata()?)?.identity != prior.identity {
                return Err(invalid("configured output mapping changed"));
            }
        }
        // Closing bookends cannot convert a changed config into a default.
        for (path, held) in &self.directories {
            if !self.inputs.is_empty()
                && Stamp::read(&walk(root, path)?.metadata()?)? != held.before
            {
                return Err(invalid("config parent changed during recheck"));
            }
        }
        Ok(())
    }
}
#[derive(Default)]
struct Fields {
    output: Option<String>,
    profile: Option<String>,
}
impl Fields {
    fn inherit(&mut self, lower: Self) {
        if self.output.is_none() {
            self.output = lower.output;
        }
        if self.profile.is_none() {
            self.profile = lower.profile;
        }
    }
}
fn normal(path: &Path) -> io::Result<()> {
    let parts: Vec<_> = path.components().collect();
    if parts.is_empty()
        || parts.len() > 64
        || parts.iter().any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(invalid("configuration path is not a bounded proper repository-relative path"));
    }
    Ok(())
}
fn open_root(path: &Path) -> io::Result<File> {
    OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(path)
}
fn open(parent: &File, name: &OsStr, directory: bool) -> io::Result<File> {
    let name = CString::new(name.as_bytes()).map_err(io::Error::other)?;
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_CLOEXEC
        | libc::O_NONBLOCK
        | if directory { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 { Err(io::Error::last_os_error()) } else { Ok(unsafe { File::from_raw_fd(fd) }) }
}
fn walk(root: &File, path: &Path) -> io::Result<File> {
    let mut at = open(root, OsStr::new("."), true)?;
    for part in path.components() {
        let Component::Normal(name) = part else {
            return Err(invalid("non-normal retained namespace"));
        };
        at = open(&at, name, true)?;
    }
    Ok(at)
}
fn absent(parent: &File, name: &OsStr) -> io::Result<bool> {
    // no-follow open refuses symlinks (including dangling ones); only the
    // actual direct ENOENT is positive absence, never a broken/unknown entry.
    match open(parent, name, false) {
        Ok(_) => Ok(false),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(true),
        Err(e) => Err(e),
    }
}
fn read(file: &File) -> io::Result<Vec<u8>> {
    if file.metadata()?.len() > MAX_BYTES as u64 {
        return Err(invalid("config exceeds byte bound"));
    }
    let mut bytes = Vec::new();
    let mut block = [0; 8192];
    loop {
        let n = file.read_at(&mut block, bytes.len() as u64)?;
        if n == 0 {
            break;
        }
        if bytes.len() + n > MAX_BYTES {
            return Err(invalid("config grew beyond byte bound"));
        }
        bytes.extend_from_slice(&block[..n]);
    }
    Ok(bytes)
}
#[cfg(test)]
mod tests;
