//! Trust: which incremental folder a cargo unit's compile wrote (DC-12c), in std alone, so
//! bootstrap's compiler wrapper (`src/bin/rustc.rs`) and its prune (`trust_prune.rs`) share
//! one format.
//!
//! **The link.** Cargo hands every unit of a profile it compiles incrementally the same
//! `-C incremental=<profile>/incremental`, and the compiler names the folder inside it:
//! `<crate>-<stable crate id>` (`crate_path` in `compiler/rustc_incremental/src/persist/fs.rs`).
//! The compiler collects old sessions only inside the folder it uses
//! (`garbage_collect_session_directories`), so a unit's new variant leaves the old variant's
//! folder behind for good, and only the compile knows which folder is its unit's: the stable
//! crate id hashes the crate name, `-C metadata` and the compiler's version.
//!
//! **The note.** The wrapper reads the call's incremental directory before the compiler runs
//! ([`Before::read`]: each folder of the call's crate name with its modification time) and,
//! after a compile that succeeded, writes beside those folders one file named by the unit's id
//! ([`NOTE_PREFIX`]`<unit id>`) that lists, one per line, each folder of that crate name the
//! compile made or changed ([`Before::note`]): the compiler adds a session directory to the
//! folder it uses on every compile, so that folder's entries change, and its time with them
//! where the file system's clock ticks finer than the compile (a folder counts as changed when
//! either did, so a coarse clock misses none). The note is staged and renamed into place, so a
//! reader sees a whole one; a stage the wrapper could not finish (no room, killed between the
//! write and the rename) is debris the prune removes ([`partial_note`]), since it runs only
//! under the tree's cargo locks, while no compile of that tree runs. A compile that changed no
//! folder writes none and leaves the unit's last note. Two compiles of one crate name that run at once in one profile
//! (two build scripts, `build_script_build` each) see each other's folder change too, so a note
//! can name a folder its unit does not use: a note may keep a folder longer, never take one.
//! The unit id is the call's `-C extra-filename` (`-<16 hex>`), the name cargo gives the unit's
//! `deps/` artifacts and fingerprint directory, else the id its `--out-dir` names
//! (`build/<pkg>/<id>/out`, `build/<pkg>-<id>`); a call with neither writes no note.
//!
//! **The reader** is the prune: it keeps every folder the note of a unit it judges live names,
//! and every folder of a crate name a live unit with no readable note may have
//! ([`folder_crate`]); see `trust_prune.rs`, "Incremental folders".

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

/// A note's file name before its unit id.
pub(crate) const NOTE_PREFIX: &str = ".trust-unit-";

/// The longest note read: a note names a handful of folders.
const NOTE_MAX: u64 = 64 << 10;

fn is_hex16(text: &str) -> bool {
    text.len() == 16 && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// The crate name of an incremental crate folder's name (`<crate>-<stable crate id>`), or
/// `None` for any other name: a crate name is `[A-Za-z0-9_]+` and the id the compiler's
/// base-36 digits.
pub(crate) fn folder_crate(name: &str) -> Option<&str> {
    let (krate, id) = name.split_once('-')?;
    let word = |text: &str, extra: bool| {
        !text.is_empty() && text.bytes().all(|b| b.is_ascii_alphanumeric() || (extra && b == b'_'))
    };
    (word(krate, true) && word(id, false)).then_some(krate)
}

/// The unit id a note's file name carries, or `None` for any other name.
pub(crate) fn note_unit(name: &str) -> Option<&str> {
    name.strip_prefix(NOTE_PREFIX).filter(|id| is_hex16(id))
}

/// Whether `name` is a note's stage ([`Before::note`]): `<note>.partial-<pid>`.
pub(crate) fn partial_note(name: &str) -> bool {
    name.split_once(".partial-").is_some_and(|(note, pid)| {
        note_unit(note).is_some() && !pid.is_empty() && pid.bytes().all(|b| b.is_ascii_digit())
    })
}

/// The value of the last `-C <key>=<value>` (or `-C<key>=<value>`) of `args`.
pub(crate) fn codegen_value<'a>(args: &'a [OsString], key: &str) -> Option<&'a str> {
    let mut found = None;
    let mut args = args.iter().map(|arg| arg.to_str());
    while let Some(arg) = args.next() {
        let option = match arg {
            Some("-C") => args.next().flatten(),
            Some(arg) => arg.strip_prefix("-C"),
            None => None,
        };
        if let Some(value) = option.and_then(|o| o.strip_prefix(key)?.strip_prefix('=')) {
            found = Some(value);
        }
    }
    found
}

/// The value of the last `<flag> <value>` (or `<flag>=<value>`) of `args`.
fn flag_value<'a>(args: &'a [OsString], flag: &str) -> Option<&'a OsStr> {
    let mut found = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == flag {
            found = iter.next().map(OsString::as_os_str);
        } else if let Some(value) =
            arg.to_str().and_then(|a| a.strip_prefix(flag)?.strip_prefix('='))
        {
            found = Some(OsStr::new(value));
        }
    }
    found
}

/// The id of the unit a compiler call builds: its `-C extra-filename=-<16 hex>`, else the id
/// its `--out-dir` names (`.../build/<pkg>/<id>/out` or `.../build/<pkg>-<id>`).
pub(crate) fn unit_id(args: &[OsString]) -> Option<String> {
    if let Some(id) = codegen_value(args, "extra-filename").and_then(|e| e.strip_prefix('-'))
        && is_hex16(id)
    {
        return Some(id.to_owned());
    }
    let out = Path::new(flag_value(args, "--out-dir")?);
    let name = out.file_name()?.to_str()?;
    if name == "out" {
        let id = out.parent()?.file_name()?.to_str()?;
        return is_hex16(id).then(|| id.to_owned());
    }
    let id = name.get(name.len().checked_sub(16)?..)?;
    (name.len() > 17 && name.as_bytes()[name.len() - 17] == b'-' && is_hex16(id))
        .then(|| id.to_owned())
}

/// What a crate folder is at one moment: its modification time and the names it holds (the
/// compile's session directories).
type Seen = (Option<SystemTime>, BTreeSet<OsString>);

/// The folders of one crate name in one incremental directory before a compile, each as it
/// was ([`Seen`]).
#[derive(Debug)]
pub(crate) struct Before {
    dir: PathBuf,
    unit: String,
    krate: String,
    seen: BTreeMap<String, Seen>,
}

/// The folders of `dir` whose crate name is `krate`, each with its modification time and the
/// names it holds; links and other entries are not folders. A folder that cannot be listed
/// holds no names: one the compile changes still differs by its time or, listed after, by them.
fn folders(dir: &Path, krate: &str) -> io::Result<BTreeMap<String, Seen>> {
    let mut found = BTreeMap::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let Ok(name) = entry.file_name().into_string() else { continue };
        if folder_crate(&name) != Some(krate) {
            continue;
        }
        let meta = fs::symlink_metadata(entry.path())?;
        if meta.file_type().is_dir() {
            let held = fs::read_dir(entry.path())
                .map(|list| list.flatten().map(|inner| inner.file_name()).collect())
                .unwrap_or_default();
            found.insert(name, (meta.modified().ok(), held));
        }
    }
    Ok(found)
}

impl Before {
    /// What a compiler call's incremental directory holds of its crate before it runs: `None`
    /// for a call that compiles nothing incrementally, names no crate or unit, or whose
    /// incremental directory cannot be read (an absent one is empty: the compiler makes it).
    pub(crate) fn read(args: &[OsString]) -> Option<Self> {
        let dir = PathBuf::from(codegen_value(args, "incremental")?);
        let krate = flag_value(args, "--crate-name")?.to_str()?.to_owned();
        let unit = unit_id(args)?;
        let seen = match folders(&dir, &krate) {
            Ok(seen) => seen,
            Err(error) if error.kind() == io::ErrorKind::NotFound => BTreeMap::new(),
            Err(_) => return None,
        };
        Some(Before { dir, unit, krate, seen })
    }

    /// After a compile that succeeded: writes the unit's note naming each folder of its crate
    /// the compile made or changed (its time or its names). Nothing when none changed; an error
    /// leaves the last note and removes the stage it may have begun.
    pub(crate) fn note(&self) -> io::Result<()> {
        let after = folders(&self.dir, &self.krate)?;
        let changed: Vec<&str> = after
            .iter()
            .filter(|(name, seen)| self.seen.get(*name) != Some(seen))
            .map(|(name, _)| name.as_str())
            .collect();
        if changed.is_empty() {
            return Ok(());
        }
        let note = self.dir.join(format!("{NOTE_PREFIX}{}", self.unit));
        let partial =
            self.dir.join(format!("{NOTE_PREFIX}{}.partial-{}", self.unit, std::process::id()));
        let text: String = changed.iter().map(|name| format!("{name}\n")).collect();
        fs::write(&partial, text).and_then(|()| fs::rename(&partial, &note)).inspect_err(|_| {
            let _ = fs::remove_file(&partial);
        })
    }
}

/// The folders a note names. An error for a note that cannot be read, is no regular file, is
/// longer than a note is, or holds a line that is no folder name: its unit counts as one with
/// no note.
pub(crate) fn read_note(path: &Path) -> io::Result<Vec<String>> {
    let invalid = |why: &str| io::Error::new(io::ErrorKind::InvalidData, why.to_owned());
    if !fs::symlink_metadata(path)?.file_type().is_file() {
        return Err(invalid("not a regular file"));
    }
    let mut text = String::new();
    fs::File::open(path)?.take(NOTE_MAX + 1).read_to_string(&mut text)?;
    if text.len() as u64 > NOTE_MAX {
        return Err(invalid("too long"));
    }
    text.lines()
        .map(|line| {
            folder_crate(line).map(|_| line.to_owned()).ok_or_else(|| invalid("not a folder name"))
        })
        .collect()
}
