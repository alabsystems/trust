//! Trust: the receipt a build keeps of the units its compile graph used (DC-12a).
//!
//! When a build's compile graph has run and succeeded, `finish_compilation`
//! (`build_runner/mod.rs`) keeps one receipt for the build's selection at
//! `<build-dir>/.targo-receipts/<name>.json` (`DIR`, `Receipt::name`): when the
//! build began, what it was asked to build, every unit of the build directory
//! the job queue ran, by profile and unit hash, fresh or built, and the bytes
//! of the outputs of the units it compiled. There is one file for each
//! selection: the build of a selection that finishes its graph last replaces
//! the receipt before it, whichever of two overlapping builds
//! (`-Zfine-grain-locking`) began first.
//!
//! WHAT A RECEIPT SAYS: the compile graph finished, and every unit it names is
//! finalized on disk. The command can still fail after that, and the receipt
//! stands: a test that fails, a verification verdict, a cancellation that
//! comes once the compile leases are retired, or a failed write of the final
//! `build-finished` record. A graph that failed keeps no receipt, and the one
//! before stands: the units that build used are still what this selection's
//! last finished graph used.
//!
//! A graph that succeeded but keeps no receipt (no receipt can tell it, or
//! the write failed, as on a full disk) withdraws the one before
//! (`withdraw`): that receipt names what an earlier build of the selection
//! used, not what this one used, and a reader that took it as the
//! selection's newest run could remove a unit this build just used (one an
//! earlier checkout built, found fresh again). With none, a reader knows
//! nothing of the selection's last build, as with a build run as `cargo`.
//! This is the only receipt targo removes. A reader ages the receipts as it
//! ages its own runs, by `began_ms`; targo keeps one file for each selection
//! it ever built and removes none for its age.
//!
//! THE BYTES (`Receipt::encode`) are compact JSON: UTF-8, no whitespace and no
//! trailing newline, with every object's keys and every array in ascending
//! order. The top-level keys are, in that order:
//!
//! * `began_ms`: when the invocation began, in milliseconds since the epoch
//!   (`GlobalContext::invocation_time`). That is earlier than every write the
//!   graph made.
//! * `built`: each profile and the hashes of the units of it that a compiler
//!   (rustc or rustdoc) ran for: dispatched dirty, and not found fresh under
//!   its lock (`compiled`). A build script's run compiles nothing and is never
//!   in it, so `built` names the units of the `compiler-artifact` messages
//!   whose `fresh` is false, the ones aterm's verify counts as compiled. Each of
//!   them is also in `profiles`. A profile with no compiled unit is left out.
//! * `incremental` (DC-12b): each profile and, for each unit of it compiled
//!   incrementally into the profile's `incremental/` folder, its hash and the
//!   crate folders there it uses: the names of the folders its compile wrote,
//!   or, for a unit this build found fresh, the names the kept receipts gave
//!   it (`incremental_trim::folders_of`). Only the compiler names such a
//!   folder (`<crate>-<stable crate id>`), so a name nobody recorded is given
//!   as the bare crate name, which stands for every folder of that crate. The
//!   key is always there, empty where no unit was compiled incrementally: a
//!   receipt without it was written before DC-12b, and its units' folders
//!   are unknown (`incremental_trim`).
//! * `members`: the names of the workspace members whose units the build
//!   used.
//! * `output_bytes`: the bytes of the regular files the compiled units output,
//!   counted as aterm's verify counts the files its compile messages name
//!   (`output_bytes`): one metadata read of each path, a path and (on Unix) a
//!   file counted once. A unit in a shared store counts here too.
//! * `profiles`: each profile, by its path below the build directory (`debug`,
//!   `aarch64-apple-darwin/debug`: plain components joined by `/` on every
//!   platform), and the hashes of every unit of it the queue ran, fresh or
//!   built. A hash is `CompilationFiles::unit_hash`, sixteen lowercase hex
//!   digits, the one in `.fingerprint/<pkg>-<hash>` (`build/<pkg>/<hash>` in
//!   the new layout).
//! * `receipt`: the format, `FORMAT`.
//! * `selection`: what the receipt's name hashes (`Selection`).
//!
//! `began_ms`, `members` and `profiles` have the shape of the run that aterm's
//! DC-03a record holds (`stale::Used`, in aterm's
//! `crates/atpkg/src/build_cache_stale.rs`), and `began_ms` and `profiles` its
//! meaning. `members` names every member the build used, where verify's run
//! names the members it built tests of: in both, the packages whose units a
//! reader may take as superseded. Without targo's own keys a receipt is
//! byte for byte what aterm's encoding of that run gives, and aterm's
//! `Used::of_value`, which reads keys by name, reads a whole receipt as that
//! run. A receipt has no `schema` key, so it is never taken for aterm's
//! `.aterm-used` record. aterm's DC-12d reader is to test the bytes of this
//! module's `FIXTURE`.
//!
//! WHAT IS LEFT OUT. A doctest has no unit in the build directory (no
//! fingerprint, no outputs: rustdoc builds it in a folder of its own), so the
//! receipt does not name it. A unit kept in a shared dependency store lies in
//! no profile of the build directory, so no profile names it, though the bytes
//! it wrote count. A `--compile-time-deps` run never queues the units it
//! skips, and its selection says it was one, so it never replaces a full
//! build's receipt. A build run as `cargo` keeps upstream Cargo's behaviour and
//! keeps no receipt.
//!
//! THE WRITE (`Receipt::keep`) goes to a private file beside the receipt,
//! which is then renamed over the one before. It is not synced: a torn receipt
//! fails to decode, and a reader takes it for none, which supersedes nothing.
//! A write cut short (the process killed) can leave its private
//! `.receipt-*.tmp` file in `DIR`, so a reader reads only the files whose name
//! is sixteen lowercase hex digits and `.json`. A receipt that cannot be named,
//! written or withdrawn changes nothing else about the build (`at_finish`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::hash::Hash;
use std::io::{self, Write as _};
use std::path::{Component, Path, PathBuf};
use std::time::SystemTime;

use serde::Serialize;

use super::CompileMode;
use crate::util::data_structures::HashMap;

/// The folder at the top of the build directory that holds the receipts.
pub(super) const DIR: &str = ".targo-receipts";

/// The receipt's format, its `receipt` key.
pub(super) const FORMAT: u64 = 1;

/// How the queue ran a unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Ran {
    /// The unit was fresh: the build used it and did not compile it.
    Fresh,
    /// The build compiled it.
    Built,
}

/// Each unit the job queue dispatched and how it ran: what it said at
/// dispatch, or, for a dirty unit that turned fresh once it took its lock
/// (`-Zfine-grain-locking`), what the recheck said. Beside it (DC-12b), when
/// each dirty unit was dispatched, and the incremental folders the compile of
/// each built unit wrote (`incremental_trim::written_by`).
pub(super) struct Ledger<K> {
    ran: HashMap<K, Ran>,
    started: HashMap<K, SystemTime>,
    wrote: HashMap<K, BTreeSet<String>>,
}

// Written by hand: a derive would require `K: Default`, which `Unit` is not.
impl<K> Default for Ledger<K> {
    fn default() -> Self {
        Ledger {
            ran: HashMap::default(),
            started: HashMap::default(),
            wrote: HashMap::default(),
        }
    }
}

impl<K: Eq + Hash + Clone> Ledger<K> {
    /// The queue dispatched `unit`, `fresh` or dirty, now.
    pub(super) fn dispatched(&mut self, unit: K, fresh: bool) {
        self.dispatched_at(unit, fresh, SystemTime::now());
    }

    /// The queue dispatched `unit`, `fresh` or dirty, at `at`.
    pub(super) fn dispatched_at(&mut self, unit: K, fresh: bool, at: SystemTime) {
        if fresh {
            self.started.remove(&unit);
        } else {
            self.started.insert(unit.clone(), at);
        }
        self.wrote.remove(&unit);
        self.ran
            .insert(unit, if fresh { Ran::Fresh } else { Ran::Built });
    }

    /// The recheck under its lock found the dirty `unit` fresh: another build
    /// completed it in the meantime, and this build compiled nothing for it.
    pub(super) fn found_fresh(&mut self, unit: K) {
        self.started.remove(&unit);
        self.wrote.remove(&unit);
        self.ran.insert(unit, Ran::Fresh);
    }

    /// When the queue dispatched `unit` to be compiled: `None` for a unit it
    /// did not compile.
    pub(super) fn compiling_since(&self, unit: &K) -> Option<SystemTime> {
        self.started.get(unit).copied()
    }

    /// The compile of `unit` wrote the incremental `folders`.
    pub(super) fn wrote(&mut self, unit: K, folders: BTreeSet<String>) {
        self.wrote.insert(unit, folders);
    }

    /// The incremental folders the compile of `unit` wrote, where noted.
    pub(super) fn folders_written(&self, unit: &K) -> Option<&BTreeSet<String>> {
        self.wrote.get(unit)
    }

    /// Whether the queue dispatched no unit.
    pub(super) fn is_empty(&self) -> bool {
        self.ran.is_empty()
    }

    /// Each unit, and how it ran.
    pub(super) fn iter(&self) -> impl Iterator<Item = (&K, Ran)> {
        self.ran.iter().map(|(unit, ran)| (unit, *ran))
    }
}

/// How the receipt names a unit of compile mode `mode` that the queue ran as
/// `ran`: `None` for a doctest, which has no unit in the build directory (no
/// fingerprint and no outputs), so the receipt leaves it out; else whether
/// the build compiled it, which is whether a compiler (rustc or rustdoc) ran
/// for it. A build script's run compiles nothing, so it is used and never
/// built: cargo names it in no `compiler-artifact` message, and its outputs are
/// no compiler's.
pub(super) fn compiled(mode: CompileMode, ran: Ran) -> Option<bool> {
    match mode {
        CompileMode::Doctest => None,
        CompileMode::RunCustomBuild => Some(false),
        CompileMode::Test
        | CompileMode::Build
        | CompileMode::Check { .. }
        | CompileMode::Doc
        | CompileMode::Docscrape => Some(ran == Ran::Built),
    }
}

/// One unit the build used, as the receipt names it.
pub(super) struct UnitUsed {
    /// Its profile, by its path below the build directory (`profile_of`).
    /// `None` for a unit in a shared store, outside the build directory.
    pub(super) profile: Option<String>,
    /// Its `CompilationFiles::unit_hash`.
    pub(super) hash: String,
    /// The name of its package.
    pub(super) package: String,
    /// Whether its package is a member of the workspace.
    pub(super) member: bool,
    /// Whether the build compiled it (`compiled`).
    pub(super) built: bool,
    /// The files a compiled unit output, as `link_targets` names them in its
    /// `compiler-artifact` message: for each output that is there, its link
    /// where it has one, else the output itself. Empty for a unit the build
    /// did not compile.
    pub(super) outputs: Vec<PathBuf>,
    /// For a unit compiled incrementally into its profile's `incremental/`,
    /// the crate folders there it uses (`incremental_trim::folders_of`): a
    /// folder by its name, `<crate>-<id>`, or, where the folder is unknown,
    /// the bare crate name, which stands for every folder of that crate.
    /// `None` for any other unit.
    pub(super) incremental: Option<BTreeSet<String>>,
}

/// One root unit of a `Selection`. Its package is named by name alone, with
/// no version: a version bump asks for the same build again, so its receipt
/// replaces the one before, and a reader can take the old version's units as
/// superseded. A member's name is unique in its workspace; two versions of one
/// package outside it, both selected (`-p dep@1 -p dep@2`), are one root here,
/// so that build and the build of either version alone share a receipt.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(super) struct Root {
    /// The extra arguments given for this root alone (`targo rustc -- …`),
    /// without the per-run transport (`trust_unit_id`).
    pub(super) args: Vec<String>,
    /// Its features, sorted.
    pub(super) features: Vec<String>,
    /// `host`, or the short name of the target it is compiled for.
    pub(super) kind: String,
    /// Its compile mode (`build`, `check`, `test`, `doc`, …).
    pub(super) mode: String,
    /// The name of its package.
    pub(super) package: String,
    /// Its rustdocflags for a doc or docscrape unit, else its rustflags,
    /// without the per-run transport.
    pub(super) rustflags: Vec<String>,
    /// Its target, as `<kind>:<name>` (`lib:receipt_member`).
    pub(super) target: String,
}

/// What a build was asked to build. The receipt's name hashes it, so the
/// builds of one selection replace each other's receipt and no other's.
/// Beside the roots, the profile and the features, it holds the parts of the
/// command that `compute_metadata` hashes into a unit's id and a person
/// alternates between: each root's flags and extra arguments, and the
/// workspace wrapper. So `targo check` and `targo tippy` keep a receipt each,
/// and a verified run's per-run transport does not make a new file of each
/// run. It does not hold the rest of what that hash reads (a `--config`
/// profile override, `-Zbuild-std`, `__CARGO_DEFAULT_LIB_METADATA`, whether
/// target flags apply to the host): two builds that differ only there share
/// one receipt, and each replaces the other's.
#[derive(Debug, Clone, Serialize)]
pub(super) struct Selection {
    /// Whether the build was a `--compile-time-deps` run.
    pub(super) compile_time_deps_only: bool,
    /// The requested profile (`dev`, `release`, a custom one).
    pub(super) profile: String,
    /// Its root units.
    pub(super) roots: BTreeSet<Root>,
    /// The workspace's root folder.
    pub(super) workspace: String,
    /// The file name of the workspace wrapper (tippy's driver), if any. The
    /// folder it is installed in is left out, so a build with another
    /// toolchain is the same selection; aterm's reader takes the units an old
    /// compiler built by its own rule.
    pub(super) wrapper: Option<String>,
}

impl Selection {
    /// The file name in `DIR` of this selection's receipt: the first sixteen
    /// hex digits of the SHA-256 of its encoding, then `.json`. A build of the
    /// same selection, by any targo on any platform, has the same name.
    ///
    /// # Errors
    /// The encoder failed, which these types never make it do.
    pub(super) fn name(&self) -> io::Result<String> {
        let selection = serde_json::to_vec(self)?;
        let digest = cargo_util::Sha256::new().update(&selection).finish_hex();
        Ok(format!("{}.json", &digest[..16]))
    }
}

/// What a build whose graph succeeded can say of itself (`at_finish`).
#[derive(Debug)]
pub(super) enum Told {
    /// The receipt of the build.
    Receipt(Receipt),
    /// No receipt can tell the build of this selection (`Receipt::new`).
    Untold(Selection),
    /// The build's selection itself cannot be named (a part of it is not
    /// UTF-8). No build of it ever kept a receipt, so none is withdrawn.
    Unnamed,
}

impl From<Result<Receipt, Selection>> for Told {
    fn from(receipt: Result<Receipt, Selection>) -> Told {
        match receipt {
            Ok(receipt) => Told::Receipt(receipt),
            Err(selection) => Told::Untold(selection),
        }
    }
}

/// The receipt of one successful build (the module docs give its bytes).
#[derive(Debug, Serialize)]
pub(super) struct Receipt {
    began_ms: u64,
    built: BTreeMap<String, BTreeSet<String>>,
    incremental: BTreeMap<String, BTreeMap<String, BTreeSet<String>>>,
    members: BTreeSet<String>,
    output_bytes: u64,
    profiles: BTreeMap<String, BTreeSet<String>>,
    receipt: u64,
    selection: Selection,
}

impl Receipt {
    /// The receipt of the build of `selection` that began at `began_ms` and
    /// used `units`. The selection back, as the error, where it would not tell
    /// all of them: no unit lies
    /// in the build directory, a unit there has a profile that is not plain
    /// components joined by `/` or a hash that is not sixteen lowercase hex
    /// digits, or a member's package has no name. aterm's reader takes no part
    /// of a run it cannot read, and a receipt that left a unit out could let a
    /// reader remove a unit this build used.
    ///
    /// # Errors
    /// The receipt would not tell every unit: the error is `selection`, whose
    /// receipt before the caller withdraws (`at_finish`).
    pub(super) fn new(
        began_ms: u64,
        selection: Selection,
        units: Vec<UnitUsed>,
    ) -> Result<Receipt, Selection> {
        let mut built: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut incremental: BTreeMap<String, BTreeMap<String, BTreeSet<String>>> = BTreeMap::new();
        let mut members = BTreeSet::new();
        let mut profiles: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut written = Vec::new();
        for unit in units {
            if unit.member {
                if unit.package.is_empty() {
                    return Err(selection);
                }
                members.insert(unit.package);
            }
            if let Some(profile) = unit.profile {
                if !profile.split('/').all(plain) || !is_hash(&unit.hash) {
                    return Err(selection);
                }
                // Trust: DC-12b. A folder the receipt cannot name could be
                // trimmed while this unit uses it.
                if let Some(folders) = unit.incremental {
                    if !folders.iter().all(|folder| is_folder_or_crate(folder)) {
                        return Err(selection);
                    }
                    incremental
                        .entry(profile.clone())
                        .or_default()
                        .insert(unit.hash.clone(), folders);
                }
                if unit.built {
                    built
                        .entry(profile.clone())
                        .or_default()
                        .insert(unit.hash.clone());
                }
                profiles.entry(profile).or_default().insert(unit.hash);
            }
            if unit.built {
                written.extend(unit.outputs);
            }
        }
        if profiles.is_empty() {
            return Err(selection);
        }
        Ok(Receipt {
            began_ms,
            built,
            incremental,
            members,
            output_bytes: output_bytes(&written),
            profiles,
            receipt: FORMAT,
            selection,
        })
    }

    /// The receipt's bytes (the module docs give them).
    ///
    /// # Errors
    /// The encoder failed, which these types never make it do.
    pub(super) fn encode(&self) -> io::Result<Vec<u8>> {
        Ok(serde_json::to_vec(self)?)
    }

    /// The receipt's file name in `DIR`, its selection's (`Selection::name`).
    ///
    /// # Errors
    /// The encoder failed, which these types never make it do.
    pub(super) fn name(&self) -> io::Result<String> {
        self.selection.name()
    }

    /// Keep the receipt in the build directory `build_dir`, which must exist:
    /// `DIR` is made there if it is not there, and the receipt is written to a
    /// private file in it and renamed over the one before. The rename replaces
    /// the file that has the receipt's name, a symlink included, and never
    /// writes through it; it replaces no directory. Returns the receipt's path.
    ///
    /// # Errors
    /// The build directory is not there, `DIR` is no directory (a symlink to
    /// one included), or a write or the rename failed (a directory with the
    /// receipt's name among them): the receipt before stands, and the private
    /// file is removed.
    pub(super) fn keep(&self, build_dir: &Path) -> io::Result<PathBuf> {
        let bytes = self.encode()?;
        let dir = build_dir.join(DIR);
        let path = dir.join(self.name()?);
        match fs::create_dir(&dir) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
        if !fs::symlink_metadata(&dir)?.file_type().is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::NotADirectory,
                format!("`{}` is not a directory", dir.display()),
            ));
        }
        let mut staged = tempfile::Builder::new()
            .prefix(".receipt-")
            .suffix(".tmp")
            .tempfile_in(&dir)?;
        staged.write_all(&bytes)?;
        // Dropping the error drops the private file with it, which removes it.
        staged.persist(&path).map_err(|error| error.error)?;
        Ok(path)
    }
}

/// What became of a build's receipt (`at_finish`).
#[derive(Debug)]
pub(super) enum Receipted {
    /// The graph did not succeed, so the receipt before stands.
    Failed,
    /// The build's selection cannot be named, so no receipt is of it.
    Unnamed,
    /// No receipt could tell this build (`Receipt::new`); `withdrawn` is
    /// what became of the receipt before (`withdraw`).
    Unstated { withdrawn: io::Result<()> },
    /// The receipt is at this path.
    Written(PathBuf),
    /// The receipt could not be written (`Receipt::keep`); `withdrawn` is
    /// what became of the receipt before (`withdraw`).
    NotWritten {
        error: io::Error,
        withdrawn: io::Result<()>,
    },
}

impl fmt::Display for Receipted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let before = |f: &mut fmt::Formatter<'_>, withdrawn: &io::Result<()>| match withdrawn {
            Ok(()) => f.write_str(", the one before withdrawn"),
            Err(error) => write!(f, ", the one before not withdrawn: {error}"),
        };
        match self {
            Receipted::Failed => f.write_str("none, the graph did not succeed"),
            Receipted::Unnamed => f.write_str("none, the selection has no name"),
            Receipted::Unstated { withdrawn } => {
                f.write_str("none, no receipt can tell this build")?;
                before(f, withdrawn)
            }
            Receipted::Written(path) => write!(f, "written to {}", path.display()),
            Receipted::NotWritten { error, withdrawn } => {
                write!(f, "not written: {error}")?;
                before(f, withdrawn)
            }
        }
    }
}

/// THE END OF A BUILD'S GRAPH: where it succeeded (`graph_succeeded`), keep the
/// receipt `of` tells in the build directory `build_dir`, or, where it tells
/// none or the write fails, withdraw the selection's receipt before. `of` is
/// not called for a failed graph, and the receipt before stands. This returns
/// no error and never panics, so nothing here can change the build's result or
/// what it printed; the caller only records the outcome.
pub(super) fn at_finish(
    graph_succeeded: bool,
    build_dir: &Path,
    of: impl FnOnce() -> Told,
) -> Receipted {
    finish_with(graph_succeeded, build_dir, of, Receipt::keep)
}

/// `at_finish`, with the write `keep` in place of `Receipt::keep`, so a test
/// can fail it as a full disk does.
fn finish_with(
    graph_succeeded: bool,
    build_dir: &Path,
    of: impl FnOnce() -> Told,
    keep: impl FnOnce(&Receipt, &Path) -> io::Result<PathBuf>,
) -> Receipted {
    if !graph_succeeded {
        return Receipted::Failed;
    }
    match of() {
        Told::Unnamed => Receipted::Unnamed,
        Told::Untold(selection) => Receipted::Unstated {
            withdrawn: withdraw(build_dir, &selection),
        },
        Told::Receipt(receipt) => match keep(&receipt, build_dir) {
            Ok(path) => Receipted::Written(path),
            Err(error) => Receipted::NotWritten {
                error,
                withdrawn: withdraw(build_dir, &receipt.selection),
            },
        },
    }
}

/// Withdraw the receipt of `selection` from the build directory `build_dir`,
/// where a build of it succeeded and kept none (the module docs give why).
/// Only a file or symlink at the receipt's name in a `DIR` that is a real
/// folder is removed: never a folder, and nothing through a `DIR` that is a
/// symlink, which `Receipt::keep` never writes through either. A receipt that
/// is not there is withdrawn already.
///
/// # Errors
/// The receipt is there and could not be removed, or `DIR` or the receipt's
/// name could not be read: the receipt before may stand.
fn withdraw(build_dir: &Path, selection: &Selection) -> io::Result<()> {
    let absent = |result: io::Result<()>| match result {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        result => result,
    };
    let dir = build_dir.join(DIR);
    match fs::symlink_metadata(&dir) {
        Ok(meta) if meta.file_type().is_dir() => {}
        Ok(_) => return Ok(()),
        Err(error) => return absent(Err(error)),
    }
    let path = dir.join(selection.name()?);
    match fs::symlink_metadata(&path) {
        Ok(meta) if meta.file_type().is_dir() => Ok(()),
        Ok(_) => absent(fs::remove_file(&path)),
        Err(error) => absent(Err(error)),
    }
}

/// The profile of the profile folder `profile_dir` (`<build-dir>[/<target>]/<profile>`)
/// of the build directory `build_root`: its path below `build_root`, its
/// components joined by `/` on every platform. `None` for a folder outside
/// `build_root` or `build_root` itself, or a path with a component that is not
/// plain UTF-8.
pub(super) fn profile_of(build_root: &Path, profile_dir: &Path) -> Option<String> {
    let below = profile_dir.strip_prefix(build_root).ok()?;
    let parts = below
        .components()
        .map(|part| match part {
            Component::Normal(part) => part.to_str().filter(|part| plain(part)),
            _ => None,
        })
        .collect::<Option<Vec<&str>>>()?;
    (!parts.is_empty()).then(|| parts.join("/"))
}

/// Whether `word` is one plain path component: not empty, not `.` or `..`,
/// and holding no separator (aterm's `plain`).
pub(super) fn plain(word: &str) -> bool {
    !word.is_empty() && word != "." && word != ".." && !word.contains(['/', '\\'])
}

/// The crate of `name` where it is an incremental crate folder's name as the
/// compiler makes it, `<crate>-<id>` (`crate_path` in
/// `compiler/rustc_incremental/src/persist/fs.rs`): a crate name, which holds
/// no `-`, then `-` and the stable crate id in ASCII letters and digits.
pub(super) fn crate_of_folder(name: &str) -> Option<&str> {
    let (krate, id) = name.split_once('-')?;
    (is_crate(krate) && !id.is_empty() && id.bytes().all(|byte| byte.is_ascii_alphanumeric()))
        .then_some(krate)
}

/// Whether `word` is a crate name as a folder name holds it: a plain
/// component with no `-` and no `.` (a crate name is an identifier).
pub(super) fn is_crate(word: &str) -> bool {
    plain(word) && !word.contains(['-', '.'])
}

/// Whether `word` is what a receipt's `incremental` key may name: a crate
/// folder (`crate_of_folder`) or a bare crate name (`is_crate`).
pub(super) fn is_folder_or_crate(word: &str) -> bool {
    crate_of_folder(word).is_some() || is_crate(word)
}

/// Whether `word` is a unit's hash: sixteen lowercase hex digits (aterm's
/// `is_hash`).
pub(super) fn is_hash(word: &str) -> bool {
    word.len() == 16
        && word
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
}

/// The bytes the regular files at `files` hold, as aterm's verify counts the
/// files its compile messages name (`output_bytes` in aterm's
/// `crates/aterm-verify/src/compile_account.rs`): one `symlink_metadata` of
/// each, a path read once and, on Unix, a file (device and inode) counted
/// once, so an output hard-linked beside its `deps/` copy is not counted
/// twice. A directory (a `.dSYM`), a symlink and a path that is gone add
/// nothing, and nothing is walked.
fn output_bytes(files: &[PathBuf]) -> u64 {
    let mut paths = BTreeSet::<&Path>::new();
    #[cfg(unix)]
    let mut inodes = BTreeSet::<(u64, u64)>::new();
    let mut total = 0_u64;
    for file in files {
        if !paths.insert(file) {
            continue;
        }
        let Ok(meta) = fs::symlink_metadata(file) else {
            continue;
        };
        if !meta.file_type().is_file() {
            continue;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            if !inodes.insert((meta.dev(), meta.ino())) {
                continue;
            }
        }
        total = total.saturating_add(meta.len());
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The receipt of the build `queue` records, whose files `write_outputs`
    /// writes. aterm's DC-12d reader is to test the same 493 bytes, in aterm's
    /// `crates/atpkg/src/build_cache_stale_tests.rs`.
    const FIXTURE: &[u8] = br#"{"began_ms":1794528000000,"built":{"debug":["1111111111111111"]},"incremental":{},"members":["receipt-member"],"output_bytes":4096,"profiles":{"aarch64-apple-darwin/debug":["3333333333333333"],"debug":["1111111111111111","2222222222222222"]},"receipt":1,"selection":{"compile_time_deps_only":false,"profile":"dev","roots":[{"args":[],"features":["default"],"kind":"host","mode":"build","package":"receipt-member","rustflags":[],"target":"lib:receipt_member"}],"workspace":"/w","wrapper":null}}"#;

    /// What aterm's `Used` encodes for the same run: `FIXTURE` without
    /// targo's own five keys.
    const USED: &[u8] = br#"{"began_ms":1794528000000,"members":["receipt-member"],"profiles":{"aarch64-apple-darwin/debug":["3333333333333333"],"debug":["1111111111111111","2222222222222222"]}}"#;

    /// The receipt name of `selection("receipt-member")`.
    const NAME: &str = "a5fb627b7bb345bb.json";

    const BEGAN_MS: u64 = 1_794_528_000_000;
    /// The member's library, which the build compiled.
    const MEMBER: &str = "1111111111111111";
    /// A dependency the queue dispatched dirty and found fresh under its lock.
    const DEPENDENCY: &str = "2222222222222222";
    /// The member's unit for another target, fresh.
    const CROSS: &str = "3333333333333333";

    /// A private build directory under the system's temporary folder.
    fn scratch() -> tempfile::TempDir {
        let base = std::env::temp_dir()
            .join(".ubd")
            .join("targo-build-receipt.noindex");
        fs::create_dir_all(&base).unwrap();
        tempfile::Builder::new()
            .prefix("build-")
            .tempdir_in(base)
            .unwrap()
    }

    /// A build of `package`'s library, on the host, in the dev profile.
    fn selection(package: &str) -> Selection {
        Selection {
            compile_time_deps_only: false,
            profile: "dev".to_owned(),
            roots: BTreeSet::from([Root {
                args: Vec::new(),
                features: vec!["default".to_owned()],
                kind: "host".to_owned(),
                mode: "build".to_owned(),
                package: package.to_owned(),
                rustflags: Vec::new(),
                target: format!("lib:{}", package.replace('-', "_")),
            }]),
            workspace: "/w".to_owned(),
            wrapper: None,
        }
    }

    /// The fixture's queue: the member's library dispatched dirty and built,
    /// the dependency dispatched dirty and found fresh once it took its lock,
    /// the member's other unit dispatched fresh.
    fn queue() -> Ledger<&'static str> {
        let mut ran = Ledger::default();
        ran.dispatched(MEMBER, false);
        ran.dispatched(DEPENDENCY, false);
        ran.found_fresh(DEPENDENCY);
        ran.dispatched(CROSS, true);
        ran
    }

    /// The files the member's library and the dependency output.
    struct Outputs {
        member: Vec<PathBuf>,
        dependency: Vec<PathBuf>,
    }

    /// Write the fixture's outputs under the build directory `dir`. The
    /// member's: an rlib of 3000 bytes and an rmeta of 1096, the rlib named
    /// twice, a `.dSYM` folder, a path that is gone and, on Unix, a hard link
    /// to the rlib and a symlink to it, so they count 4096 bytes. The
    /// dependency's: one file of 5000 bytes.
    fn write_outputs(dir: &Path) -> Outputs {
        let deps = dir.join("debug").join("deps");
        fs::create_dir_all(&deps).unwrap();
        let rlib = deps.join("libreceipt_member-1111111111111111.rlib");
        fs::write(&rlib, vec![0_u8; 3000]).unwrap();
        let rmeta = deps.join("libreceipt_member-1111111111111111.rmeta");
        fs::write(&rmeta, vec![0_u8; 1096]).unwrap();
        let dsym = deps.join("receipt_member-1111111111111111.dSYM");
        fs::create_dir(&dsym).unwrap();
        #[cfg_attr(not(unix), allow(unused_mut))]
        let mut member = vec![
            rlib.clone(),
            rmeta,
            rlib.clone(),
            dsym,
            deps.join("receipt_member-1111111111111111.gone"),
        ];
        #[cfg(unix)]
        {
            let link = dir.join("debug").join("libreceipt_member.rlib");
            fs::hard_link(&rlib, &link).unwrap();
            let symlink = dir.join("debug").join("libreceipt_member.symlink");
            std::os::unix::fs::symlink(&rlib, &symlink).unwrap();
            member.extend([link, symlink]);
        }
        let dependency = deps.join("libreceipt_dep-2222222222222222.rlib");
        fs::write(&dependency, vec![0_u8; 5000]).unwrap();
        Outputs {
            member,
            dependency: vec![dependency],
        }
    }

    /// The units `queue` ran, all libraries compiled in `CompileMode::Build`,
    /// as `BuildRunner::receipt_of` names them: each in its profile of the
    /// build directory `dir`, with the files of the compiled ones. The tests in
    /// `src/tools/targo/tests/build_receipt.rs` hold `receipt_of` itself to a
    /// real build.
    fn units(dir: &Path, queue: &Ledger<&'static str>, outputs: &Outputs) -> Vec<UnitUsed> {
        let host = profile_of(dir, &dir.join("debug")).unwrap();
        let cross = profile_of(dir, &dir.join("aarch64-apple-darwin").join("debug")).unwrap();
        queue
            .iter()
            .map(|(&hash, ran)| {
                let (profile, package, member, files) = match hash {
                    MEMBER => (host.clone(), "receipt-member", true, outputs.member.clone()),
                    DEPENDENCY => (
                        host.clone(),
                        "receipt-dep",
                        false,
                        outputs.dependency.clone(),
                    ),
                    _ => (cross.clone(), "receipt-member", true, Vec::new()),
                };
                let built = compiled(CompileMode::Build, ran).unwrap();
                UnitUsed {
                    profile: Some(profile),
                    hash: hash.to_owned(),
                    package: package.to_owned(),
                    member,
                    built,
                    outputs: if built { files } else { Vec::new() },
                    incremental: None,
                }
            })
            .collect()
    }

    /// A receipt of `selection("receipt-member")` with one compiled unit, of a
    /// build that began at `began_ms`.
    fn receipt(began_ms: u64) -> Receipt {
        let unit = UnitUsed {
            profile: Some("debug".to_owned()),
            hash: MEMBER.to_owned(),
            package: "receipt-member".to_owned(),
            member: true,
            built: true,
            outputs: Vec::new(),
            incremental: None,
        };
        Receipt::new(began_ms, selection("receipt-member"), vec![unit]).unwrap()
    }

    /// The names in the folder `dir`, sorted.
    fn entries(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect();
        names.sort();
        names
    }

    /// Whether `run` holds a run as aterm's `Used::of_value` reads one: a
    /// `began_ms` that is a u64, `members` an array of non-empty strings, and
    /// `profiles` an object whose keys are plain components joined by `/`,
    /// each an array of unit hashes.
    fn reads_as_used(run: &serde_json::Value) -> bool {
        let began = run
            .get("began_ms")
            .and_then(serde_json::Value::as_u64)
            .is_some();
        let members = run
            .get("members")
            .and_then(serde_json::Value::as_array)
            .is_some_and(|members| {
                members
                    .iter()
                    .all(|member| member.as_str().is_some_and(|member| !member.is_empty()))
            });
        let profiles = run
            .get("profiles")
            .and_then(serde_json::Value::as_object)
            .is_some_and(|profiles| {
                profiles.iter().all(|(name, hashes)| {
                    name.split('/').all(plain)
                        && hashes.as_array().is_some_and(|hashes| {
                            hashes
                                .iter()
                                .all(|hash| hash.as_str().is_some_and(is_hash))
                        })
                })
            });
        began && members && profiles
    }

    /// The keys aterm's `Used` encodes, in its order.
    #[derive(Serialize)]
    struct UsedKeys<'a> {
        began_ms: &'a serde_json::Value,
        members: &'a serde_json::Value,
        profiles: &'a serde_json::Value,
    }

    /// A build whose graph succeeded keeps one receipt of its selection, at
    /// `.targo-receipts/a5fb627b7bb345bb.json`, and nothing else: exactly the
    /// bytes of `FIXTURE`, whose selection names its root's package with no
    /// version, so a version bump asks for the same selection. It names every
    /// unit its queue ran in its profile, fresh or built, the dependency the
    /// recheck under its lock found fresh as fresh. It counts the bytes of the
    /// compiled unit's files once each, with no directory, symlink, missing
    /// path or second name of a file among them. Its three shared keys are
    /// what aterm's `Used` reads and encodes, and a build of another selection
    /// keeps a second receipt beside the first. Of the units the queue runs, a
    /// doctest is not named, a build script's run is named and never built,
    /// and a unit of any other mode is built where it was not fresh.
    ///
    /// Negative controls: without the recheck's answer (`found_fresh`) the
    /// dependency counts as built, so the bytes come to 9096 and the receipt
    /// differs from `FIXTURE`; so does one that leaves the dependency out. A
    /// compiled unit in a shared store adds its 100 bytes and nothing else.
    /// No receipt is made of a unit with an uppercase hash or a profile that
    /// climbs out of the build directory, of a member with no name, of no
    /// unit, or of a shared unit alone, and a folder outside the build
    /// directory has no profile. A build whose graph succeeded but that no
    /// receipt can tell withdraws its selection's receipt before, which names
    /// another build's units, and leaves the other selection's; one whose
    /// selection has no name withdraws nothing.
    #[test]
    fn a_finished_build_writes_a_receipt_of_every_unit_it_used_and_the_bytes_it_wrote() {
        assert_eq!(compiled(CompileMode::Doctest, Ran::Built), None);
        assert_eq!(compiled(CompileMode::Doctest, Ran::Fresh), None);
        assert_eq!(compiled(CompileMode::RunCustomBuild, Ran::Built), Some(false));
        assert_eq!(compiled(CompileMode::RunCustomBuild, Ran::Fresh), Some(false));
        for mode in [
            CompileMode::Build,
            CompileMode::Test,
            CompileMode::Check { test: false },
            CompileMode::Check { test: true },
            CompileMode::Doc,
            CompileMode::Docscrape,
        ] {
            assert_eq!(compiled(mode, Ran::Built), Some(true), "{mode:?}");
            assert_eq!(compiled(mode, Ran::Fresh), Some(false), "{mode:?}");
        }

        let build = scratch();
        let dir = build.path();
        assert_eq!(profile_of(dir, &dir.join("debug")).as_deref(), Some("debug"));
        assert_eq!(
            profile_of(dir, &dir.join("aarch64-apple-darwin").join("debug")).as_deref(),
            Some("aarch64-apple-darwin/debug")
        );
        let outputs = write_outputs(dir);

        let receipted = at_finish(true, dir, || {
            Receipt::new(
                BEGAN_MS,
                selection("receipt-member"),
                units(dir, &queue(), &outputs),
            )
            .into()
        });
        let receipts = dir.join(DIR);
        let path = receipts.join(NAME);
        assert!(
            matches!(&receipted, Receipted::Written(written) if *written == path),
            "{receipted:?}"
        );
        let bytes = fs::read(&path).unwrap();
        assert_eq!(FIXTURE.len(), 493);
        assert_eq!(
            String::from_utf8_lossy(&bytes),
            String::from_utf8_lossy(FIXTURE)
        );
        assert_eq!(entries(&receipts), [NAME]);

        let run: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert!(run.get("schema").is_none());
        assert!(reads_as_used(&run), "{run}");
        let used = serde_json::to_vec(&UsedKeys {
            began_ms: &run["began_ms"],
            members: &run["members"],
            profiles: &run["profiles"],
        })
        .unwrap();
        assert_eq!(String::from_utf8_lossy(&used), String::from_utf8_lossy(USED));

        let other = match at_finish(true, dir, || {
            Receipt::new(
                BEGAN_MS,
                selection("receipt-other"),
                units(dir, &queue(), &outputs),
            )
            .into()
        }) {
            Receipted::Written(other) => other,
            receipted => panic!("{receipted:?}"),
        };
        assert_ne!(other, path);
        assert_eq!(fs::read(&path).unwrap(), FIXTURE);
        assert_eq!(entries(&receipts).len(), 2);

        // Negative control: the recheck's answer removed.
        let mut unchecked = Ledger::default();
        unchecked.dispatched(MEMBER, false);
        unchecked.dispatched(DEPENDENCY, false);
        unchecked.dispatched(CROSS, true);
        let receipt = Receipt::new(
            BEGAN_MS,
            selection("receipt-member"),
            units(dir, &unchecked, &outputs),
        )
        .unwrap();
        assert_eq!(receipt.output_bytes, 9096);
        assert_ne!(receipt.encode().unwrap(), FIXTURE);

        // Negative control: a unit the queue ran left out.
        let mut without = units(dir, &queue(), &outputs);
        without.retain(|unit| unit.hash != DEPENDENCY);
        let receipt = Receipt::new(BEGAN_MS, selection("receipt-member"), without).unwrap();
        assert_ne!(receipt.encode().unwrap(), FIXTURE);

        // A compiled unit in a shared store: its bytes count, no profile
        // names it.
        let store = scratch();
        let stored = store.path().join("libreceipt_shared-4444444444444444.rlib");
        fs::write(&stored, vec![0_u8; 100]).unwrap();
        let shared = || UnitUsed {
            profile: None,
            hash: "4444444444444444".to_owned(),
            package: "receipt-shared".to_owned(),
            member: false,
            built: true,
            outputs: vec![stored.clone()],
            incremental: None,
        };
        let mut with_shared = units(dir, &queue(), &outputs);
        with_shared.push(shared());
        let with_shared =
            Receipt::new(BEGAN_MS, selection("receipt-member"), with_shared).unwrap();
        let unshared = Receipt::new(
            BEGAN_MS,
            selection("receipt-member"),
            units(dir, &queue(), &outputs),
        )
        .unwrap();
        assert_eq!(with_shared.profiles, unshared.profiles);
        assert_eq!(with_shared.built, unshared.built);
        assert_eq!(with_shared.members, unshared.members);
        assert_eq!(unshared.output_bytes, 4096);
        assert_eq!(with_shared.output_bytes, 4196);

        // What cannot be named keeps no receipt.
        let mut uppercase = units(dir, &queue(), &outputs);
        uppercase[0].hash = "ABCDEF0123456789".to_owned();
        assert!(Receipt::new(BEGAN_MS, selection("receipt-member"), uppercase).is_err());
        let mut climbing = units(dir, &queue(), &outputs);
        climbing[0].profile = Some("../debug".to_owned());
        assert!(Receipt::new(BEGAN_MS, selection("receipt-member"), climbing).is_err());
        let mut nameless = units(dir, &queue(), &outputs);
        nameless
            .iter_mut()
            .find(|unit| unit.member)
            .unwrap()
            .package
            .clear();
        assert!(Receipt::new(BEGAN_MS, selection("receipt-member"), nameless).is_err());
        assert!(Receipt::new(BEGAN_MS, selection("receipt-member"), Vec::new()).is_err());
        assert!(Receipt::new(BEGAN_MS, selection("receipt-member"), vec![shared()]).is_err());
        assert_eq!(profile_of(dir, store.path()), None);
        assert_eq!(profile_of(dir, dir), None);

        // A build of a selection whose graph succeeded with no receipt that
        // can tell it withdraws that selection's receipt before, and no other.
        // A selection with no name withdraws nothing.
        let other_name = other.file_name().unwrap().to_str().unwrap().to_owned();
        let receipted = at_finish(true, dir, || Told::Unnamed);
        assert!(matches!(receipted, Receipted::Unnamed), "{receipted:?}");
        assert_eq!(fs::read(&path).unwrap(), FIXTURE);
        let mut uppercase = units(dir, &queue(), &outputs);
        uppercase[0].hash = "ABCDEF0123456789".to_owned();
        let receipted = at_finish(true, dir, || {
            Receipt::new(BEGAN_MS, selection("receipt-member"), uppercase).into()
        });
        assert!(
            matches!(receipted, Receipted::Unstated { withdrawn: Ok(()) }),
            "{receipted:?}"
        );
        assert_eq!(entries(&receipts), [other_name.clone()]);
        let receipted = at_finish(true, dir, || Told::Untold(selection("receipt-member")));
        assert!(
            matches!(receipted, Receipted::Unstated { withdrawn: Ok(()) }),
            "{receipted:?}"
        );
        assert_eq!(entries(&receipts), [other_name]);
    }

    /// A build whose graph failed keeps no receipt, never asks what it used,
    /// and leaves the receipt of the build before it as it was.
    ///
    /// Negative control: the same build succeeding replaces that receipt with
    /// its own, while a hard link to the one before still reads the earlier
    /// bytes, so the receipt was written aside and renamed over the one
    /// before, never written into it. On Unix, a symlink standing at the
    /// receipt's name is replaced by the receipt, and the file it pointed to
    /// keeps its bytes.
    #[test]
    fn a_failed_build_leaves_the_receipt_before_it() {
        let build = scratch();
        let dir = build.path();
        let before = receipt(BEGAN_MS);
        let earlier = before.encode().unwrap();
        let path = before.keep(dir).unwrap();
        let link = dir.join("a-link");
        fs::hard_link(&path, &link).unwrap();
        let later = receipt(BEGAN_MS + 1).encode().unwrap();
        assert_ne!(earlier, later);

        let mut asked = false;
        let receipted = at_finish(false, dir, || {
            asked = true;
            Told::Receipt(receipt(BEGAN_MS + 1))
        });
        assert!(matches!(receipted, Receipted::Failed), "{receipted:?}");
        assert!(!asked, "a failed graph's units were read");
        assert_eq!(fs::read(&path).unwrap(), earlier);
        assert_eq!(entries(&dir.join(DIR)), [NAME]);

        // Negative control: the build succeeds.
        let receipted = at_finish(true, dir, || Told::Receipt(receipt(BEGAN_MS + 1)));
        assert!(
            matches!(&receipted, Receipted::Written(written) if *written == path),
            "{receipted:?}"
        );
        assert_eq!(fs::read(&path).unwrap(), later);
        assert_eq!(fs::read(&link).unwrap(), earlier);
        assert_eq!(entries(&dir.join(DIR)), [NAME]);

        // A symlink at the receipt's name is replaced, never written through.
        #[cfg(unix)]
        {
            let outside = dir.join("outside");
            fs::write(&outside, b"outside").unwrap();
            fs::remove_file(&path).unwrap();
            std::os::unix::fs::symlink(&outside, &path).unwrap();
            let receipted = at_finish(true, dir, || Told::Receipt(receipt(BEGAN_MS + 2)));
            assert!(
                matches!(&receipted, Receipted::Written(written) if *written == path),
                "{receipted:?}"
            );
            assert_eq!(fs::read(&outside).unwrap(), b"outside");
            assert!(fs::symlink_metadata(&path).unwrap().file_type().is_file());
            assert_eq!(
                fs::read(&path).unwrap(),
                receipt(BEGAN_MS + 2).encode().unwrap()
            );
            assert_eq!(entries(&dir.join(DIR)), [NAME]);
        }
    }

    /// A receipt that cannot be written is an outcome, not an error: with a
    /// file where the receipts' folder goes, a folder where the receipt goes
    /// or, on Unix, a symlink to a folder elsewhere where the receipts' folder
    /// goes, `at_finish` returns `NotWritten`, a value with no `Result` to
    /// propagate (the `let receipted: Receipted` bindings stop compiling if it
    /// ever returns one), and leaves what was there as it was, its private
    /// file removed and nothing else touched, nothing written or removed
    /// through the symlink among it. A write that fails as on a full disk,
    /// where the selection's receipt before stands, withdraws that receipt,
    /// which names another build's units, and leaves the other selection's.
    ///
    /// Negative controls: the same call in an empty build directory writes the
    /// receipt; the same failed write after a graph that failed leaves the
    /// receipt before as it was.
    #[test]
    fn a_receipt_that_cannot_be_written_never_fails_the_build() {
        let withdrew = |receipted: &Receipted| {
            matches!(
                receipted,
                Receipted::NotWritten {
                    withdrawn: Ok(()),
                    ..
                }
            )
        };
        let build = scratch();
        let dir = build.path();
        let blocker = dir.join(DIR);
        fs::write(&blocker, b"not a folder").unwrap();
        let receipted: Receipted = at_finish(true, dir, || Told::Receipt(receipt(BEGAN_MS)));
        assert!(withdrew(&receipted), "{receipted:?}");
        assert_eq!(fs::read(&blocker).unwrap(), b"not a folder");
        assert_eq!(entries(dir), [DIR]);

        let build = scratch();
        let dir = build.path();
        let taken = dir.join(DIR).join(NAME);
        fs::create_dir_all(&taken).unwrap();
        fs::write(taken.join("kept"), b"kept").unwrap();
        let receipted: Receipted = at_finish(true, dir, || Told::Receipt(receipt(BEGAN_MS)));
        assert!(withdrew(&receipted), "{receipted:?}");
        assert_eq!(entries(&dir.join(DIR)), [NAME]);
        assert_eq!(entries(&taken), ["kept"]);
        assert_eq!(fs::read(taken.join("kept")).unwrap(), b"kept");

        #[cfg(unix)]
        {
            let build = scratch();
            let elsewhere = scratch();
            fs::write(elsewhere.path().join(NAME), b"elsewhere").unwrap();
            std::os::unix::fs::symlink(elsewhere.path(), build.path().join(DIR)).unwrap();
            let receipted: Receipted =
                at_finish(true, build.path(), || Told::Receipt(receipt(BEGAN_MS)));
            assert!(withdrew(&receipted), "{receipted:?}");
            assert_eq!(entries(elsewhere.path()), [NAME]);
            assert_eq!(fs::read(elsewhere.path().join(NAME)).unwrap(), b"elsewhere");
            assert_eq!(entries(build.path()), [DIR]);
        }

        // A full disk: the receipt before is withdrawn, the other kept.
        let build = scratch();
        let dir = build.path();
        let before = receipt(BEGAN_MS).keep(dir).unwrap();
        let other = Receipt::new(BEGAN_MS, selection("receipt-other"), {
            let unit = UnitUsed {
                profile: Some("debug".to_owned()),
                hash: MEMBER.to_owned(),
                package: "receipt-other".to_owned(),
                member: true,
                built: false,
                outputs: Vec::new(),
                incremental: None,
            };
            vec![unit]
        })
        .unwrap()
        .keep(dir)
        .unwrap();
        let full = |_: &Receipt, _: &Path| -> io::Result<PathBuf> {
            Err(io::Error::new(
                io::ErrorKind::StorageFull,
                "no space left on device",
            ))
        };
        // Negative control: a graph that failed leaves it.
        let receipted = finish_with(false, dir, || Told::Receipt(receipt(BEGAN_MS + 1)), full);
        assert!(matches!(receipted, Receipted::Failed), "{receipted:?}");
        assert_eq!(
            fs::read(&before).unwrap(),
            receipt(BEGAN_MS).encode().unwrap()
        );
        let receipted: Receipted =
            finish_with(true, dir, || Told::Receipt(receipt(BEGAN_MS + 1)), full);
        assert!(
            matches!(
                &receipted,
                Receipted::NotWritten { error, withdrawn: Ok(()) }
                    if error.kind() == io::ErrorKind::StorageFull
            ),
            "{receipted:?}"
        );
        assert!(!before.exists());
        assert_eq!(
            entries(&dir.join(DIR)),
            [other.file_name().unwrap().to_str().unwrap()]
        );

        // Negative control: nothing in the way.
        let build = scratch();
        let dir = build.path();
        let receipted: Receipted = at_finish(true, dir, || Told::Receipt(receipt(BEGAN_MS)));
        assert!(
            matches!(&receipted, Receipted::Written(path) if *path == dir.join(DIR).join(NAME)),
            "{receipted:?}"
        );
        assert_eq!(entries(&dir.join(DIR)), [NAME]);
    }
}
