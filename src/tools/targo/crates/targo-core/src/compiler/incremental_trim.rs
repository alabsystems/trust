//! Trust: the incremental folders a build directory keeps (DC-12b).
//!
//! The compiler keeps a crate's incremental state in one folder of the
//! profile's `incremental/` (`BuildDirLayout::incremental`), named
//! `<crate>-<stable crate id>` (`crate_path` in
//! `compiler/rustc_incremental/src/persist/fs.rs`), and collects old sessions
//! only inside the folder it is using (`garbage_collect_session_directories`).
//! A unit's new variant (a feature, a flag, a dependency's version) gets a new
//! stable crate id and so a new folder, and the old variant's folder stays for
//! good. This module removes those folders when a build ends.
//!
//! THE LINK from a unit to its folder is the one the compile made: only the
//! compiler derives the folder's name, so targo notes, when the compile of a
//! unit ends, the folders named for the unit's crate that changed since the
//! queue dispatched it (`written_by`). Each new session the compiler starts
//! and finalizes writes the crate folder, the second time as the compile
//! ends, so the folder the compile used is among them. Another unit of the
//! same crate name compiled at the same time (a library and its test), or a
//! folder written within `WRITE_SLACK` before the dispatch, can be noted too;
//! that keeps a folder longer and never removes one. Where none is found, the
//! compile's folder is unknown, and the receipt names the bare crate, which
//! keeps every folder of that crate. A unit found fresh writes nothing, yet
//! its next edit needs its folder, so its receipt carries forward what the
//! kept receipts said of it (`folders_of`), and where none did, the bare crate
//! name. The receipt holds all of it under its `incremental` key
//! (`build_receipt`).
//!
//! THE RULE (`at_finish`): once a build has kept its receipt, in each profile
//! that receipt names under `incremental` and whose build directory lock the
//! build took exclusively and still holds, every crate folder that no unit of
//! the build directory's kept receipts uses is removed. It is kept where:
//!
//! * a kept receipt names it, or names its crate bare;
//! * it was written since this build began (less `FENCE_SLACK`), which a
//!   compile of this build the ledger did not see may have done;
//! * a compiler holds one of its session locks (`s-*.lock`), as the
//!   compiler's own collection tests them;
//! * it is no folder (a file or a symlink), or its name is not one the
//!   compiler makes.
//!
//! THE EXCLUSION. Every Cargo build holds its profile's `.cargo-build-lock`
//! while it compiles, exclusively unless it runs with fine-grain locking
//! (`-Zfine-grain-locking` or `build.shared-dependency-cache`),
//! and the compiler makes, uses and finalizes a crate folder only while the
//! build that runs it compiles. So while this build holds that lock
//! exclusively, no other build can have a compile in the profile, nor a unit
//! compiled and its receipt not yet kept: nothing can start a session in a
//! folder between the trim's look at it and its removal, and no folder is an
//! unreceipted one of a build still running. Where the lock is shared
//! (fine-grain locking), borrowed from a retained original (a continued
//! build) or not taken, another build may be doing both, so the profile is
//! left as it is (`Left::Shared`); a later build that holds it exclusively
//! trims it. A build that predates the lock (an older Cargo) takes the
//! artifact directory's `.cargo-lock` exclusively, which every build here
//! holds shared.
//!
//! A RECEIPT WITHOUT `incremental` was written by a targo from before this
//! module (DC-12a): its units' folders are unknown, so every profile it names
//! under `profiles` is left as it is (`Left::Unnamed`) until a build of its
//! selection replaces it. Every receipt this targo writes holds the key, empty
//! where no unit was compiled incrementally.
//!
//! Nothing is trimmed where the build kept no receipt (its graph failed, no
//! receipt could tell it, the write failed): its own units are then named
//! nowhere. Nothing is trimmed where a kept receipt cannot be read, since the
//! units it names are unknown. A profile this build's receipt names no unit
//! of under `incremental` is left as it is, as is every folder outside the build
//! directory's profiles (a confined unit's, a candidate lane's private unit's).
//! A build directory at or under a folder that holds aterm's custody marker
//! (`MARKER`) is left to aterm's own pass. A folder a receipt names that is
//! already gone is nothing to remove.
//!
//! THE REMOVAL runs in `finish_compilation`, under the build-directory lock
//! the build holds, after the receipt and before the build releases that
//! lock. It returns a value and never an error, so its failure never changes
//! the build's result.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::build_receipt::{self, Ran, Receipted};

/// The file aterm keeps at the top of a build cache it has in custody
/// (`MARKER` in aterm's `crates/atpkg/src/build_cache_registered.rs`).
pub(super) const MARKER: &str = ".aterm-build-cache.json";

/// How far before a compile's dispatch a folder's modification time may lie
/// and still count as the compile's (`written_by`): a kernel's coarse
/// file-system clock (one tick) can stamp a write earlier than the time read
/// just before it. Kept short, since a folder written in it by a build just
/// before counts too; a file system coarser still (FAT's two seconds) misses
/// a compile's folder, which then counts as unknown and keeps its crate's.
const WRITE_SLACK: Duration = Duration::from_millis(50);

/// How far before this build began a folder's modification time may lie and
/// still keep it as possibly this build's (`at_finish`): generous, since it
/// only keeps a folder longer, and so as coarse as FAT's clock.
const FENCE_SLACK: Duration = Duration::from_secs(2);

/// What incremental receipts say of each unit: per profile, the unit's hash
/// and the folders (or bare crate names) it uses.
type Incremental = BTreeMap<String, BTreeMap<String, BTreeSet<String>>>;

/// What one receipt says of the incremental folders its units use.
enum Named {
    /// Its `incremental` key.
    Folders(Incremental),
    /// It has no `incremental` key (a targo from before DC-12b wrote it):
    /// the profiles it names under `profiles`, whose folders its units may
    /// use.
    Unknown(BTreeSet<String>),
}

/// The crate folders in the profile's incremental folder `dir` that a compile
/// of crate `crate_name`, dispatched at `since`, wrote: each folder named
/// `<crate_name>-<id>` modified at or after `since` (less `WRITE_SLACK`).
/// `None` where `dir` cannot be read or no such folder is found: a compile
/// into `dir` writes its folder, so then its folder is unknown.
pub(super) fn written_by(
    dir: &Path,
    crate_name: &str,
    since: SystemTime,
) -> Option<BTreeSet<String>> {
    let since = since.checked_sub(WRITE_SLACK).unwrap_or(UNIX_EPOCH);
    let entries = fs::read_dir(dir).ok()?;
    let mut written = BTreeSet::new();
    for entry in entries {
        let entry = entry.ok()?;
        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };
        if build_receipt::crate_of_folder(&name) != Some(crate_name) {
            continue;
        }
        let Ok(meta) = fs::symlink_metadata(entry.path()) else {
            continue;
        };
        if meta.is_dir() && meta.modified().is_ok_and(|modified| modified >= since) {
            written.insert(name);
        }
    }
    (!written.is_empty()).then_some(written)
}

/// The folders a unit of crate `crate_name`, with hash `hash` in profile
/// `profile`, uses, as its receipt names them: for a unit the build compiled
/// (`ran`), the folders its compile wrote (`written`); for one it found
/// fresh, what the kept receipts (`kept`) said of it. Where neither is known
/// (the compile's folders were not noted, no kept receipt names the unit, or
/// one could not be read), the bare crate name, which keeps every folder of
/// that crate.
pub(super) fn folders_of(
    ran: Ran,
    written: Option<&BTreeSet<String>>,
    kept: Option<&Kept>,
    profile: &str,
    hash: &str,
    crate_name: &str,
) -> BTreeSet<String> {
    let named = match ran {
        Ran::Built => written.cloned(),
        Ran::Fresh => kept.and_then(|kept| kept.of(profile, hash)).cloned(),
    };
    named.unwrap_or_else(|| BTreeSet::from([crate_name.to_owned()]))
}

/// What the kept receipts of a build directory say of the incremental
/// folders its units use.
#[derive(Debug, Default)]
pub(super) struct Kept {
    units: Incremental,
    /// The profiles a receipt with no `incremental` key names: any folder in
    /// them may be one of its units'.
    unknown: BTreeSet<String>,
}

impl Kept {
    /// Every receipt in the receipts' folder of the build directory
    /// `build_dir`: a file there named sixteen lowercase hex digits and
    /// `.json`. `None` where one of them is not a regular file or cannot be
    /// read or decoded, or the folder is no folder or cannot be read; a build
    /// directory with no receipts' folder has none.
    pub(super) fn read(build_dir: &Path) -> Option<Kept> {
        let dir = build_dir.join(build_receipt::DIR);
        match fs::symlink_metadata(&dir) {
            Ok(meta) if meta.is_dir() => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return Some(Kept::default());
            }
            _ => return None,
        }
        let mut kept = Kept::default();
        for entry in fs::read_dir(&dir).ok()? {
            let entry = entry.ok()?;
            let Ok(name) = entry.file_name().into_string() else {
                continue;
            };
            if !name
                .strip_suffix(".json")
                .is_some_and(build_receipt::is_hash)
            {
                continue;
            }
            let path = entry.path();
            if !fs::symlink_metadata(&path).ok()?.is_file() {
                return None;
            }
            match decode(&fs::read(&path).ok()?)?.1 {
                Named::Folders(incremental) => {
                    for (profile, units) in incremental {
                        let into = kept.units.entry(profile).or_default();
                        for (hash, folders) in units {
                            into.entry(hash).or_default().extend(folders);
                        }
                    }
                }
                Named::Unknown(profiles) => kept.unknown.extend(profiles),
            }
        }
        Some(kept)
    }

    /// What the kept receipts say the unit `hash` of `profile` uses.
    pub(super) fn of(&self, profile: &str, hash: &str) -> Option<&BTreeSet<String>> {
        self.units.get(profile)?.get(hash)
    }

    /// The folders, and the bare crate names, that some unit of `profile`
    /// uses.
    fn used_in(&self, profile: &str) -> BTreeSet<&str> {
        self.units
            .get(profile)
            .into_iter()
            .flat_map(BTreeMap::values)
            .flatten()
            .map(String::as_str)
            .collect()
    }
}

/// A receipt's `began_ms` and what it names of incremental folders, or
/// `None` where its bytes are not a receipt of this format or any name in its
/// `incremental` (or, without that key, its `profiles`) is not one a receipt
/// keeps.
fn decode(bytes: &[u8]) -> Option<(u64, Named)> {
    let receipt: serde_json::Value = serde_json::from_slice(bytes).ok()?;
    if receipt.get("receipt")?.as_u64()? != build_receipt::FORMAT {
        return None;
    }
    let began_ms = receipt.get("began_ms")?.as_u64()?;
    let Some(named) = receipt.get("incremental") else {
        let profiles = receipt.get("profiles")?.as_object()?;
        if !profiles
            .keys()
            .all(|profile| profile.split('/').all(build_receipt::plain))
        {
            return None;
        }
        return Some((began_ms, Named::Unknown(profiles.keys().cloned().collect())));
    };
    let mut incremental = Incremental::new();
    for (profile, units) in named.as_object()? {
        if !profile.split('/').all(build_receipt::plain) {
            return None;
        }
        let into = incremental.entry(profile.clone()).or_default();
        for (hash, folders) in units.as_object()? {
            if !build_receipt::is_hash(hash) {
                return None;
            }
            let folders = folders
                .as_array()?
                .iter()
                .map(|folder| {
                    folder
                        .as_str()
                        .filter(|folder| build_receipt::is_folder_or_crate(folder))
                        .map(str::to_owned)
                })
                .collect::<Option<BTreeSet<String>>>()?;
            into.insert(hash.clone(), folders);
        }
    }
    Some((began_ms, Named::Folders(incremental)))
}

/// What the trim at the end of a build did (`at_finish`).
#[derive(Debug)]
pub(super) enum Trimmed {
    /// The build kept no receipt, so its units are named nowhere.
    NoReceipt,
    /// The build directory lies at or under this folder, which holds aterm's
    /// custody marker.
    Custody(PathBuf),
    /// A kept receipt, this build's among them, could not be read.
    Unread,
    /// The trim ran: the folders it removed, those it could not, and the
    /// profiles it left as they were.
    Ran {
        removed: Vec<PathBuf>,
        failed: Vec<(PathBuf, io::Error)>,
        left: Vec<(String, Left)>,
    },
}

/// Why the trim left a profile its receipt names as it was.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Left {
    /// This build does not hold the profile's build directory lock
    /// exclusively, so another build may be compiling in it.
    Shared,
    /// A kept receipt without `incremental` names the profile.
    Unnamed,
}

impl fmt::Display for Trimmed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Trimmed::NoReceipt => f.write_str("none, the build kept no receipt"),
            Trimmed::Custody(holder) => {
                write!(f, "none, aterm keeps {} in custody", holder.display())
            }
            Trimmed::Unread => f.write_str("none, a kept receipt cannot be read"),
            Trimmed::Ran {
                removed,
                failed,
                left,
            } => {
                write!(f, "{} folders removed", removed.len())?;
                for (path, error) in failed {
                    write!(f, "; {} not removed: {error}", path.display())?;
                }
                for (profile, why) in left {
                    let why = match why {
                        Left::Shared => "another build may be compiling in it",
                        Left::Unnamed => "an older receipt names it",
                    };
                    write!(f, "; {profile} left, {why}")?;
                }
                Ok(())
            }
        }
    }
}

/// THE END OF A BUILD: where the build kept its receipt (`receipted`), remove
/// from each profile of the build directory `build_dir` that receipt names
/// under `incremental`, and whose `incremental/` folder is among `exclusive`
/// (`CompilationFiles::exclusive_incremental_dirs`: the build holds that
/// profile's build directory lock exclusively), every crate folder that no
/// unit of the kept receipts uses (the module docs give the rule). This
/// returns no error and never panics, so nothing here can change the build's
/// result.
pub(super) fn at_finish(receipted: &Receipted, build_dir: &Path, exclusive: &[PathBuf]) -> Trimmed {
    let Receipted::Written(receipt) = receipted else {
        return Trimmed::NoReceipt;
    };
    if let Some(holder) = build_dir
        .ancestors()
        .find(|folder| fs::symlink_metadata(folder.join(MARKER)).is_ok())
    {
        return Trimmed::Custody(holder.to_path_buf());
    }
    let Some((began_ms, Named::Folders(this))) =
        fs::read(receipt).ok().and_then(|bytes| decode(&bytes))
    else {
        return Trimmed::Unread;
    };
    let Some(kept) = Kept::read(build_dir) else {
        return Trimmed::Unread;
    };
    let fence = UNIX_EPOCH
        .checked_add(Duration::from_millis(began_ms))
        .and_then(|began| began.checked_sub(FENCE_SLACK))
        .unwrap_or(UNIX_EPOCH);
    let mut removed = Vec::new();
    let mut failed = Vec::new();
    let mut left = Vec::new();
    for profile in this.keys() {
        let mut dir = build_dir.to_path_buf();
        dir.extend(profile.split('/'));
        dir.push("incremental");
        if !exclusive.contains(&dir) {
            left.push((profile.clone(), Left::Shared));
            continue;
        }
        if kept.unknown.contains(profile) {
            left.push((profile.clone(), Left::Unnamed));
            continue;
        }
        trim(
            &dir,
            &kept.used_in(profile),
            fence,
            &mut removed,
            &mut failed,
        );
    }
    Trimmed::Ran {
        removed,
        failed,
        left,
    }
}

/// Remove from the incremental folder `dir` each crate folder that `used`
/// names neither by its name nor by its crate, last modified before `fence`
/// and whose sessions no compiler holds.
fn trim(
    dir: &Path,
    used: &BTreeSet<&str>,
    fence: SystemTime,
    removed: &mut Vec<PathBuf>,
    failed: &mut Vec<(PathBuf, io::Error)>,
) {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return,
        Err(error) => {
            failed.push((dir.to_path_buf(), error));
            return;
        }
    };
    for entry in entries {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                failed.push((dir.to_path_buf(), error));
                continue;
            }
        };
        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };
        let Some(krate) = build_receipt::crate_of_folder(&name) else {
            continue;
        };
        if used.contains(name.as_str()) || used.contains(krate) {
            continue;
        }
        let path = entry.path();
        let Ok(meta) = fs::symlink_metadata(&path) else {
            continue;
        };
        if !meta.is_dir() || !meta.modified().is_ok_and(|modified| modified < fence) {
            continue;
        }
        if in_use(&path) {
            continue;
        }
        match fs::remove_dir_all(&path) {
            Ok(()) => removed.push(path),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => failed.push((path, error)),
        }
    }
}

/// Whether a compiler may hold a session of the crate folder `folder`: it
/// cannot be read, or one of its `*.lock` files is locked (the compiler holds
/// a session's lock while the session is active, and its own collection
/// tests them the same way).
fn in_use(folder: &Path) -> bool {
    let Ok(entries) = fs::read_dir(folder) else {
        return true;
    };
    for entry in entries {
        let Ok(entry) = entry else {
            return true;
        };
        let path = entry.path();
        if path.extension().is_none_or(|extension| extension != "lock") {
            continue;
        }
        let file = match fs::File::open(&path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(_) => return true,
        };
        // The lock, where taken, goes with `file`.
        if crate::util::flock::try_lock_exclusive(&file).is_err() {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::build_receipt::{Receipt, Root, Selection, Told, UnitUsed};
    use crate::workspace::profiles::RequestedIncremental;

    /// The crate whose units the tests build.
    const CRATE: &str = "receipt_member";
    /// The member's library on one branch.
    const ON_MAIN: &str = "1111111111111111";
    /// The same library on another branch: another variant, so another
    /// folder.
    const ON_BRANCH: &str = "2222222222222222";
    /// A unit no receipt has named before.
    const UNNAMED: &str = "3333333333333333";

    /// A private build directory under the system's temporary folder.
    fn scratch() -> tempfile::TempDir {
        let base = std::env::temp_dir()
            .join(".ubd")
            .join("targo-incremental-trim.noindex");
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
            incremental: RequestedIncremental {
                compiles: true,
                by_default: true,
            },
            profile: "dev".to_owned(),
            roots: BTreeSet::from([Root {
                args: Vec::new(),
                features: Vec::new(),
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

    /// The `debug` profile's incremental folder of the build directory `dir`.
    fn incremental(dir: &Path) -> PathBuf {
        dir.join("debug").join("incremental")
    }

    /// Make the folder `name` in the incremental folder `dir`, with a session
    /// in it, last written a day ago.
    fn old_folder(dir: &Path, name: &str) -> PathBuf {
        let folder = new_folder(dir, name);
        age(&folder);
        folder
    }

    /// Make the folder `name` in the incremental folder `dir`, with a session
    /// in it, written now.
    fn new_folder(dir: &Path, name: &str) -> PathBuf {
        let folder = dir.join(name);
        let session = folder.join("s-gzjqk1hq2v-1ac2jcn-working");
        fs::create_dir_all(&session).unwrap();
        fs::write(session.join("dep-graph.bin"), b"graph").unwrap();
        folder
    }

    /// Make `path` last written a day ago.
    fn age(path: &Path) {
        let day_ago = SystemTime::now() - Duration::from_secs(24 * 60 * 60);
        filetime::set_file_mtime(path, filetime::FileTime::from_system_time(day_ago)).unwrap();
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

    /// The names `names`, as a set.
    fn set(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|name| (*name).to_owned()).collect()
    }

    /// One unit of `CRATE` the queue ran, in the `debug` profile.
    struct Ran1 {
        hash: &'static str,
        ran: Ran,
        written: Option<BTreeSet<String>>,
    }

    /// The end of a build of `package`'s selection that began now and ran
    /// `units`, holding the `debug` profile's lock exclusively, as
    /// `finish_compilation` ends it: each unit's folders named as
    /// `BuildRunner::units_used` names them (`folders_of`, from the receipts
    /// kept before), the receipt kept, then the trim.
    fn build(dir: &Path, package: &str, units: Vec<Ran1>) -> (Receipted, Trimmed) {
        build_holding(dir, package, units, &[incremental(dir)])
    }

    /// `build`, holding exclusively the profiles whose incremental folders
    /// are `exclusive`.
    fn build_holding(
        dir: &Path,
        package: &str,
        units: Vec<Ran1>,
        exclusive: &[PathBuf],
    ) -> (Receipted, Trimmed) {
        let began_ms = u64::try_from(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_millis(),
        )
        .unwrap();
        let kept = Kept::read(dir);
        let units = units
            .into_iter()
            .map(|unit| UnitUsed {
                profile: Some("debug".to_owned()),
                hash: unit.hash.to_owned(),
                package: package.to_owned(),
                member: true,
                built: unit.ran == Ran::Built,
                outputs: Vec::new(),
                incremental: Some(folders_of(
                    unit.ran,
                    unit.written.as_ref(),
                    kept.as_ref(),
                    "debug",
                    unit.hash,
                    CRATE,
                )),
            })
            .collect();
        let receipted = build_receipt::at_finish(true, dir, || {
            Receipt::new(began_ms, selection(package), units).into()
        });
        let trimmed = at_finish(&receipted, dir, exclusive);
        (receipted, trimmed)
    }

    /// The folders a trim that left no profile removed, by name, sorted.
    fn removed(trimmed: &Trimmed) -> Vec<String> {
        let Trimmed::Ran {
            removed,
            failed,
            left,
        } = trimmed
        else {
            panic!("{trimmed:?}");
        };
        assert!(failed.is_empty(), "{trimmed}");
        assert!(left.is_empty(), "{trimmed}");
        let mut names: Vec<String> = removed
            .iter()
            .map(|path| path.file_name().unwrap().to_str().unwrap().to_owned())
            .collect();
        names.sort();
        names
    }

    /// When a build ends, the crate folders of its profile that no unit of
    /// the kept receipts uses go: the old variant of the unit it compiled and
    /// a crate no unit uses. The folder the unit's compile wrote, which the
    /// ledger notes (`written_by`, the old variant and another crate's
    /// folder not among it), stays, and the receipt names it. A file, a
    /// symlink (and the folder it points to), a folder whose name the
    /// compiler never makes, a profile the receipt names under no
    /// `incremental`, and a profile no receipt names stay as they were.
    ///
    /// Negative controls: a graph that failed, and a receipt that could not
    /// be written, trim nothing. A folder no receipt names stays while it was
    /// written since the build began or a compiler holds its session lock,
    /// and goes at the next build's end once neither holds. The ledger notes
    /// no folder for a unit it did not compile, nor one written a second
    /// before the compile's dispatch.
    #[test]
    fn an_incremental_folder_no_kept_builds_unit_uses_goes_when_a_build_ends() {
        let build_dir = scratch();
        let dir = build_dir.path();
        let incr = incremental(dir);
        let old_variant = "receipt_member-0old000000000";
        let unused = "receipt_gone-1abc000000000";
        old_folder(&incr, old_variant);
        old_folder(&incr, unused);
        old_folder(&incr, "not_a_crate_folder");
        fs::write(incr.join("receipt_file-2fil000000000"), b"file").unwrap();
        age(&incr.join("receipt_file-2fil000000000"));
        let elsewhere = scratch();
        let pointed = old_folder(elsewhere.path(), "receipt_link-3lnk000000000");
        #[cfg(unix)]
        std::os::unix::fs::symlink(&pointed, incr.join("receipt_link-3lnk000000000")).unwrap();
        let cross = dir
            .join("aarch64-apple-darwin")
            .join("debug")
            .join("incremental");
        old_folder(&cross, unused);
        let release = dir.join("release").join("incremental");
        old_folder(&release, unused);

        // The compile of the member's library writes its folder; the ledger
        // notes it, and only it.
        let mut ledger = build_receipt::Ledger::default();
        ledger.dispatched(ON_MAIN, false);
        ledger.dispatched(UNNAMED, true);
        assert_eq!(ledger.compiling_since(&UNNAMED), None);
        let since = ledger.compiling_since(&ON_MAIN).unwrap();
        let current = "receipt_member-4new000000000";
        new_folder(&incr, current);
        new_folder(&incr, "receipt_other-5oth000000000");
        let written = written_by(&incr, CRATE, since).unwrap();
        assert_eq!(written, set(&[current]));
        ledger.wrote(ON_MAIN, written);
        // Negative control: a folder written a second before the dispatch (a
        // build just before this one) is not the compile's.
        let just_before = new_folder(&incr, "receipt_member-9bfr000000000");
        filetime::set_file_mtime(
            &just_before,
            filetime::FileTime::from_system_time(since - Duration::from_secs(1)),
        )
        .unwrap();
        assert_eq!(written_by(&incr, CRATE, since), Some(set(&[current])));
        fs::remove_dir_all(&just_before).unwrap();
        // Negative control: a compile dispatched later wrote none of them,
        // so its folder is unknown, as it is where the folder cannot be read.
        assert_eq!(
            written_by(&incr, CRATE, SystemTime::now() + Duration::from_secs(60)),
            None
        );
        assert_eq!(written_by(&dir.join("nowhere"), CRATE, since), None);
        age(&incr.join(current));
        age(&incr.join("receipt_other-5oth000000000"));

        // An overlapping build's folder, written while this build runs, and
        // one a compiler holds.
        let overlapping = "receipt_overlap-6ovl000000000";
        let written_later = SystemTime::now() + Duration::from_secs(60 * 60);
        filetime::set_file_mtime(
            new_folder(&incr, overlapping),
            filetime::FileTime::from_system_time(written_later),
        )
        .unwrap();
        let busy = old_folder(&incr, "receipt_busy-7bsy000000000");
        let lock = busy.join("s-gzjqk1hq2v-1ac2jcn.lock");
        fs::write(&lock, b"").unwrap();
        let held = fs::File::open(&lock).unwrap();
        crate::util::flock::try_lock_exclusive(&held).unwrap();
        age(&busy);

        let before = entries(&incr);
        // Negative control: a graph that failed trims nothing.
        let receipted = build_receipt::at_finish(false, dir, || unreachable!());
        assert!(matches!(
            at_finish(&receipted, dir, &[incr.clone()]),
            Trimmed::NoReceipt
        ));
        // Negative control: a receipt that was not written trims nothing.
        let unwritten = Receipted::NotWritten {
            error: io::Error::new(io::ErrorKind::StorageFull, "no space left on device"),
            withdrawn: Ok(()),
        };
        assert!(matches!(
            at_finish(&unwritten, dir, &[incr.clone()]),
            Trimmed::NoReceipt
        ));
        assert_eq!(entries(&incr), before);

        let units = ledger
            .iter()
            .map(|(&hash, ran)| Ran1 {
                hash,
                ran,
                written: ledger.folders_written(&hash).cloned(),
            })
            .collect();
        let (receipted, trimmed) = build(dir, "receipt-member", units);
        let Receipted::Written(receipt) = &receipted else {
            panic!("{receipted:?}");
        };
        let receipt: serde_json::Value =
            serde_json::from_slice(&fs::read(receipt).unwrap()).unwrap();
        assert_eq!(
            receipt["incremental"],
            serde_json::json!({ "debug": {
                ON_MAIN: [current],
                UNNAMED: [CRATE],
            }})
        );
        // The fresh unit no receipt named keeps every folder of its crate,
        // so the old variant stays this time.
        assert_eq!(
            removed(&trimmed),
            ["receipt_gone-1abc000000000", "receipt_other-5oth000000000"]
        );

        // Now the fresh unit is named by what it used before: the bare
        // crate, until it is compiled. Compiled, it names its folder, and
        // the old variant goes.
        let mut ledger = build_receipt::Ledger::default();
        ledger.dispatched(ON_MAIN, true);
        ledger.dispatched(UNNAMED, false);
        let unnamed_folder = "receipt_member-8unn000000000";
        new_folder(&incr, unnamed_folder);
        let since = ledger.compiling_since(&UNNAMED).unwrap();
        ledger.wrote(UNNAMED, written_by(&incr, CRATE, since).unwrap());
        assert_eq!(
            ledger.folders_written(&UNNAMED),
            Some(&set(&[unnamed_folder]))
        );
        let units = ledger
            .iter()
            .map(|(&hash, ran)| Ran1 {
                hash,
                ran,
                written: ledger.folders_written(&hash).cloned(),
            })
            .collect();
        let (_, trimmed) = build(dir, "receipt-member", units);
        assert_eq!(removed(&trimmed), [old_variant]);
        let mut left = vec![
            "not_a_crate_folder",
            "receipt_busy-7bsy000000000",
            "receipt_file-2fil000000000",
            current,
            unnamed_folder,
            overlapping,
        ];
        #[cfg(unix)]
        left.push("receipt_link-3lnk000000000");
        left.sort_unstable();
        assert_eq!(entries(&incr), left);
        assert!(pointed.is_dir());
        assert!(cross.join(unused).is_dir());
        assert!(release.join(unused).is_dir());

        // Negative control: once old and released, they go.
        drop(held);
        age(&busy);
        age(&incr.join(overlapping));
        let (_, trimmed) = build(
            dir,
            "receipt-member",
            vec![
                Ran1 {
                    hash: ON_MAIN,
                    ran: Ran::Fresh,
                    written: None,
                },
                Ran1 {
                    hash: UNNAMED,
                    ran: Ran::Fresh,
                    written: None,
                },
            ],
        );
        assert_eq!(
            removed(&trimmed),
            ["receipt_busy-7bsy000000000", overlapping]
        );
    }

    /// A folder a unit of a kept receipt uses stays: two branches built in
    /// turn keep both their folders, and a unit found fresh carries its folder
    /// forward. A unit whose folder nobody recorded keeps every folder of its
    /// crate (and no other crate's); so does one compiled whose folders were
    /// not noted. A kept receipt that cannot be read stops the trim. A
    /// profile whose lock the build holds shared, and one a kept receipt from
    /// before DC-12b names (its units' folders unknown), are left whole.
    ///
    /// Negative controls: once the other branch's receipt is withdrawn and
    /// the older receipt gone, a build holding the profile exclusively removes
    /// the branch's folder at its end; once the receipt that cannot be read is
    /// gone, the trim runs.
    #[test]
    fn an_incremental_folder_a_kept_builds_unit_uses_stays() {
        let build_dir = scratch();
        let dir = build_dir.path();
        let incr = incremental(dir);
        let main = "receipt_member-0man000000000";
        let branch = "receipt_member-1brn000000000";
        let unrelated = "receipt_unrelated-2unr000000000";

        // main's build compiles its variant.
        new_folder(&incr, main);
        let (_, trimmed) = build(
            dir,
            "receipt-member",
            vec![Ran1 {
                hash: ON_MAIN,
                ran: Ran::Built,
                written: Some(set(&[main])),
            }],
        );
        assert_eq!(removed(&trimmed), Vec::<String>::new());
        age(&incr.join(main));

        // The branch's build, another selection, compiles its own; main's
        // folder stays.
        new_folder(&incr, branch);
        let (_, trimmed) = build(
            dir,
            "receipt-branch",
            vec![Ran1 {
                hash: ON_BRANCH,
                ran: Ran::Built,
                written: Some(set(&[branch])),
            }],
        );
        assert_eq!(removed(&trimmed), Vec::<String>::new());
        age(&incr.join(branch));
        assert_eq!(entries(&incr), [main, branch]);

        // main again, its unit fresh: it carries its folder forward.
        let kept = Kept::read(dir).unwrap();
        assert_eq!(kept.of("debug", ON_MAIN), Some(&set(&[main])));
        let (receipted, trimmed) = build(
            dir,
            "receipt-member",
            vec![Ran1 {
                hash: ON_MAIN,
                ran: Ran::Fresh,
                written: None,
            }],
        );
        assert_eq!(removed(&trimmed), Vec::<String>::new());
        let Receipted::Written(path) = &receipted else {
            panic!("{receipted:?}");
        };
        let Some((_, Named::Folders(named))) = decode(&fs::read(path).unwrap()) else {
            panic!("{path:?}");
        };
        assert_eq!(named["debug"][ON_MAIN], set(&[main]));
        assert_eq!(entries(&incr), [main, branch]);

        // What is unknown keeps its crate's folders and no other crate's.
        assert_eq!(
            folders_of(Ran::Fresh, None, Some(&kept), "debug", UNNAMED, CRATE),
            set(&[CRATE])
        );
        assert_eq!(
            folders_of(Ran::Fresh, None, None, "debug", ON_MAIN, CRATE),
            set(&[CRATE])
        );
        assert_eq!(
            folders_of(Ran::Built, None, Some(&kept), "debug", ON_MAIN, CRATE),
            set(&[CRATE])
        );
        assert_eq!(
            folders_of(Ran::Fresh, None, Some(&kept), "release", ON_MAIN, CRATE),
            set(&[CRATE])
        );
        old_folder(&incr, "receipt_member-3var000000000");
        old_folder(&incr, unrelated);
        let (_, trimmed) = build(
            dir,
            "receipt-unknown",
            vec![Ran1 {
                hash: UNNAMED,
                ran: Ran::Fresh,
                written: None,
            }],
        );
        assert_eq!(removed(&trimmed), [unrelated]);
        assert_eq!(
            entries(&incr),
            [main, branch, "receipt_member-3var000000000"]
        );

        // A kept receipt that cannot be read stops the trim.
        old_folder(&incr, unrelated);
        let torn = dir.join(build_receipt::DIR).join("0123456789abcdef.json");
        fs::write(&torn, br#"{"began_ms":"#).unwrap();
        assert!(Kept::read(dir).is_none());
        let (_, trimmed) = build(
            dir,
            "receipt-unknown",
            vec![Ran1 {
                hash: UNNAMED,
                ran: Ran::Fresh,
                written: None,
            }],
        );
        assert!(matches!(trimmed, Trimmed::Unread), "{trimmed}");
        assert_eq!(
            entries(&incr),
            [main, branch, "receipt_member-3var000000000", unrelated]
        );
        // A private file a cut-short write left is no receipt.
        fs::remove_file(&torn).unwrap();
        fs::write(
            dir.join(build_receipt::DIR).join(".receipt-abc.tmp"),
            b"torn",
        )
        .unwrap();
        assert!(Kept::read(dir).is_some());
        let receipted =
            build_receipt::at_finish(true, dir, || Told::Untold(selection("receipt-unknown")));
        assert!(matches!(
            receipted,
            Receipted::Unstated { withdrawn: Ok(()) }
        ));

        // With the branch's receipt withdrawn, its folder, the variant and
        // the crate no receipt names any more are no kept unit's.
        let receipted =
            build_receipt::at_finish(true, dir, || Told::Untold(selection("receipt-branch")));
        assert!(matches!(
            receipted,
            Receipted::Unstated { withdrawn: Ok(()) }
        ));
        let main_fresh = || {
            vec![Ran1 {
                hash: ON_MAIN,
                ran: Ran::Fresh,
                written: None,
            }]
        };
        let all = [main, branch, "receipt_member-3var000000000", unrelated];
        // Yet a build that does not hold the profile's lock exclusively
        // (fine-grain locking, a borrowed lock) leaves the profile: another
        // build may be compiling in it, or have compiled a unit there whose
        // receipt it has not kept yet.
        let (_, trimmed) = build_holding(dir, "receipt-member", main_fresh(), &[]);
        assert!(
            matches!(&trimmed, Trimmed::Ran { removed, failed, left }
                if removed.is_empty() && failed.is_empty()
                    && *left == [("debug".to_owned(), Left::Shared)]),
            "{trimmed}"
        );
        assert_eq!(entries(&incr), all);
        // And a kept receipt from a targo before DC-12b, which names the
        // profile under `profiles` and has no `incremental`, holds every
        // folder of it: its units' folders are unknown.
        let older = dir.join(build_receipt::DIR).join("abcdef0123456789.json");
        fs::write(
            &older,
            br#"{"began_ms":1794528000000,"built":{},"members":["receipt-older"],"output_bytes":0,"profiles":{"debug":["4444444444444444"]},"receipt":1,"selection":{}}"#,
        )
        .unwrap();
        assert_eq!(
            Kept::read(dir).unwrap().unknown,
            BTreeSet::from(["debug".to_owned()])
        );
        let (_, trimmed) = build(dir, "receipt-member", main_fresh());
        assert!(
            matches!(&trimmed, Trimmed::Ran { removed, failed, left }
                if removed.is_empty() && failed.is_empty()
                    && *left == [("debug".to_owned(), Left::Unnamed)]),
            "{trimmed}"
        );
        assert_eq!(entries(&incr), all);
        fs::remove_file(&older).unwrap();

        // Negative control: with the older receipt gone too, and the profile
        // held exclusively, they go at the next build's end; main's stays.
        let (_, trimmed) = build(
            dir,
            "receipt-member",
            vec![Ran1 {
                hash: ON_MAIN,
                ran: Ran::Fresh,
                written: None,
            }],
        );
        assert_eq!(
            removed(&trimmed),
            [branch, "receipt_member-3var000000000", unrelated]
        );
        assert_eq!(entries(&incr), [main]);
        // A folder a receipt names that is already gone is nothing to remove.
        fs::remove_dir_all(incr.join(main)).unwrap();
        let (_, trimmed) = build(
            dir,
            "receipt-member",
            vec![Ran1 {
                hash: ON_MAIN,
                ran: Ran::Fresh,
                written: None,
            }],
        );
        assert_eq!(removed(&trimmed), Vec::<String>::new());
    }

    /// A build directory at or under a folder that holds aterm's custody
    /// marker keeps every incremental folder: aterm's own pass decides
    /// there, and the receipt is still kept.
    ///
    /// Negative control: the same build with the marker gone removes the
    /// folder no unit uses.
    #[test]
    fn a_build_directory_under_aterm_custody_keeps_every_incremental_folder() {
        let cache = scratch();
        let dir = cache.path().join("worktree").join("target");
        let incr = incremental(&dir);
        let unused = "receipt_gone-0abc000000000";
        old_folder(&incr, unused);
        let current = "receipt_member-1cur000000000";
        new_folder(&incr, current);
        let ran = || {
            vec![Ran1 {
                hash: ON_MAIN,
                ran: Ran::Built,
                written: Some(set(&[current])),
            }]
        };

        for holder in [cache.path().to_path_buf(), dir.clone()] {
            let marker = holder.join(MARKER);
            fs::write(&marker, b"{}").unwrap();
            let (receipted, trimmed) = build(&dir, "receipt-member", ran());
            assert!(matches!(receipted, Receipted::Written(_)), "{receipted:?}");
            assert!(
                matches!(&trimmed, Trimmed::Custody(found) if *found == holder),
                "{trimmed}"
            );
            assert_eq!(entries(&incr), [unused, current]);
            fs::remove_file(&marker).unwrap();
        }

        // Negative control: no marker.
        let (_, trimmed) = build(&dir, "receipt-member", ran());
        assert_eq!(removed(&trimmed), [unused]);
        assert_eq!(entries(&incr), [current]);
    }
}
