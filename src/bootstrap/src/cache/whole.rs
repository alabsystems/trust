//! Whole target-tree reclamation under the existing original native owners.
//! Selection and accounting are observations; they never construct exclusion.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CString, OsStr, OsString};
use std::fs::File;
use std::io::{self, Read as _};
use std::os::fd::{AsFd, AsRawFd, BorrowedFd};
use std::os::unix::ffi::OsStrExt as _;
use std::time::{SystemTime, UNIX_EPOCH};

use sha2::{Digest as _, Sha256};

use super::*;
use crate::utils::trust_prune::{CargoLocks, space};

const TOOLS: &[&str] =
    &["stage1-tools", "stage2-tools", "stage3-tools", "bootstrap-tools", "bootstrap-seed-tools"];
const COMPILERS: &[&str] = &["stage1-rustc", "stage2-rustc"];
const RECLAIM_TAG: &str = ".slim-reclaim-";

mod links;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum WholeProfile {
    Compilers,
    /// Explicit tools-before-compiler profile, never a broken-compiler fallback.
    SeedTools,
}

/// Explicit selection DATA. Whole compiler targets require a separate opt-in;
/// no force flag or arbitrary user-supplied deletion path is supported.
pub struct WholeRequest {
    selection: SelectedOutput,
    profile: WholeProfile,
    root: PathBuf,
    build: PathBuf,
    host: PathBuf,
    compiler_caches: bool,
    dry_run: bool,
}
impl WholeRequest {
    pub fn detect_host(
        selection: &SelectedOutput,
        output: &OutputLock,
    ) -> Result<OsString, String> {
        selection.check_current()?;
        output.check_root(selection.output()).map_err(|e| e.to_string())?;
        let original = output.original_directory().map_err(|e| e.to_string())?;
        let mut hosts = Vec::new();
        for entry in space::entries(original).map_err(|e| e.to_string())? {
            let meta = space::metadata_at(original, &entry).map_err(|e| e.to_string())?;
            if !meta.directory() || scratch_host(&entry) {
                continue;
            }
            let directory = space::open_at(original, &entry, true).map_err(|e| e.to_string())?;
            for stage in ["stage0-sysroot", "stage1", "stage2"] {
                if optional(directory.as_fd(), OsStr::new(stage))
                    .map_err(|e| e.to_string())?
                    .is_some_and(|m| m.directory() || m.symlink())
                {
                    hosts.push(entry.clone());
                    break;
                }
            }
        }
        match hosts.as_slice() { [host]=>Ok(host.clone()),_=>Err("whole-tree reclaim needs --host when original output has zero or multiple host candidates".into()) }
    }
    pub fn new(
        root: &Path,
        host: &Path,
        compiler_caches: bool,
        dry_run: bool,
    ) -> Result<Self, String> {
        Self::from_selection(SelectedOutput::capture(root)?, host, compiler_caches, dry_run)
    }
    pub fn from_selection(
        selection: SelectedOutput,
        host: &Path,
        compiler_caches: bool,
        dry_run: bool,
    ) -> Result<Self, String> {
        if scratch_host(host.as_os_str()) {
            return Err("cache host cannot be a selected scratch/reclaim directory".into());
        }
        let (root, build, host) = super::location(&selection, host)?;
        let meta = std::fs::symlink_metadata(&host).map_err(|e| e.to_string())?;
        if !meta.is_dir() || meta.file_type().is_symlink() {
            return Err("whole-tree maintenance requires a plain original host directory".into());
        }
        let build = build.canonicalize().map_err(|e| e.to_string())?;
        let host = host.canonicalize().map_err(|e| e.to_string())?;
        if host.parent() != Some(build.as_path()) {
            return Err("cache host is not this original output's direct physical child".into());
        }
        Ok(Self {
            selection,
            profile: WholeProfile::Compilers,
            root,
            build,
            host,
            compiler_caches,
            dry_run,
        })
    }
    pub fn with_profile(mut self, profile: WholeProfile) -> Result<Self, String> {
        if profile == WholeProfile::SeedTools && self.compiler_caches {
            return Err("seed-tools profile cannot reclaim compiler caches".into());
        }
        self.profile = profile;
        Ok(self)
    }
    pub fn root(&self) -> &Path {
        &self.root
    }
    pub fn output(&self) -> &Path {
        &self.build
    }
}

#[derive(Debug, Serialize)]
pub struct WholeReport {
    pub profile: WholeProfile,
    pub dry_run: bool,
    pub compiler_caches: bool,
    pub planned_trees: Vec<PathBuf>,
    pub removed_trees: Vec<PathBuf>,
    pub preserved: Vec<(PathBuf, String)>,
    pub planned_file_space: SpaceEstimate,
    pub volume_space: Option<VolumeChange>,
    pub removed_allocated_bytes: u64,
    pub sysroots: Vec<(PathBuf, String)>,
    pub failures: Vec<String>,
}
impl WholeReport {
    pub fn is_complete(&self) -> bool {
        self.failures.is_empty()
    }
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}
fn relative<'a>(request: &WholeRequest, path: &'a Path) -> io::Result<&'a Path> {
    let value = path
        .strip_prefix(&request.build)
        .map_err(|_| invalid("whole-tree selection escaped output"))?;
    if value.as_os_str().is_empty()
        || value.components().any(|p| !matches!(p, Component::Normal(_)))
    {
        return Err(invalid("whole-tree selection is not a proper relative descendant"));
    }
    Ok(value)
}
fn optional(parent: BorrowedFd<'_>, name: &OsStr) -> io::Result<Option<space::Snapshot>> {
    match space::metadata_at(parent, name) {
        Ok(value) => Ok(Some(value)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error),
    }
}
fn scratch_host(name: &OsStr) -> bool {
    let folded = name.as_bytes().to_ascii_lowercase();
    folded == b"tmp" || std::str::from_utf8(&folded).ok().and_then(stale_base) == Some("tmp")
}
fn stale_base(name: &str) -> Option<&str> {
    let (base, rest) = name.split_once(RECLAIM_TAG)?;
    let (pid, epoch) = rest.split_once('-')?;
    let decimal =
        |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) && !s.starts_with('0');
    (decimal(pid) && decimal(epoch)).then_some(base)
}
fn recovery_stage(name: &str) -> Option<&str> {
    let (stage, tail) = name.split_once(".pre-cache-recovery.")?;
    let number = stage.strip_prefix("stage")?;
    (!number.is_empty()
        && !number.starts_with('0')
        && number.bytes().all(|b| b.is_ascii_digit())
        && !tail.is_empty()
        && tail.bytes().all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b)))
    .then_some(stage)
}

fn add(paths: &mut BTreeSet<PathBuf>, path: PathBuf, meta: space::Snapshot) -> io::Result<()> {
    if !meta.directory() {
        return Err(invalid(format!(
            "selected whole-tree candidate {} is not a plain directory",
            path.display()
        )));
    }
    paths.insert(path);
    Ok(())
}

struct Candidate {
    path: PathBuf,
    original: space::Snapshot,
}
struct Kept {
    original: space::Snapshot,
    target: Option<(u64, u64)>,
    bytes: Option<[u8; 32]>,
}
struct Prepared {
    candidates: Vec<Candidate>,
    inventory: space::Accounting,
    kept: BTreeMap<PathBuf, Kept>,
    preserved: Vec<(PathBuf, String)>,
    _locks: Vec<CargoLocks>,
    detached: Vec<(PathBuf, space::Snapshot)>,
    removed_links: BTreeMap<(u64, u64), u64>,
    recreated_scratch: Option<space::Snapshot>,
}

impl Prepared {
    fn new(request: &WholeRequest, output: &OutputLock) -> io::Result<Self> {
        request.selection.check_current().map_err(invalid)?;
        output.check_root(&request.build)?;
        let original = output.original_directory()?;
        let mut inventory = space::Accounting::new(&request.build, original)?;
        let host_rel = relative(request, &request.host)?;
        let (host_parent, host_name) = inventory.parent(host_rel)?;
        let host = space::open_at(host_parent.as_fd(), &host_name, true)?;
        let mut paths = BTreeSet::new();
        let mut preserved = Vec::new();
        for base in TOOLS.iter().chain(COMPILERS.iter().filter(|_| request.compiler_caches)) {
            if let Some(meta) = optional(host.as_fd(), OsStr::new(base))? {
                add(&mut paths, request.host.join(base), meta)?;
            }
        }
        for entry in space::entries(host.as_fd())? {
            let Some(text) = entry.to_str() else {
                continue;
            };
            if let Some(base) = stale_base(text) {
                if TOOLS.contains(&base) || (request.compiler_caches && COMPILERS.contains(&base)) {
                    add(
                        &mut paths,
                        request.host.join(&entry),
                        space::metadata_at(host.as_fd(), &entry)?,
                    )?;
                } else {
                    preserved.push((
                        request.host.join(&entry),
                        "protected or non-selected reclaim prefix".into(),
                    ));
                }
            } else if let Some(stage) =
                recovery_stage(text).filter(|_| request.profile == WholeProfile::Compilers)
            {
                // A recovery husk is disposable only beside the preserved
                // primary stage; no historical naming text proves completion.
                if optional(host.as_fd(), OsStr::new(stage))?.is_some_and(|m| m.directory()) {
                    add(
                        &mut paths,
                        request.host.join(&entry),
                        space::metadata_at(host.as_fd(), &entry)?,
                    )?;
                } else {
                    preserved.push((
                        request.host.join(&entry),
                        "recovery husk has no preserved plain primary stage".into(),
                    ));
                }
            }
        }
        if let Some(private_meta) = optional(host.as_fd(), OsStr::new("rustc-private-sysroots"))?
            .filter(|_| request.profile == WholeProfile::Compilers)
        {
            if !private_meta.directory() {
                return Err(invalid("private sysroot census is not a plain directory"));
            }
            let private = space::open_at(host.as_fd(), OsStr::new("rustc-private-sysroots"), true)?;
            let mut variants = Vec::new();
            let mut leftovers = Vec::new();
            for entry in space::entries(private.as_fd())? {
                let Some(text) = entry.to_str() else {
                    continue;
                };
                if !text.starts_with("rustc-private-tool-") {
                    continue;
                }
                let meta = space::metadata_at(private.as_fd(), &entry)?;
                if !meta.directory() {
                    return Err(invalid("private sysroot variant is not a plain directory"));
                }
                if stale_base(text).is_some() {
                    leftovers.push((entry, meta));
                } else if !text.contains(RECLAIM_TAG) {
                    variants.push((entry, meta));
                } else {
                    preserved.push((
                        request.host.join("rustc-private-sysroots").join(entry),
                        "unrecognized private reclaim name".into(),
                    ));
                }
            }
            let newest = variants.iter().map(|(_, m)| m.modified()).max();
            for (entry, meta) in variants {
                let path = request.host.join("rustc-private-sysroots").join(entry);
                if Some(meta.modified()) == newest {
                    preserved.push((path, "newest private sysroot (ties preserved)".into()));
                } else {
                    paths.insert(path);
                }
            }
            // If no primary variant survives, even a stale name is no proof
            // that this is not the last private sysroot. Leave it untouched.
            for (entry, _) in leftovers {
                let path = request.host.join("rustc-private-sysroots").join(entry);
                if newest.is_some() {
                    paths.insert(path);
                } else {
                    preserved.push((path, "no preserved primary private sysroot".into()));
                }
            }
        }
        let root = space::open_at(original, OsStr::new("."), true)?;
        if let Some(meta) = optional(root.as_fd(), OsStr::new("tmp"))?
            .filter(|_| request.profile == WholeProfile::Compilers)
        {
            add(&mut paths, request.build.join("tmp"), meta)?;
        }
        for entry in space::entries(root.as_fd())? {
            if request.profile == WholeProfile::Compilers
                && entry.to_str().and_then(stale_base) == Some("tmp")
            {
                add(
                    &mut paths,
                    request.build.join(&entry),
                    space::metadata_at(root.as_fd(), &entry)?,
                )?;
            }
        }
        // The actual host itself is a protected namespace, independently of
        // successful health observations or any naming-based selection. No
        // candidate may contain it (and therefore any installed/sysroot root).
        // This also protects internal callers which already hold a Request.
        let host_identity = space::Snapshot::metadata(&host.metadata()?).identity();
        for candidate in &paths {
            let (parent, leaf) = inventory.parent(relative(request, candidate)?)?;
            let candidate_identity = space::metadata_at(parent.as_fd(), &leaf)?.identity();
            if request.host.starts_with(candidate) || candidate_identity == host_identity {
                return Err(invalid(
                    "whole-tree candidate contains the protected original host/sysroot namespace",
                ));
            }
        }
        // A parent selection subsumes a nested leftover; no duplicate unlink.
        let all: Vec<_> = paths.into_iter().collect();
        let paths: Vec<_> = all
            .iter()
            .filter(|p| !all.iter().any(|parent| parent != *p && p.starts_with(parent)))
            .cloned()
            .collect();
        let mut locks = Vec::new();
        let mut candidates = Vec::new();
        for path in &paths {
            let rel = relative(request, path)?;
            let (parent, leaf) = inventory.parent(rel)?;
            let original = space::metadata_at(parent.as_fd(), &leaf)?;
            if !original.directory() {
                return Err(invalid("whole-tree candidate changed"));
            }
            let directory = space::open_at(parent.as_fd(), &leaf, true)?;
            if space::Snapshot::metadata(&directory.metadata()?) != original {
                return Err(invalid("selected tree changed before Cargo lock census"));
            }
            locks.push(CargoLocks::acquire_anchored(directory.as_fd())?);
            candidates.push(Candidate { path: path.clone(), original });
        }
        inventory.collect(&paths)?;
        let mut prepared = Self {
            candidates,
            inventory,
            kept: BTreeMap::new(),
            preserved,
            _locks: locks,
            detached: Vec::new(),
            removed_links: BTreeMap::new(),
            recreated_scratch: None,
        };
        prepared.kept = prepared.scan_kept()?;
        prepared.inventory.validate()?;
        output.check_current()?;
        Ok(prepared)
    }
    fn protect_original_inputs(
        &self,
        originals: impl IntoIterator<Item = (u64, u64)>,
    ) -> io::Result<()> {
        let selected = self.inventory.identities();
        if originals.into_iter().any(|identity| selected.contains(&identity)) {
            return Err(invalid(
                "whole-tree plan contains an actual retained native controller input",
            ));
        }
        Ok(())
    }
    fn scan_kept(&self) -> io::Result<BTreeMap<PathBuf, Kept>> {
        let doomed = self.inventory.identities();
        let mut selected = self
            .candidates
            .iter()
            .filter(|c| {
                !(self.recreated_scratch.is_some() && c.path == self.inventory_root().join("tmp"))
            })
            .map(|c| {
                (
                    c.path
                        .strip_prefix(self.inventory_root())
                        .expect("selected relative")
                        .to_owned(),
                    &c.original,
                )
            })
            .collect::<BTreeMap<_, _>>();
        selected.extend(self.detached.iter().map(|(path, original)| (path.clone(), original)));
        let (parent, leaf) = self.inventory.parent(Path::new(""))?;
        let mut result = BTreeMap::new();
        walk_kept(parent.as_fd(), &leaf, Path::new(""), &selected, &doomed, &mut result)?;
        Ok(result)
    }
    fn inventory_root(&self) -> &Path {
        self.inventory.root()
    }
}

fn hash_file(
    parent: BorrowedFd<'_>,
    name: &OsStr,
    expected: &space::Snapshot,
) -> io::Result<[u8; 32]> {
    let mut file = space::open_at(parent, name, false)?;
    if !expected.regular() || space::Snapshot::metadata(&file.metadata()?) != *expected {
        return Err(invalid("kept hardlink changed before hash"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0; 16384];
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hash.update(&buffer[..n]);
    }
    if space::Snapshot::metadata(&file.metadata()?) != *expected
        || space::metadata_at(parent, name)? != *expected
    {
        return Err(invalid("kept hardlink changed during hash"));
    }
    Ok(hash.finalize().into())
}
fn walk_kept(
    parent: BorrowedFd<'_>,
    name: &OsStr,
    path: &Path,
    selected: &BTreeMap<PathBuf, &space::Snapshot>,
    doomed: &BTreeSet<(u64, u64)>,
    result: &mut BTreeMap<PathBuf, Kept>,
) -> io::Result<()> {
    let before = space::metadata_at(parent, name)?;
    if let Some(original) = selected.get(path) {
        if !original.same_directory(&before) {
            return Err(invalid("selected root identity changed during kept census"));
        }
        return Ok(());
    }
    let mut target = None;
    let mut bytes = None;
    if before.directory() {
        let directory = space::open_at(parent, name, true)?;
        if space::Snapshot::metadata(&directory.metadata()?) != before {
            return Err(invalid("kept directory changed before enumeration"));
        }
        for child in space::entries(directory.as_fd())? {
            walk_kept(directory.as_fd(), &child, &path.join(&child), selected, doomed, result)?;
        }
        if space::metadata_at(parent, name)? != before
            || space::Snapshot::metadata(&directory.metadata()?) != before
        {
            return Err(invalid("kept directory changed during enumeration"));
        }
    } else if before.symlink() {
        let actual = links::preserved_target(parent, name, doomed)?;
        if space::metadata_at(parent, name)? != before {
            return Err(invalid(format!(
                "kept symlink {} changed during dependency census",
                path.display()
            )));
        }
        target = Some(actual);
    } else if before.regular() && doomed.contains(&before.identity()) {
        bytes = Some(hash_file(parent, name, &before)?);
    }
    result.insert(path.to_owned(), Kept { original: before, target, bytes });
    Ok(())
}

#[cfg(test)]
mod tests;

impl Prepared {
    fn check_kept(&self, removed: &BTreeMap<(u64, u64), u64>) -> io::Result<()> {
        let current = self.scan_kept()?;
        if current.keys().ne(self.kept.keys()) {
            return Err(invalid(
                "unselected output namespace changed during whole-tree maintenance",
            ));
        }
        for (path, prior) in &self.kept {
            let now = &current[path];
            let links = removed.get(&prior.original.identity()).copied().unwrap_or(0);
            let same = if prior.original.directory() {
                prior.original.same_directory(&now.original)
            } else {
                prior.original.after_our_unlinks(&now.original, links)
            };
            if !same || prior.target != now.target || prior.bytes != now.bytes {
                return Err(invalid(format!("preserved output changed: {}", path.display())));
            }
        }
        Ok(())
    }
    fn apply(
        &mut self,
        request: &WholeRequest,
        lease: &Lease,
        output: &OutputLock,
        report: &mut WholeReport,
    ) -> io::Result<()> {
        self.inventory.validate()?;
        for index in 0..self.candidates.len() {
            request.selection.check_current().map_err(invalid)?;
            lease.check_root(&request.root)?;
            output.check_root(&request.build)?;
            self.check_kept(&self.removed_links)?;
            let candidate = &self.candidates[index];
            let relative = relative(request, &candidate.path)?.to_owned();
            let (parent, name) = self.inventory.parent(&relative)?;
            if !candidate.original.same_directory(&space::metadata_at(parent.as_fd(), &name)?) {
                return Err(invalid("original whole-tree root changed before detach"));
            }
            let aside = if name.to_str().and_then(stale_base).is_some() {
                name.clone()
            } else {
                let mut value = name.clone();
                value.push(reclaim_suffix()?);
                value
            };
            if aside != name {
                rename_exclusive(parent.as_fd(), &name, &aside)?;
            }
            let aside_relative = relative.parent().unwrap_or(Path::new("")).join(&aside);
            self.detached.push((aside_relative, candidate.original.clone()));
            let result = remove_selected(
                parent.as_fd(),
                &aside,
                &relative,
                &self.inventory,
                &mut self.removed_links,
                &mut report.removed_allocated_bytes,
            );
            match result {
                Ok(()) => {
                    report.removed_trees.push(candidate.path.clone());
                    self.detached.pop();
                }
                Err(error) => {
                    report.failures.push(format!(
                        "{}: {error}; detached name {} retained",
                        candidate.path.display(),
                        Path::new(&aside).display()
                    ));
                    return Ok(());
                }
            }
        }
        lease.check_root(&request.root)?;
        output.check_root(&request.build)?;
        self.check_kept(&self.removed_links)?;
        // Scratch is a selected regenerable tree. Recreate it ONLY after all
        // original kept-name checks, using the actual held output directory.
        if self.candidates.iter().any(|c| c.path == request.build.join("tmp")) {
            let root = output.original_directory()?;
            let name = c"tmp";
            if unsafe { libc::mkdirat(root.as_raw_fd(), name.as_ptr(), 0o755) } != 0 {
                return Err(io::Error::last_os_error());
            }
            let original = space::metadata_at(root, OsStr::new("tmp"))?;
            self.recreated_scratch = Some(original.clone());
            self.kept.insert(PathBuf::from("tmp"), Kept { original, target: None, bytes: None });
        }
        Ok(())
    }
}
fn reclaim_suffix() -> io::Result<String> {
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQUENCE: AtomicU64 = AtomicU64::new(1);
    let time = SystemTime::now().duration_since(UNIX_EPOCH).map_err(io::Error::other)?.as_nanos();
    // Naming DATA only. Atomic no-replace rename supplies collision refusal;
    // neither this PID nor the stamp can grant stale-owner recovery.
    Ok(format!(
        "{RECLAIM_TAG}{}-{}",
        std::process::id(),
        time.checked_add(u128::from(SEQUENCE.fetch_add(1, Ordering::Relaxed)))
            .ok_or_else(|| invalid("reclaim name overflow"))?
    ))
}
fn cstring(name: &OsStr) -> io::Result<CString> {
    CString::new(name.as_bytes()).map_err(io::Error::other)
}
fn rename_exclusive(parent: BorrowedFd<'_>, old: &OsStr, new: &OsStr) -> io::Result<()> {
    let (old, new) = (cstring(old)?, cstring(new)?);
    #[cfg(target_os = "macos")]
    let result = unsafe {
        libc::renameatx_np(
            parent.as_raw_fd(),
            old.as_ptr(),
            parent.as_raw_fd(),
            new.as_ptr(),
            libc::RENAME_EXCL,
        )
    };
    #[cfg(target_os = "linux")]
    let result = unsafe {
        libc::renameat2(
            parent.as_raw_fd(),
            old.as_ptr(),
            parent.as_raw_fd(),
            new.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    };
    if result == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
}
fn remove_selected(
    parent: BorrowedFd<'_>,
    name: &OsStr,
    original_path: &Path,
    inventory: &space::Accounting,
    removed: &mut BTreeMap<(u64, u64), u64>,
    bytes: &mut u64,
) -> io::Result<()> {
    let original = inventory
        .original(original_path)
        .ok_or_else(|| invalid("new entry is outside original selected census"))?;
    let current = space::metadata_at(parent, name)?;
    if original.directory() {
        if !original.same_directory(&current) {
            return Err(invalid("selected directory changed before removal"));
        }
        let directory = space::open_at(parent, name, true)?;
        if !original.same_directory(&space::Snapshot::metadata(&directory.metadata()?)) {
            return Err(invalid("selected directory descriptor changed"));
        }
        for child in space::entries(directory.as_fd())? {
            remove_selected(
                directory.as_fd(),
                &child,
                &original_path.join(&child),
                inventory,
                removed,
                bytes,
            )?;
        }
        if !original.same_directory(&space::metadata_at(parent, name)?) {
            return Err(invalid("selected directory name changed during removal"));
        }
        let name = cstring(name)?;
        if unsafe { libc::unlinkat(parent.as_raw_fd(), name.as_ptr(), libc::AT_REMOVEDIR) } != 0 {
            return Err(io::Error::last_os_error());
        }
    } else {
        let prior = removed.get(&original.identity()).copied().unwrap_or(0);
        if !original.after_our_unlinks(&current, prior) {
            return Err(invalid("selected inode/link/content stamp changed before unlink"));
        }
        let name = cstring(name)?;
        if unsafe { libc::unlinkat(parent.as_raw_fd(), name.as_ptr(), 0) } != 0 {
            return Err(io::Error::last_os_error());
        }
        removed.insert(
            original.identity(),
            prior.checked_add(1).ok_or_else(|| invalid("removed-link census overflow"))?,
        );
        if current.links() == 1 {
            *bytes = bytes
                .checked_add(current.allocated_blocks()?)
                .ok_or_else(|| invalid("removed allocation overflow"))?;
        }
    }
    Ok(())
}

/// The actual original process/resource owner runs every health probe and is
/// retained through complete planning, preview, mutation and postchecks. No
/// saved Observation/JSON can be supplied in place of this executable owner.
#[cfg(all(feature = "native-cache-exec", target_os = "macos", target_arch = "aarch64"))]
pub fn reclaim(
    request: &WholeRequest,
    owner: &mut build_helper::admission::cache_probe::Owner,
) -> Result<WholeReport, String> {
    request.selection.check_current()?;
    let host = request.host.file_name().ok_or("missing actual cache host")?;
    let mut before = Vec::new();
    if request.profile == WholeProfile::SeedTools {
        before.push(owner.seed_tools(host, None).map_err(|e| e.to_string())?);
    } else {
        for stage in [1, 2] {
            before.push(owner.sysroot(host, stage, None).map_err(|e| e.to_string())?);
        }
    }
    if !before.iter().any(|s| s.complete) {
        return Err("selected whole-tree profile requires its actual contained compiler --version, original runtime and libstd observation".into());
    }
    let (lease, output) = owner.guards().map_err(|e| e.to_string())?;
    let mut prepared = Ownership::native(output, lease)
        .with_current(&request.root, &request.build, || Prepared::new(request, output))?
        .map_err(|e| e.to_string())?;
    let controller = owner.controller_inputs().map_err(|e| e.to_string())?;
    prepared
        .protect_original_inputs(
            std::iter::once(&controller.executable)
                .chain(&controller.runtime)
                .map(|file| (file.device, file.inode)),
        )
        .map_err(|e| e.to_string())?;
    let space = prepared.inventory.finish().map_err(|e| e.to_string())?;
    let volume =
        space::VolumeBefore::capture(output.original_directory().map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let mut report = WholeReport {
        profile: request.profile,
        dry_run: request.dry_run,
        compiler_caches: request.compiler_caches,
        planned_trees: prepared.candidates.iter().map(|c| c.path.clone()).collect(),
        removed_trees: Vec::new(),
        preserved: std::mem::take(&mut prepared.preserved),
        planned_file_space: space,
        volume_space: None,
        removed_allocated_bytes: 0,
        sysroots: before.iter().map(|s| (s.compiler.clone(), s.detail.clone())).collect(),
        failures: Vec::new(),
    };
    // Refuse an unrepresentable report BEFORE its first destructive action.
    serde_json::to_vec(&report).map_err(|e| e.to_string())?;
    if !request.dry_run {
        let result =
            Ownership::native(output, lease).with_current(&request.root, &request.build, || {
                prepared.apply(request, lease, output, &mut report)
            })?;
        if let Err(error) = result {
            report.failures.push(error.to_string());
        }
    }
    for prior in before.iter().filter(|s| s.complete) {
        let checked = if request.profile == WholeProfile::SeedTools {
            owner.seed_tools(host, Some(prior))
        } else {
            owner.sysroot(host, prior.stage(), Some(prior))
        };
        match checked {
            Ok(after) => {
                if !after.complete {
                    report
                        .failures
                        .push(format!("original sysroot postcheck failed: {}", after.detail));
                }
                report.sysroots.push((after.compiler, after.detail));
            }
            Err(error) => {
                report.failures.push(format!("original sysroot postcheck failed: {error}"));
                // A retained unknown probe can never turn into a report-only
                // success or permit the next probe. Only the actual idle
                // original owner can authorize continued observation.
                owner.guards().map_err(|e| format!("{error}; {e}"))?;
            }
        }
    }
    let (lease, output) = owner.guards().map_err(|e| e.to_string())?;
    if let Err(error) =
        Ownership::native(output, lease).with_current(&request.root, &request.build, || {
            prepared.check_kept(&prepared.removed_links)
        })?
    {
        report.failures.push(format!("preserved output postcheck failed: {error}"));
    }
    super::finish_selection(&request.selection, &mut report.failures);
    match volume.finish() {
        Ok(change) => report.volume_space = Some(change),
        Err(e) => report.failures.push(format!("volume observation unavailable: {e}")),
    }
    Ok(report)
}
