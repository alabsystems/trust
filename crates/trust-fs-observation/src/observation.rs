//! Trust: bounded content observations for declared build-script inputs.
//! Errors make the action uncacheable; this is no proof of undeclared-input completeness.

use std::fs::{self, Metadata, OpenOptions};
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};

use anyhow::{Context as _, Result as CargoResult, bail};
use serde::{Deserialize, Serialize};

use crate::file_identity::{
    metadata_is_plain_directory, metadata_is_plain_file, opened_file_identity,
};
use crate::{InputWork, Sha256};

const VERSION: u32 = 1;
const MAX_ENTRIES: u64 = 100_000;
const MAX_BYTES: u64 = 512 * 1024 * 1024;
const MAX_PATHS: usize = 16_384;
const MAX_LINKS: usize = 40;
const MAX_PATH_BYTES: usize = 32 * 1024;
const MAX_PREFIXES: usize = 4096;
const MAX_PREFIX_BYTES: usize = 2 * 1024 * 1024;
const MAX_RESOLUTION_STEPS: u64 = 4 * MAX_ENTRIES;
pub const MAX_RECORD: u64 = 16 * 1024 * 1024;

#[derive(Clone, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Snapshot {
    version: u32,
    entries: u64,
    bytes: u64,
    sha256: String,
}

impl Snapshot {
    pub fn valid(&self) -> bool {
        self.version == VERSION
            && self.entries <= MAX_ENTRIES
            && self.bytes <= MAX_BYTES
            && self.sha256.len() == 64
            && self
                .sha256
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    }
}

fn field(hash: &mut Option<Sha256>, bytes: &[u8]) {
    if let Some(hash) = hash {
        hash.update(&(bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
}

fn same(before: &Metadata, after: &Metadata) -> bool {
    if before.len() != after.len()
        || before.file_type() != after.file_type()
        || !matches!((before.modified(),after.modified()),(Ok(a),Ok(b)) if a == b)
    {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.mode() == after.mode()
            && before.uid() == after.uid()
            && before.gid() == after.gid()
            && before.ctime() == after.ctime()
            && before.ctime_nsec() == after.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        before.permissions().readonly() == after.permissions().readonly()
    }
}

struct Capture {
    hash: Option<Sha256>,
    entries: u64,
    bytes: u64,
    bytes_hashed: u64,
    // Trust: transient work accounting, never persisted freshness authority.
    metadata_reads: u64,
    resolution_steps: u64,
    link_reads: u64,
    revalidations: u64,
    observed: Vec<(PathBuf, Option<Metadata>)>,
    resolve_inputs: bool,
    reuse_prefixes: bool,
    // An originally observed, plain absolute root can be shared by inputs.
    // Its FIRST namespace stamps remain in observed through revalidation.
    plain_input_root: Option<PathBuf>,
    prefix_directories: std::collections::BTreeMap<PathBuf, Metadata>,
    prefix_bytes: usize,
    // Trust: recursive directory visits must not reserve a file read buffer
    // on every stack frame before the depth bound can reject the tree.
    read_buffer: Vec<u8>,
}

// Trust: only the digest is persisted. These original change stamps remain in
// the running action and prevent blessing post-execution bytes the script may
// never have read, including edit-and-restore changes during execution.
pub struct Observation {
    snapshot: Snapshot,
    observed: Vec<(PathBuf, Option<Metadata>)>,
}

impl Observation {
    pub fn into_snapshot(self) -> Snapshot {
        self.snapshot
    }

    /// Retain this full capture's original change stamps across an owning
    /// execution. Decoded snapshots cannot construct the returned window.
    pub fn into_parts(self) -> (Snapshot, Window) {
        (
            self.snapshot,
            Window {
                observed: self.observed,
            },
        )
    }
}

// Trust: execution-window custody has no content digest and cannot become a
// persisted Snapshot. Only a full post-execution Observation supplies that fact.
pub struct Window {
    observed: Vec<(PathBuf, Option<Metadata>)>,
}

// Trust: work survives a failed capture without entering any persisted
// fingerprint. Callers report the final outcome after execution-window checks.
pub struct Attempt<T> {
    pub result: CargoResult<T>,
    pub work: InputWork,
}

impl Window {
    /// Revalidate these factory-held original stamps at the current point.
    /// This reads metadata only; it neither restores a decoded window nor
    /// establishes a completed execution or a new content observation.
    pub fn is_current(&self) -> bool {
        #[cfg(unix)]
        {
            self.is_current_with(|path| fs::symlink_metadata(path))
        }
        #[cfg(not(unix))]
        {
            false
        }
    }

    #[cfg(unix)]
    fn is_current_with(
        &self,
        mut metadata: impl FnMut(&Path) -> std::io::Result<Metadata>,
    ) -> bool {
        self.observed
            .iter()
            .all(|(path, before)| match (before, metadata(path)) {
                (Some(before), Ok(after)) => same(before, &after),
                (None, Err(error)) => error.raw_os_error() == Some(libc::ENOENT),
                _ => false,
            })
    }

    pub fn covers(&self, after: &Observation) -> bool {
        // Other platforms without a reliable non-restorable change stamp are
        // conservatively uncacheable after execution.
        if !cfg!(unix) {
            return false;
        }
        let before: std::collections::BTreeMap<_, _> = self
            .observed
            .iter()
            .map(|(path, metadata)| (path, metadata))
            .collect();
        after.observed.iter().all(|(path, metadata)| {
            before
                .get(path)
                .is_some_and(|before| match (before, metadata) {
                    (Some(before), Some(after)) => same(before, after),
                    (None, None) => true,
                    _ => false,
                })
        })
    }
}

impl Capture {
    fn work(&self) -> InputWork {
        InputWork {
            entries: self.entries,
            input_bytes: self.bytes,
            bytes_hashed: self.bytes_hashed,
            metadata_reads: self.metadata_reads,
            resolution_steps: self.resolution_steps,
            link_reads: self.link_reads,
            observations: self.observed.len() as u64,
            revalidations: self.revalidations,
        }
    }
    fn new(purpose: Purpose, reuse_prefixes: bool) -> Self {
        let resolve_inputs = cfg!(unix) && !matches!(purpose, Purpose::Generated);
        let mut capture = Self {
            hash: match purpose {
                Purpose::Content | Purpose::Generated => Some(Sha256::new()),
                Purpose::Window => None,
            },
            entries: 0,
            bytes: 0,
            bytes_hashed: 0,
            metadata_reads: 0,
            resolution_steps: 0,
            link_reads: 0,
            revalidations: 0,
            observed: Vec::new(),
            // Windows lacks the native change-stamp guarantee used by Window.
            // Generated outputs retain their original strict symlink rejection.
            resolve_inputs,
            reuse_prefixes: reuse_prefixes && resolve_inputs,
            plain_input_root: None,
            prefix_directories: std::collections::BTreeMap::new(),
            prefix_bytes: 0,
            read_buffer: Vec::new(),
        };
        field(
            &mut capture.hash,
            match purpose {
                Purpose::Content | Purpose::Window => b"targo-build-script-input-content-v1",
                Purpose::Generated => b"targo-build-script-generated-content-v1",
            },
        );
        capture
    }

    fn path_metadata(&mut self, path: &Path) -> std::io::Result<Metadata> {
        self.metadata_reads += 1;
        fs::symlink_metadata(path)
    }

    // Trust: this is a per-capture syscall saving, never cached freshness.
    // Only successful plain directory prefixes are reused. Every logical
    // observation is still recorded and charged, and final validation reads
    // the original nodes again without consulting this map.
    fn prefix_metadata(&mut self, path: &Path) -> std::io::Result<Metadata> {
        if self.reuse_prefixes
            && let Some(metadata) = self.prefix_directories.get(path)
        {
            return Ok(metadata.clone());
        }
        let metadata = self.path_metadata(path)?;
        let bytes = path.as_os_str().as_encoded_bytes().len();
        if self.reuse_prefixes
            && metadata_is_plain_directory(&metadata)
            && self.prefix_directories.len() < MAX_PREFIXES
            && bytes <= MAX_PREFIX_BYTES - self.prefix_bytes
        {
            self.prefix_directories
                .insert(path.to_owned(), metadata.clone());
            self.prefix_bytes += bytes;
        }
        Ok(metadata)
    }

    fn revalidate(&mut self) -> CargoResult<()> {
        let validate =
            |path: &Path, before: &Option<Metadata>| match (before, fs::symlink_metadata(path)) {
                (Some(before), Ok(after)) if same(before, &after) => Ok(()),
                (None, Err(error)) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
                _ => bail!("build-script input inventory changed during capture"),
            };
        if self.reuse_prefixes {
            // Preserve the FIRST observation, including misses and links.
            // A fresh conflicting duplicate cannot replace original custody.
            let mut first: std::collections::BTreeMap<&Path, &Option<Metadata>> =
                std::collections::BTreeMap::new();
            for (path, metadata) in &self.observed {
                let original = first.entry(path.as_path()).or_insert(metadata);
                if !matches!((*original, metadata), (None, None))
                    && !matches!((*original, metadata), (Some(a), Some(b)) if same(a, b))
                {
                    bail!("conflicting build-script input observations during capture");
                }
            }
            for (path, before) in first {
                self.metadata_reads += 1;
                self.revalidations += 1;
                validate(path, before)?;
            }
        } else {
            for (path, before) in &self.observed {
                self.metadata_reads += 1;
                self.revalidations += 1;
                validate(path, before)?;
            }
        }
        Ok(())
    }

    fn record(&mut self, path: PathBuf, metadata: Option<Metadata>) -> CargoResult<()> {
        // Trust: repeated resolver nodes consume the same global bound as
        // visited inputs. Deduplication must not hide traversal work.
        if self.observed.len() >= MAX_ENTRIES as usize {
            bail!("build-script input observation count exceeds bound");
        }
        self.observed.push((path, metadata));
        Ok(())
    }

    // Trust: resolve only input paths, before reading either a leaf or its
    // children. Keep every original link and directory stamp through the
    // action; canonicalize alone would discard retarget-and-restore evidence.
    fn resolve_input(&mut self, path: &Path, label: &Path) -> CargoResult<PathBuf> {
        if !path.is_absolute() || path.as_os_str().as_encoded_bytes().len() > MAX_PATH_BYTES {
            bail!("build-script input path is not bounded and absolute");
        }
        let components = |path: &Path| {
            let mut components = path
                .components()
                .map(|component| component.as_os_str().to_owned())
                .collect::<std::collections::VecDeque<_>>();
            // Path::components removes a terminal slash or `/.`, but native
            // traversal requires the preceding node to be a directory.
            let bytes = path.as_os_str().as_encoded_bytes();
            if bytes.ends_with(b"/") || bytes.ends_with(b"/.") {
                components.push_back(".".into());
            }
            components
        };
        let suffix = self.plain_input_root.as_ref().and_then(|root| {
            path.strip_prefix(root)
                .ok()
                .map(|suffix| (root.clone(), suffix.to_owned()))
        });
        let (mut resolved, mut pending) = if let Some((root, suffix)) = suffix {
            let mut pending = components(&suffix);
            // strip_prefix may normalize a terminal slash or `/.` away.
            // Native traversal still requires the ORIGINAL path's final node
            // to be a directory, including a missing/file suffix.
            let original = path.as_os_str().as_encoded_bytes();
            if (original.ends_with(b"/") || original.ends_with(b"/."))
                && pending
                    .back()
                    .is_none_or(|part| part.as_os_str() != std::ffi::OsStr::new("."))
            {
                pending.push_back(".".into());
            }
            (root, pending)
        } else {
            let root = PathBuf::from("/");
            let metadata = self.prefix_metadata(&root)?;
            if !metadata_is_plain_directory(&metadata) {
                bail!("build-script input root is not a plain directory");
            }
            self.record(root.clone(), Some(metadata))?;
            (root, components(path))
        };
        let mut links = 0;
        while let Some(component) = pending.pop_front() {
            // Navigation-only paths also consume bounded work even when no
            // metadata observation is needed for a `..` or root component.
            if self.resolution_steps >= MAX_RESOLUTION_STEPS {
                bail!("build-script input resolution work exceeds bound");
            }
            self.resolution_steps += 1;
            match Path::new(&component).components().next() {
                Some(Component::RootDir) => resolved = PathBuf::from("/"),
                Some(Component::CurDir) => {}
                Some(Component::ParentDir) => {
                    resolved.pop();
                }
                Some(Component::Normal(_)) => {
                    let next = resolved.join(&component);
                    if next.as_os_str().as_encoded_bytes().len() > MAX_PATH_BYTES {
                        bail!("resolved build-script input path exceeds bound");
                    }
                    let metadata = match self.prefix_metadata(&next) {
                        Ok(metadata) => metadata,
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                            self.record(next.clone(), None)?;
                            // A missing ancestor is an input too. Do not
                            // normalize `missing/..` into an existing path.
                            let mut missing = next;
                            for component in pending {
                                if !matches!(
                                    Path::new(&component).components().next(),
                                    Some(Component::Normal(_))
                                ) {
                                    bail!("unresolved build-script input contains navigation");
                                }
                                missing.push(component);
                                if missing.as_os_str().as_encoded_bytes().len() > MAX_PATH_BYTES {
                                    bail!("missing build-script input path exceeds bound");
                                }
                            }
                            if links != 0 {
                                field(&mut self.hash, b"resolved-input");
                                field(&mut self.hash, missing.as_os_str().as_encoded_bytes());
                            }
                            return Ok(missing);
                        }
                        Err(error) => return Err(error.into()),
                    };
                    self.record(next.clone(), Some(metadata.clone()))?;
                    if metadata.file_type().is_symlink() {
                        links += 1;
                        if links > MAX_LINKS {
                            bail!("build-script input link traversal exceeds bound");
                        }
                        self.link_reads += 1;
                        let target = fs::read_link(&next)?;
                        let target_bytes = target.as_os_str().as_encoded_bytes();
                        if target_bytes.is_empty() || target_bytes.len() > MAX_PATH_BYTES {
                            bail!("build-script input link target exceeds bound");
                        }
                        self.bytes = self
                            .bytes
                            .checked_add(target_bytes.len() as u64)
                            .context("build-script input byte overflow")?;
                        if self.bytes > MAX_BYTES {
                            bail!("build-script inputs exceed byte bound");
                        }
                        field(&mut self.hash, b"input-link");
                        field(&mut self.hash, label.as_os_str().as_encoded_bytes());
                        field(&mut self.hash, next.as_os_str().as_encoded_bytes());
                        field(&mut self.hash, target_bytes);
                        for component in components(&target).into_iter().rev() {
                            pending.push_front(component);
                        }
                    } else if metadata_is_plain_directory(&metadata)
                        || (pending.is_empty() && metadata_is_plain_file(&metadata))
                    {
                        resolved = next;
                    } else {
                        bail!(
                            "build-script input traversal reached a non-directory or special node"
                        );
                    }
                }
                _ => bail!("unsupported build-script input path component"),
            }
        }
        if links != 0 {
            field(&mut self.hash, b"resolved-input");
            field(&mut self.hash, resolved.as_os_str().as_encoded_bytes());
        }
        Ok(resolved)
    }

    // Share only an absolute, originally plain root namespace. Every original
    // ancestor stamp remains in this capture; later input resolution and the
    // final revalidation cannot bless a replaced/restored root. Aliased roots
    // keep the full resolver and its exact per-input link hash representation.
    fn prepare_plain_input_root(&mut self, root: &Path) -> CargoResult<()> {
        if !self.reuse_prefixes
            || !root.is_absolute()
            || root
                .components()
                .any(|part| matches!(part, Component::ParentDir))
        {
            return Ok(());
        }
        if root.as_os_str().as_encoded_bytes().len() > MAX_PATH_BYTES {
            bail!("build-script input path is not bounded and absolute");
        }
        // Eligibility follows NO links and hashes NO extra input. Encountering
        // an alias/non-directory leaves the original full resolver in charge.
        let mut prefix = PathBuf::from("/");
        let metadata = self.prefix_metadata(&prefix)?;
        if !metadata_is_plain_directory(&metadata) {
            return Ok(());
        }
        self.record(prefix.clone(), Some(metadata))?;
        for part in root.components() {
            if self.resolution_steps >= MAX_RESOLUTION_STEPS {
                bail!("build-script input resolution work exceeds bound");
            }
            self.resolution_steps += 1;
            match part {
                Component::RootDir => continue,
                Component::Normal(name) => prefix.push(name),
                _ => return Ok(()),
            }
            let metadata = match self.prefix_metadata(&prefix) {
                Ok(metadata) if metadata_is_plain_directory(&metadata) => metadata,
                Ok(_) => return Ok(()),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
                Err(error) => return Err(error.into()),
            };
            self.record(prefix.clone(), Some(metadata))?;
        }
        self.plain_input_root = Some(prefix);
        Ok(())
    }

    fn observation(mut self) -> CargoResult<Observation> {
        let mut hash = self
            .hash
            .take()
            .context("content observation requires its digest")?;
        Ok(Observation {
            snapshot: Snapshot {
                version: VERSION,
                entries: self.entries,
                bytes: self.bytes,
                sha256: hash.finish_hex(),
            },
            observed: self.observed,
        })
    }

    fn visit(
        &mut self,
        path: &Path,
        label: &Path,
        recursive: bool,
        depth: usize,
    ) -> CargoResult<()> {
        self.entries += 1;
        if self.entries > MAX_ENTRIES || depth > 128 {
            bail!("build-script input inventory exceeds bound");
        }
        field(&mut self.hash, label.as_os_str().as_encoded_bytes());
        let resolved;
        let path = if self.resolve_inputs {
            resolved = self.resolve_input(path, label)?;
            resolved.as_path()
        } else {
            path
        };
        let metadata = match self.path_metadata(path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                field(&mut self.hash, b"missing");
                self.record(path.to_owned(), None)?;
                return Ok(());
            }
            Err(error) => return Err(error.into()),
        };
        self.record(path.to_owned(), Some(metadata.clone()))?;
        if let Some(hash) = &mut self.hash {
            hash.update(&[u8::from(metadata.permissions().readonly())]);
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            if let Some(hash) = &mut self.hash {
                hash.update(&metadata.mode().to_le_bytes());
            }
        }
        if metadata_is_plain_directory(&metadata) {
            field(&mut self.hash, b"directory");
            if recursive {
                let remaining = (MAX_ENTRIES - self.entries) as usize;
                let mut names = fs::read_dir(path)?
                    .take(remaining + 1)
                    .map(|entry| entry.map(|e| e.file_name()))
                    .collect::<std::io::Result<Vec<_>>>()?;
                names.sort_unstable();
                if names.len() as u64 > MAX_ENTRIES - self.entries {
                    bail!("build-script directory exceeds bound");
                }
                for name in names {
                    self.visit(&path.join(&name), &label.join(name), true, depth + 1)?;
                }
            }
        } else if metadata_is_plain_file(&metadata) {
            field(&mut self.hash, b"file");
            let mut options = OpenOptions::new();
            options.read(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt as _;
                options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
            }
            let mut file = options.open(path)?;
            let before = file.metadata()?;
            if !same(&metadata, &before) || !metadata_is_plain_file(&before) {
                bail!("build-script input changed before reading");
            }
            let identity = opened_file_identity(&file)?;
            self.bytes = self
                .bytes
                .checked_add(before.len())
                .context("build-script input byte overflow")?;
            if self.bytes > MAX_BYTES {
                bail!("build-script inputs exceed byte bound");
            }
            if let Some(hash) = &mut self.hash {
                hash.update(&before.len().to_le_bytes());
                let mut count = 0u64;
                self.read_buffer.resize(64 * 1024, 0);
                loop {
                    let n = file.read(&mut self.read_buffer)?;
                    if n == 0 {
                        break;
                    }
                    count += n as u64;
                    self.bytes_hashed += n as u64;
                    if count > before.len() {
                        bail!("build-script input grew while reading");
                    }
                    hash.update(&self.read_buffer[..n]);
                }
                if count != before.len() {
                    bail!("build-script input changed while reading");
                }
            }
            if !same(&before, &file.metadata()?)
                || identity != opened_file_identity(&options.open(path)?)?
            {
                bail!("build-script input changed while reading");
            }
        } else {
            bail!("linked or special build-script input is not content-cacheable");
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Purpose {
    Content,
    Window,
    Generated,
}

impl Purpose {
    fn label(self) -> &'static str {
        match self {
            Self::Content => "content",
            Self::Window => "window",
            Self::Generated => "generated-content",
        }
    }
}

fn scan(root: &Path, paths: &[PathBuf], recursive: bool, purpose: Purpose) -> CargoResult<Capture> {
    scan_with_prefix_reuse(root, paths, recursive, purpose, true)
}

fn scan_with_prefix_reuse(
    root: &Path,
    paths: &[PathBuf],
    recursive: bool,
    purpose: Purpose,
    reuse_prefixes: bool,
) -> CargoResult<Capture> {
    scan_attempt(root, paths, recursive, purpose, reuse_prefixes).result
}

fn scan_attempt(
    root: &Path,
    paths: &[PathBuf],
    recursive: bool,
    purpose: Purpose,
    reuse_prefixes: bool,
) -> Attempt<Capture> {
    let mut capture = Capture::new(purpose, reuse_prefixes);
    let result = scan_into(root, paths, recursive, purpose, &mut capture);
    let work = capture.work();
    Attempt {
        result: result.map(|()| capture),
        work,
    }
}

// Only an optimization candidate, never an admitted input or a path rewrite.
// A bounded pass may broaden the package root to a shared ancestor of declared
// absolute watches. The actual plain-namespace eligibility/first-stamp capture
// and every original input traversal still follow below.
fn shared_input_namespace(root: &Path, paths: &[PathBuf]) -> PathBuf {
    let mut shared = root.to_owned();
    let mut examined = 0usize;
    for path in paths {
        let absolute = root.join(path);
        let bytes = absolute.as_os_str().as_encoded_bytes().len();
        // Keep this optional analysis bounded by the existing record bound.
        // Fall back to the original package root, never drop an input.
        let Some(next) = examined.checked_add(bytes) else {
            return root.to_owned();
        };
        if bytes > MAX_PATH_BYTES || next > MAX_RECORD as usize {
            return root.to_owned();
        }
        examined = next;
        if !absolute.starts_with(&shared) {
            // Trim once in component order rather than repeatedly rescanning
            // a long common prefix after each pop.
            let common: PathBuf = shared
                .components()
                .zip(absolute.components())
                .take_while(|(left, right)| left == right)
                .map(|(part, _)| part.as_os_str())
                .collect();
            if common.as_os_str().is_empty() {
                return root.to_owned();
            }
            shared = common;
        }
    }
    shared
}

fn scan_into(
    root: &Path,
    paths: &[PathBuf],
    recursive: bool,
    purpose: Purpose,
    capture: &mut Capture,
) -> CargoResult<()> {
    if paths.len() > MAX_PATHS {
        bail!("build-script declared path count exceeds bound");
    }
    if !paths.is_empty() && capture.resolve_inputs {
        capture.prepare_plain_input_root(&shared_input_namespace(root, paths))?;
    }
    for path in paths {
        capture.visit(&root.join(path), path, recursive, 0)?;
    }
    // Trust: a leaf can be restored unchanged after a different directory or
    // a previously missing input was transiently used. Retain ancestor stamps
    // through the action as well, without making their timestamps cache keys.
    let mut directories = std::collections::BTreeSet::new();
    for (path, _) in &capture.observed {
        if capture.resolve_inputs {
            // Input traversal already retained ancestry before leaf reads.
            continue;
        }
        let in_package = path.starts_with(root);
        for directory in path.ancestors().skip(1) {
            if in_package && !directory.starts_with(root) {
                break;
            }
            directories.insert(directory.to_owned());
            if capture.observed.len() + directories.len() > MAX_ENTRIES as usize {
                bail!("build-script ancestor count exceeds bound");
            }
        }
    }
    for directory in directories {
        let metadata = match capture.path_metadata(&directory) {
            Ok(metadata) if metadata_is_plain_directory(&metadata) => Some(metadata),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            _ => bail!("build-script input ancestor is not a plain directory"),
        };
        capture.record(directory, metadata)?;
    }
    capture.revalidate()?;
    if matches!(purpose, Purpose::Generated) {
        tracing::debug!(
            target: "targo::compiler::fingerprint::build_script_output",
            output_bytes = capture.bytes,
            bytes_hashed = capture.bytes_hashed,
            entries = capture.entries,
            "observed generated output tree"
        );
    } else {
        tracing::debug!(
          target: "targo::compiler::fingerprint::build_script_inputs",
          capture_kind = purpose.label(),
          input_bytes = capture.bytes,
          bytes_hashed = capture.bytes_hashed,
          entries = capture.entries,
          metadata_reads = capture.metadata_reads,
          resolution_steps = capture.resolution_steps,
          link_reads = capture.link_reads,
          observations = capture.observed.len(),
          revalidations = capture.revalidations,
          "observed build-script inputs"
        );
    }
    Ok(())
}

#[cfg(any(test, feature = "test-support"))]
pub fn window(root: &Path, paths: &[PathBuf], recursive: bool) -> CargoResult<Window> {
    window_attempt(root, paths, recursive).result
}

#[cfg(any(test, feature = "test-support"))]
pub fn observe(root: &Path, paths: &[PathBuf], recursive: bool) -> CargoResult<Observation> {
    observe_attempt(root, paths, recursive).result
}

pub fn window_attempt(root: &Path, paths: &[PathBuf], recursive: bool) -> Attempt<Window> {
    let attempt = scan_attempt(root, paths, recursive, Purpose::Window, true);
    Attempt {
        result: attempt.result.map(|capture| Window {
            observed: capture.observed,
        }),
        work: attempt.work,
    }
}

pub fn observe_attempt(root: &Path, paths: &[PathBuf], recursive: bool) -> Attempt<Observation> {
    let attempt = scan_attempt(root, paths, recursive, Purpose::Content, true);
    Attempt {
        result: attempt.result.and_then(Capture::observation),
        work: attempt.work,
    }
}

// Trust: generated artifacts use the same bounded content inventory. Visit
// the exact root leaf: joining an empty path would append a slash and could
// follow a directory symlink before symlink_metadata sees it.
pub fn capture_tree(root: &Path) -> CargoResult<Snapshot> {
    let before = fs::symlink_metadata(root)?;
    if !metadata_is_plain_directory(&before) {
        bail!("build-script output root is not a plain directory");
    }
    let parent = root.parent().context("output root has no parent")?;
    let name = root.file_name().context("output root has no name")?;
    let observation =
        scan(parent, &[PathBuf::from(name)], true, Purpose::Generated)?.observation()?;
    if !same(&before, &fs::symlink_metadata(root)?) {
        bail!("build-script output root changed during capture");
    }
    Ok(observation.into_snapshot())
}

#[cfg(any(test, feature = "test-support"))]
pub fn capture(root: &Path, paths: &[PathBuf], recursive: bool) -> CargoResult<Snapshot> {
    observe(root, paths, recursive).map(Observation::into_snapshot)
}

pub fn read_record(path: &Path) -> CargoResult<String> {
    let before = fs::symlink_metadata(path)?;
    if !metadata_is_plain_file(&before) {
        bail!("build-script fingerprint record is not a plain file");
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let mut file = options.open(path)?;
    if !same(&before, &file.metadata()?) || file.metadata()?.len() > MAX_RECORD {
        bail!("build-script fingerprint record is invalid or exceeds bound");
    }
    let mut text = String::new();
    (&mut file).take(MAX_RECORD + 1).read_to_string(&mut text)?;
    if text.len() as u64 > MAX_RECORD {
        bail!("build-script fingerprint record grew beyond bound");
    }
    if !same(&before, &file.metadata()?) || !same(&before, &fs::symlink_metadata(path)?) {
        bail!("build-script fingerprint record changed during read");
    }
    Ok(text)
}

/// Runs a test `body` on a fresh world until no directory above the world changed
/// while it ran, and returns its outcome. A capture records every directory from `/`
/// down to its inputs, times included, and fails or stops covering when one of them
/// changes. So the worlds live beside the test binary, in its target directory, away
/// from the shared temporary directory that every compiler on the machine adds entries
/// to, and one body runs at a time. That makes a change above the world rare, not
/// impossible: no lock is held while tests run, other builds may share the target
/// directory, and anything may write to the directories above it. So a change is
/// detected instead, with `same`, the comparison the capture itself uses: when the
/// stamps above the world are the same before and after the body, its outcome, pass or
/// fail, stands; otherwise the run is redone on a fresh world, and the retry is written
/// to the test's output. A retry can only replace an outcome seen while something above
/// the world changed, so a deterministic failure fails on every attempt. A change undone
/// within one tick of a coarse file-system clock can slip past both comparisons, and a
/// failure it caused then stands: a rare flake, never a pass. Production makes no such
/// retry: there a capture that saw a change leaves its unit uncacheable.
#[cfg(any(test, feature = "test-support"))]
pub fn settled<T>(mut body: impl FnMut(&tempfile::TempDir) -> T) -> T {
    const ATTEMPTS: u64 = 20;
    static ONE_AT_A_TIME: std::sync::Mutex<()> = std::sync::Mutex::new(());
    static WORLDS: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    let _turn = ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let worlds = WORLDS.get_or_init(|| {
        // Two levels above the test binary, in its target directory: `<profile>` for
        // `<profile>/deps/<binary>`, the unit's own directory for `<unit>/out/<binary>`.
        let exe = std::env::current_exe().unwrap();
        let worlds = exe
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("targo-core-test-worlds");
        fs::create_dir_all(&worlds).unwrap();
        worlds.canonicalize().unwrap()
    });
    let stamps = |root: &Path| -> Vec<Option<Metadata>> {
        root.ancestors()
            .skip(1)
            .map(|directory| fs::symlink_metadata(directory).ok())
            .collect()
    };
    for attempt in 0..ATTEMPTS {
        let world = tempfile::tempdir_in(worlds).unwrap();
        let root = world.path().canonicalize().unwrap();
        let before = stamps(&root);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| body(&world)));
        let after = stamps(&root);
        let quiet = before.len() == after.len()
            && before
                .iter()
                .zip(&after)
                .all(|(before, after)| match (before, after) {
                    (Some(before), Some(after)) => same(before, after),
                    (None, None) => true,
                    _ => false,
                });
        if quiet {
            return outcome.unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        }
        eprintln!(
            "settled: a directory above the test world changed during attempt {}; \
             rerunning on a fresh world",
            attempt + 1
        );
        drop(world);
        std::thread::sleep(std::time::Duration::from_millis(5 * (attempt + 1)));
    }
    panic!("a directory above the test world changed during each of {ATTEMPTS} attempts");
}

#[cfg(test)]
mod tests {
    use std::fs::{File, FileTimes};

    use super::*;

    #[cfg(unix)]
    #[test]
    fn current_window_keeps_original_stamps_after_content_restore() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let path = root.join("value");
            fs::write(&path, b"one").unwrap();
            let (snapshot, window) =
                observe_attempt(Path::new("/"), std::slice::from_ref(&path), false)
                    .result
                    .unwrap()
                    .into_parts();
            assert!(window.is_current());
            fs::write(&path, b"two").unwrap();
            assert!(!window.is_current());
            fs::write(&path, b"one").unwrap();
            assert_eq!(
                capture(Path::new("/"), std::slice::from_ref(&path), false).unwrap(),
                snapshot
            );
            assert!(!window.is_current());
        });
    }

    #[cfg(unix)]
    #[test]
    fn current_window_missing_is_only_enoent_and_errors_refuse() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let missing = root.join("missing");
            let (_, window) =
                observe_attempt(Path::new("/"), std::slice::from_ref(&missing), false)
                    .result
                    .unwrap()
                    .into_parts();
            assert!(window.is_current());
            for code in [libc::EACCES, libc::ENOTDIR, libc::ELOOP, libc::EINVAL] {
                assert!(!window.is_current_with(|path| {
                    if path == missing {
                        Err(std::io::Error::from_raw_os_error(code))
                    } else {
                        fs::symlink_metadata(path)
                    }
                }));
            }
            assert!(window.is_current_with(|path| {
                if path == missing {
                    Err(std::io::Error::from_raw_os_error(libc::ENOENT))
                } else {
                    fs::symlink_metadata(path)
                }
            }));
            fs::write(&missing, b"appeared").unwrap();
            assert!(!window.is_current());
        });
    }

    #[test]
    fn empty_v1_snapshot_wire_and_digest_are_frozen() {
        // Independently calculated SHA256 of the original length-prefixed
        // domain field, with no filesystem entries or platform metadata.
        let snapshot = capture(Path::new("unused"), &[], false).unwrap();
        assert_eq!(
            serde_json::to_string(&snapshot).unwrap(),
            "{\"version\":1,\"entries\":0,\"bytes\":0,\"sha256\":\"152728eb801b188599be49360751d56abc7dc76bb32431e4236506ffc3004363\"}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn regular_file_v1_snapshot_wire_and_digest_are_frozen() {
        use std::os::unix::fs::PermissionsExt as _;
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let path = root.join("value");
            fs::write(&path, b"abc").unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
            let snapshot = capture(&root, &[PathBuf::from("value")], false).unwrap();
            // Original framing: domain, label, readonly byte, Unix mode,
            // file tag, u64 length, then the exact three file bytes.
            assert_eq!(
                serde_json::to_string(&snapshot).unwrap(),
                "{\"version\":1,\"entries\":1,\"bytes\":3,\"sha256\":\"12592de129aac3b66f4873cf918ae4d09a6ce2e2870c560ee3b36dc74344158b\"}"
            );
        });
    }

    #[test]
    #[should_panic(expected = "the body's own failure")]
    fn settled_keeps_a_failure_seen_while_nothing_above_the_world_changed() {
        settled(|_| panic!("the body's own failure"))
    }

    #[test]
    fn settled_reruns_a_body_that_saw_a_directory_above_the_world_change() {
        let mut attempts = 0;
        let ran = settled(|world| {
            attempts += 1;
            if attempts == 1 {
                // Siblings of the world appear and go until the parent's stamp moves as
                // `same` sees it: where the clock is coarse, one sibling made in the
                // same tick as the world leaves the parent's times as they were.
                let parent = world
                    .path()
                    .canonicalize()
                    .unwrap()
                    .parent()
                    .unwrap()
                    .to_owned();
                let start = fs::symlink_metadata(&parent).unwrap();
                for _ in 0..2000 {
                    tempfile::tempdir_in(&parent).unwrap();
                    if !same(&start, &fs::symlink_metadata(&parent).unwrap()) {
                        panic!("a failure caused by the change above the world");
                    }
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
                unreachable!("the parent's stamp never moved in two seconds");
            }
            attempts
        });
        assert!(ran >= 2);
    }

    #[cfg(unix)]
    #[test]
    fn prefix_reuse_preserves_the_exact_snapshot_and_logical_work() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::create_dir(root.join("inputs")).unwrap();
            for index in 0..32 {
                fs::write(root.join(format!("inputs/value-{index}")), b"111").unwrap();
            }
            std::os::unix::fs::symlink("inputs", root.join("relative")).unwrap();
            std::os::unix::fs::symlink(root.join("relative"), root.join("absolute")).unwrap();
            let paths = [
                PathBuf::from("inputs"),
                PathBuf::from("relative"),
                PathBuf::from("absolute"),
                PathBuf::from("optional"),
            ];
            let reference =
                scan_with_prefix_reuse(&root, &paths, true, Purpose::Content, false).unwrap();
            let reused =
                scan_with_prefix_reuse(&root, &paths, true, Purpose::Content, true).unwrap();
            assert!(reused.metadata_reads < reference.metadata_reads / 2);
            assert!(reused.revalidations < reference.revalidations);
            assert!(reused.observed.len() < reference.observed.len());
            assert!(reused.resolution_steps < reference.resolution_steps);
            assert_eq!(reused.bytes_hashed, reference.bytes_hashed);
            assert_eq!(reused.link_reads, reference.link_reads);
            assert_eq!(
                reused.observation().unwrap().snapshot,
                reference.observation().unwrap().snapshot
            );
        })
    }

    #[cfg(unix)]
    #[test]
    fn shared_plain_root_keeps_large_declared_inputs_within_original_bounds() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap().join("owner/a/b/c/d");
            fs::create_dir_all(root.join("inputs/a/b/c/d")).unwrap();
            let paths: Vec<_> = (0..9000)
                .map(|n| {
                    let path = PathBuf::from(format!("inputs/a/b/c/d/{n}"));
                    fs::write(root.join(&path), b"stable").unwrap();
                    path
                })
                .collect();
            let reference = scan_with_prefix_reuse(&root, &paths, false, Purpose::Window, false)
                .err()
                .expect("full root traversal exhausts the unchanged observation bound");
            assert!(
                reference
                    .to_string()
                    .contains("observation count exceeds bound")
            );
            let before = window_attempt(&root, &paths, false).result.unwrap();
            let after = observe_attempt(&root, &paths, false).result.unwrap();
            assert_eq!(after.snapshot.entries, 9000);
            assert!(before.covers(&after));
            fs::write(root.join(&paths[0]), b"changed").unwrap();
            assert!(!before.covers(&observe_attempt(&root, &paths, false).result.unwrap()));
        })
    }

    #[cfg(unix)]
    #[test]
    fn shared_plain_root_retains_first_namespace_through_same_leaf_aba() {
        settled(|world| {
            let base = world.path().canonicalize().unwrap();
            let root = base.join("root");
            let replacement = base.join("replacement");
            fs::create_dir(&root).unwrap();
            fs::create_dir(&replacement).unwrap();
            fs::write(root.join("first"), b"111").unwrap();
            fs::write(root.join("second"), b"222").unwrap();
            fs::hard_link(root.join("second"), replacement.join("second")).unwrap();
            let leaf = fs::symlink_metadata(root.join("second")).unwrap();
            let mut capture = Capture::new(Purpose::Content, true);
            capture.prepare_plain_input_root(&root).unwrap();
            assert_eq!(capture.plain_input_root.as_deref(), Some(root.as_path()));
            capture
                .visit(&root.join("first"), Path::new("first"), false, 0)
                .unwrap();
            fs::rename(&root, base.join("saved")).unwrap();
            fs::rename(&replacement, &root).unwrap();
            capture
                .visit(&root.join("second"), Path::new("second"), false, 0)
                .unwrap();
            fs::rename(&root, &replacement).unwrap();
            fs::rename(base.join("saved"), &root).unwrap();
            assert!(same(
                &leaf,
                &fs::symlink_metadata(root.join("second")).unwrap()
            ));
            assert!(
                capture
                    .revalidate()
                    .unwrap_err()
                    .to_string()
                    .contains("inventory changed")
            );
        })
    }

    #[cfg(unix)]
    #[test]
    fn aliased_roots_keep_exact_per_input_link_hashes() {
        settled(|world| {
            let base = world.path().canonicalize().unwrap();
            fs::create_dir(base.join("root")).unwrap();
            fs::write(base.join("root/value"), b"111").unwrap();
            let alias = base.join("alias");
            std::os::unix::fs::symlink("root", &alias).unwrap();
            let paths = [PathBuf::from("value")];
            let reference =
                scan_with_prefix_reuse(&alias, &paths, false, Purpose::Content, false).unwrap();
            let reused =
                scan_with_prefix_reuse(&alias, &paths, false, Purpose::Content, true).unwrap();
            assert!(reused.plain_input_root.is_none());
            assert_eq!(
                reused.observation().unwrap().snapshot,
                reference.observation().unwrap().snapshot
            );
        })
    }

    #[cfg(unix)]
    #[test]
    fn plain_dot_root_keeps_suffix_link_hash_representation() {
        settled(|world| {
            let base = world.path().canonicalize().unwrap();
            fs::create_dir(base.join("root")).unwrap();
            fs::write(base.join("root/value"), b"111").unwrap();
            std::os::unix::fs::symlink("value", base.join("root/link")).unwrap();
            let lexical = base.join("root/./");
            let paths = [PathBuf::from("link")];
            let reference =
                scan_with_prefix_reuse(&lexical, &paths, false, Purpose::Content, false).unwrap();
            let reused =
                scan_with_prefix_reuse(&lexical, &paths, false, Purpose::Content, true).unwrap();
            assert_eq!(
                reused.plain_input_root.as_deref(),
                Some(base.join("root").as_path())
            );
            assert_eq!(
                reused.observation().unwrap().snapshot,
                reference.observation().unwrap().snapshot
            );
        })
    }

    #[cfg(unix)]
    #[test]
    fn external_declared_inputs_share_namespace_without_becoming_package_files() {
        settled(|world| {
            let base = world
                .path()
                .canonicalize()
                .unwrap()
                .join("workspace/a/b/c/d");
            let root = base.join("package");
            fs::create_dir_all(&root).unwrap();
            fs::create_dir_all(base.join("shared/a/b/c/d")).unwrap();
            fs::write(root.join("local"), b"local").unwrap();
            let mut paths = vec![PathBuf::from("local")];
            paths.extend((0..9000).map(|n| {
                let path = base.join(format!("shared/a/b/c/d/{n}"));
                fs::write(&path, b"stable").unwrap();
                path
            }));
            assert_eq!(shared_input_namespace(&root, &paths), base);
            let before = window_attempt(&root, &paths, false).result.unwrap();
            let after = observe_attempt(&root, &paths, false).result.unwrap();
            assert_eq!(after.snapshot.entries, 9001);
            assert!(before.covers(&after));
            fs::write(paths.last().unwrap(), b"changed").unwrap();
            assert!(!before.covers(&observe_attempt(&root, &paths, false).result.unwrap()));
        })
    }

    #[test]
    fn namespace_analysis_limit_falls_back_without_discarding_declared_inputs() {
        let root = Path::new("/package");
        let oversized = vec![PathBuf::from(format!(
            "/elsewhere/{}",
            "x".repeat(MAX_PATH_BYTES + 1)
        ))];
        assert_eq!(shared_input_namespace(root, &oversized), root);
        let many = vec![
            PathBuf::from(format!("/elsewhere/{}", "x".repeat(2048)));
            MAX_RECORD as usize / 2048 + 1
        ];
        assert_eq!(shared_input_namespace(root, &many), root);
        assert_eq!(
            shared_input_namespace(root, &[PathBuf::from("/elsewhere/value")]),
            Path::new("/")
        );
    }

    #[cfg(unix)]
    #[test]
    fn external_watches_keep_aliased_package_root_link_hashes() {
        settled(|world| {
            let base = world.path().canonicalize().unwrap();
            fs::create_dir(base.join("package")).unwrap();
            fs::write(base.join("package/value"), b"local").unwrap();
            fs::write(base.join("external"), b"outside").unwrap();
            let alias = base.join("alias");
            std::os::unix::fs::symlink("package", &alias).unwrap();
            let paths = [PathBuf::from("value"), base.join("external")];
            assert_eq!(shared_input_namespace(&alias, &paths), base);
            let reference =
                scan_with_prefix_reuse(&alias, &paths, false, Purpose::Content, false).unwrap();
            let reused =
                scan_with_prefix_reuse(&alias, &paths, false, Purpose::Content, true).unwrap();
            assert_eq!(reused.plain_input_root.as_deref(), Some(base.as_path()));
            assert_eq!(
                reused.observation().unwrap().snapshot,
                reference.observation().unwrap().snapshot
            );
        })
    }

    #[cfg(unix)]
    #[test]
    fn one_capture_retains_original_prefix_custody_through_same_leaf_aba() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::create_dir(root.join("prefix")).unwrap();
            fs::create_dir(root.join("replacement")).unwrap();
            fs::write(root.join("prefix/first"), b"111").unwrap();
            fs::write(root.join("prefix/second"), b"222").unwrap();
            // The second leaf has the SAME inode throughout the directory swap;
            // only retained namespace ancestry can expose the restored generation.
            fs::hard_link(root.join("prefix/second"), root.join("replacement/second")).unwrap();
            let leaf = fs::symlink_metadata(root.join("prefix/second")).unwrap();
            let mut capture = Capture::new(Purpose::Content, true);
            capture
                .visit(
                    &root.join("prefix/first"),
                    Path::new("prefix/first"),
                    false,
                    0,
                )
                .unwrap();
            fs::rename(root.join("prefix"), root.join("saved")).unwrap();
            fs::rename(root.join("replacement"), root.join("prefix")).unwrap();
            capture
                .visit(
                    &root.join("prefix/second"),
                    Path::new("prefix/second"),
                    false,
                    0,
                )
                .unwrap();
            fs::rename(root.join("prefix"), root.join("replacement")).unwrap();
            fs::rename(root.join("saved"), root.join("prefix")).unwrap();
            assert!(same(
                &leaf,
                &fs::symlink_metadata(root.join("prefix/second")).unwrap()
            ));
            let error = capture.revalidate().unwrap_err().to_string();
            assert!(error.contains("inventory changed"), "{error}");
        })
    }

    #[cfg(unix)]
    #[test]
    fn fresh_conflicting_duplicates_cannot_replace_first_observations() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let path = root.join("value");
            let mut capture = Capture::new(Purpose::Content, true);
            capture.record(path.clone(), None).unwrap();
            fs::write(&path, b"111").unwrap();
            capture
                .record(path.clone(), Some(fs::symlink_metadata(&path).unwrap()))
                .unwrap();
            assert!(
                capture
                    .revalidate()
                    .unwrap_err()
                    .to_string()
                    .contains("conflicting")
            );
            let mut capture = Capture::new(Purpose::Content, true);
            capture
                .record(path.clone(), Some(fs::symlink_metadata(&path).unwrap()))
                .unwrap();
            fs::write(&path, b"2222").unwrap();
            capture
                .record(path.clone(), Some(fs::symlink_metadata(&path).unwrap()))
                .unwrap();
            assert!(
                capture
                    .revalidate()
                    .unwrap_err()
                    .to_string()
                    .contains("conflicting")
            );
        })
    }

    #[cfg(unix)]
    #[test]
    fn reuse_does_not_enlarge_the_logical_observation_budget() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            // Force real suffix traversal past the unchanged observation
            // bound, independently of how deeply the temporary root lives.
            fs::create_dir_all(root.join("a/b/c/d/e/f")).unwrap();
            fs::write(root.join("a/b/c/d/e/f/value"), b"111").unwrap();
            let paths = vec![PathBuf::from("a/b/c/d/e/f/value"); MAX_PATHS];
            for reuse in [false, true] {
                let error = scan_with_prefix_reuse(&root, &paths, false, Purpose::Window, reuse)
                    .err()
                    .expect("repeated logical work must remain bounded")
                    .to_string();
                assert!(error.contains("observation count exceeds bound"), "{error}");
            }
        })
    }

    #[cfg(unix)]
    #[test]
    fn saturated_prefix_caches_fall_back_to_live_metadata() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            for long in [false, true] {
                let mut base = root.join(if long { "long" } else { "short" });
                if long {
                    for _ in 0..9 {
                        base.push("prefix".repeat(10));
                    }
                }
                fs::create_dir_all(&base).unwrap();
                let mut paths = Vec::new();
                for index in 0..=MAX_PREFIXES {
                    let path = base.join(format!("d{index}"));
                    fs::create_dir(&path).unwrap();
                    paths.push(path);
                }
                // Exercise the prefix cache itself. Scanning thousands of
                // absolute inputs also charges every repeated ancestor to the
                // independent observation bound, which depends on the test
                // binary's directory depth and can expire before saturation.
                let mut capture = Capture::new(Purpose::Content, true);
                for path in &paths {
                    capture.prefix_metadata(path).unwrap();
                }
                assert!(capture.prefix_directories.len() <= MAX_PREFIXES);
                assert!(capture.prefix_bytes <= MAX_PREFIX_BYTES);
                if long {
                    assert!(capture.prefix_directories.len() < MAX_PREFIXES);
                } else if paths
                    .iter()
                    .map(|path| path.as_os_str().as_encoded_bytes().len())
                    .max()
                    .unwrap()
                    <= MAX_PREFIX_BYTES / MAX_PREFIXES
                {
                    assert_eq!(capture.prefix_directories.len(), MAX_PREFIXES);
                }
                let last = paths.last().unwrap();
                assert!(!capture.prefix_directories.contains_key(last));
                assert!(
                    capture.prefix_directories.len() == MAX_PREFIXES
                        || capture.prefix_bytes + last.as_os_str().as_encoded_bytes().len()
                            > MAX_PREFIX_BYTES
                );
                // An uncached prefix must observe the replacement, rather
                // than retain the directory metadata from saturation.
                fs::remove_dir(last).unwrap();
                fs::write(last, b"replacement").unwrap();
                let reads = capture.metadata_reads;
                assert!(capture.prefix_metadata(last).unwrap().is_file());
                assert!(capture.prefix_metadata(last).unwrap().is_file());
                assert_eq!(capture.metadata_reads, reads + 2);
                assert!(!capture.prefix_directories.contains_key(last));
            }
        })
    }

    #[cfg(unix)]
    #[test]
    fn navigation_without_observations_has_a_separate_work_bound() {
        let mut capture = Capture::new(Purpose::Window, true);
        let path = PathBuf::from(format!("/{}", "../".repeat(4000)));
        loop {
            match capture.resolve_input(&path, &path) {
                Ok(_) => {}
                Err(error) => {
                    assert!(error.to_string().contains("resolution work exceeds bound"));
                    assert_eq!(capture.resolution_steps, MAX_RESOLUTION_STEPS);
                    break;
                }
            }
        }
    }

    #[test]
    fn restored_mtime_changes_content_but_timestamp_only_edits_do_not() {
        settled(|world| {
            let path = world.path().join("schema");
            fs::write(&path, b"111").unwrap();
            let old = fs::metadata(&path).unwrap().modified().unwrap();
            let paths = vec![PathBuf::from("schema")];
            let first = capture(world.path(), &paths, true).unwrap();
            fs::write(&path, b"222").unwrap();
            File::open(&path)
                .unwrap()
                .set_times(FileTimes::new().set_modified(old))
                .unwrap();
            let second = capture(world.path(), &paths, true).unwrap();
            assert_ne!(first, second);
            File::open(&path)
                .unwrap()
                .set_times(FileTimes::new().set_modified(old + std::time::Duration::from_secs(1)))
                .unwrap();
            assert_eq!(second, capture(world.path(), &paths, true).unwrap());
        })
    }

    #[test]
    fn directory_membership_missing_and_type_changes_are_inputs() {
        settled(|world| {
            let path = world.path().join("input");
            let paths = vec![PathBuf::from("input")];
            let missing = capture(world.path(), &paths, true).unwrap();
            fs::create_dir(&path).unwrap();
            let empty = capture(world.path(), &paths, true).unwrap();
            assert_ne!(missing, empty);
            fs::write(path.join("schema"), b"value").unwrap();
            let populated = capture(world.path(), &paths, true).unwrap();
            assert_ne!(empty, populated);
            fs::remove_file(path.join("schema")).unwrap();
            fs::remove_dir(&path).unwrap();
            fs::write(&path, b"value").unwrap();
            assert_ne!(populated, capture(world.path(), &paths, true).unwrap());
        })
    }

    #[cfg(unix)]
    #[test]
    fn excessive_plain_directory_depth_returns_an_error() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let mut directory = root.join("input");
            fs::create_dir(&directory).unwrap();
            for _ in 0..129 {
                directory.push("d");
                fs::create_dir(&directory).unwrap();
            }
            assert!(capture(&root, &[PathBuf::from("input")], true).is_err());
            assert!(capture_tree(&root.join("input")).is_err());
        })
    }

    #[cfg(unix)]
    #[test]
    fn original_execution_window_rejects_edit_and_restore_even_with_equal_digest() {
        settled(|world| {
            let path = world.path().join("schema");
            fs::write(&path, b"111").unwrap();
            let old = fs::metadata(&path).unwrap().modified().unwrap();
            let paths = vec![PathBuf::from("schema")];
            let before_content = capture(world.path(), &paths, true).unwrap();
            let before = window(world.path(), &paths, true).unwrap();
            fs::write(&path, b"222").unwrap();
            fs::write(&path, b"111").unwrap();
            File::open(&path)
                .unwrap()
                .set_times(FileTimes::new().set_modified(old))
                .unwrap();
            let after = observe(world.path(), &paths, true).unwrap();
            assert_eq!(before_content, after.snapshot);
            assert!(!before.covers(&after));
        })
    }

    #[cfg(unix)]
    #[test]
    fn execution_window_covers_missing_nodes_membership_and_ancestor_swaps() {
        settled(|world| {
            fs::create_dir(world.path().join("schema")).unwrap();
            let paths = vec![PathBuf::from("schema/optional")];
            let before_content = capture(world.path(), &paths, true).unwrap();
            let before = window(world.path(), &paths, true).unwrap();
            fs::write(world.path().join("schema/optional"), b"temporary").unwrap();
            fs::remove_file(world.path().join("schema/optional")).unwrap();
            let after = observe(world.path(), &paths, true).unwrap();
            assert_eq!(before_content, after.snapshot);
            assert!(!before.covers(&after));

            fs::write(world.path().join("schema/value"), b"original").unwrap();
            let paths = vec![PathBuf::from("schema/value")];
            let before_content = capture(world.path(), &paths, false).unwrap();
            let before = window(world.path(), &paths, false).unwrap();
            fs::write(world.path().join("schema/temporary"), b"temporary").unwrap();
            fs::remove_file(world.path().join("schema/temporary")).unwrap();
            let after = observe(world.path(), &paths, false).unwrap();
            assert_eq!(before_content, after.snapshot);
            assert!(!before.covers(&after));

            let before_content = capture(world.path(), &paths, true).unwrap();
            let before = window(world.path(), &paths, true).unwrap();
            fs::rename(world.path().join("schema"), world.path().join("saved")).unwrap();
            fs::create_dir(world.path().join("schema")).unwrap();
            fs::write(world.path().join("schema/value"), b"replacement").unwrap();
            fs::remove_dir_all(world.path().join("schema")).unwrap();
            fs::rename(world.path().join("saved"), world.path().join("schema")).unwrap();
            let after = observe(world.path(), &paths, true).unwrap();
            assert_eq!(before_content, after.snapshot);
            assert!(!before.covers(&after));
        })
    }

    #[cfg(unix)]
    #[test]
    fn input_links_bind_their_spelling_and_target_content() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::create_dir(root.join("actual")).unwrap();
            fs::create_dir(root.join("other")).unwrap();
            fs::write(root.join("actual/value"), b"111").unwrap();
            fs::write(root.join("other/value"), b"111").unwrap();
            std::os::unix::fs::symlink("actual", root.join("input")).unwrap();
            let paths = vec![PathBuf::from("input/value")];
            let first = capture(&root, &paths, true).unwrap();
            assert_eq!(first, capture(&root, &paths, true).unwrap());

            let modified = fs::metadata(root.join("actual/value"))
                .unwrap()
                .modified()
                .unwrap();
            fs::write(root.join("actual/value"), b"222").unwrap();
            File::open(root.join("actual/value"))
                .unwrap()
                .set_times(FileTimes::new().set_modified(modified))
                .unwrap();
            assert_ne!(first, capture(&root, &paths, true).unwrap());
            fs::write(root.join("actual/value"), b"111").unwrap();
            assert_eq!(first, capture(&root, &paths, true).unwrap());
            fs::remove_file(root.join("input")).unwrap();
            std::os::unix::fs::symlink("other", root.join("input")).unwrap();
            // Equal target bytes do not erase the logical link binding.
            assert_ne!(first, capture(&root, &paths, true).unwrap());
        })
    }

    #[cfg(unix)]
    #[test]
    fn relative_absolute_and_parent_components_follow_native_link_order() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::create_dir_all(root.join("actual/inner")).unwrap();
            fs::write(root.join("actual/value"), b"111").unwrap();
            fs::write(root.join("value"), b"222").unwrap();
            std::os::unix::fs::symlink("actual/inner", root.join("first")).unwrap();
            std::os::unix::fs::symlink(root.join("first"), root.join("absolute")).unwrap();
            std::os::unix::fs::symlink("../value", root.join("actual/leaf")).unwrap();
            let paths = vec![PathBuf::from("absolute/../value")];
            let first = capture(&root, &paths, false).unwrap();
            fs::write(root.join("value"), b"333").unwrap();
            assert_eq!(first, capture(&root, &paths, false).unwrap());
            fs::write(root.join("actual/value"), b"444").unwrap();
            assert_ne!(first, capture(&root, &paths, false).unwrap());

            // A direct file link is also observed rather than treated as empty.
            let paths = vec![PathBuf::from("actual/leaf")];
            let first = capture(&root, &paths, false).unwrap();
            fs::write(root.join("value"), b"555").unwrap();
            assert_ne!(first, capture(&root, &paths, false).unwrap());
            assert!(capture(&root, &[PathBuf::from("missing/../value")], false).is_err());
            for path in ["value/", "value/."] {
                assert!(capture(&root, &[PathBuf::from(path)], false).is_err());
            }
            std::os::unix::fs::symlink("value/", root.join("trailing-slash")).unwrap();
            std::os::unix::fs::symlink("value/.", root.join("trailing-dot")).unwrap();
            for path in ["trailing-slash", "trailing-dot"] {
                assert!(capture(&root, &[PathBuf::from(path)], false).is_err());
            }
        })
    }

    #[cfg(unix)]
    #[test]
    fn original_link_and_target_ancestry_cannot_be_retargeted_and_restored() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            fs::create_dir(root.join("actual")).unwrap();
            fs::create_dir(root.join("other")).unwrap();
            fs::write(root.join("actual/value"), b"111").unwrap();
            fs::write(root.join("other/value"), b"999").unwrap();
            std::os::unix::fs::symlink("actual", root.join("input")).unwrap();
            let paths = vec![PathBuf::from("input/value")];
            let first = capture(&root, &paths, false).unwrap();
            let before = window(&root, &paths, false).unwrap();
            fs::rename(root.join("input"), root.join("saved-link")).unwrap();
            std::os::unix::fs::symlink("other", root.join("input")).unwrap();
            assert_eq!(fs::read(root.join("input/value")).unwrap(), b"999");
            fs::remove_file(root.join("input")).unwrap();
            fs::rename(root.join("saved-link"), root.join("input")).unwrap();
            let after = observe(&root, &paths, false).unwrap();
            assert_eq!(first, after.snapshot);
            assert!(!before.covers(&after));

            let before = window(&root, &paths, false).unwrap();
            fs::rename(root.join("actual"), root.join("saved-target")).unwrap();
            fs::create_dir(root.join("actual")).unwrap();
            fs::write(root.join("actual/value"), b"999").unwrap();
            fs::remove_file(root.join("actual/value")).unwrap();
            fs::remove_dir(root.join("actual")).unwrap();
            fs::rename(root.join("saved-target"), root.join("actual")).unwrap();
            let after = observe(&root, &paths, false).unwrap();
            assert_eq!(first, after.snapshot);
            assert!(!before.covers(&after));
        })
    }

    #[cfg(unix)]
    #[test]
    fn dangling_inputs_are_observed_but_cycles_special_nodes_and_output_links_are_refused() {
        settled(|world| {
            let root = world.path().canonicalize().unwrap();
            std::os::unix::fs::symlink("optional", root.join("input")).unwrap();
            let paths = vec![PathBuf::from("input")];
            let missing = capture(&root, &paths, true).unwrap();
            let before = window(&root, &paths, true).unwrap();
            fs::write(root.join("optional"), b"temporary").unwrap();
            fs::remove_file(root.join("optional")).unwrap();
            let after = observe(&root, &paths, true).unwrap();
            assert_eq!(missing, after.snapshot);
            assert!(!before.covers(&after));
            fs::write(root.join("optional"), b"present").unwrap();
            assert_ne!(missing, capture(&root, &paths, true).unwrap());
            std::os::unix::fs::symlink("cycle", root.join("cycle")).unwrap();
            assert!(capture(&root, &[PathBuf::from("cycle")], true).is_err());
            // A recursive directory link also fails the bounded traversal.
            fs::create_dir(root.join("recursive")).unwrap();
            std::os::unix::fs::symlink(".", root.join("recursive/again")).unwrap();
            assert!(capture(&root, &[PathBuf::from("recursive")], true).is_err());
            // Trust: a FIFO opens and reads as empty, so only the refusal of a special node
            // fails it; a socket fails to open in any case, and binds only where its path
            // fits `SUN_LEN`, which a world beside the test binary may not.
            use std::os::unix::ffi::OsStrExt as _;
            let fifo = std::ffi::CString::new(root.join("fifo").as_os_str().as_bytes()).unwrap();
            assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
            std::os::unix::fs::symlink("fifo", root.join("special")).unwrap();
            assert!(capture(&root, &[PathBuf::from("special")], true).is_err());
            if let Ok(_socket) = std::os::unix::net::UnixListener::bind(root.join("socket")) {
                std::os::unix::fs::symlink("socket", root.join("special-socket")).unwrap();
                assert!(capture(&root, &[PathBuf::from("special-socket")], true).is_err());
            }
            fs::create_dir(root.join("output")).unwrap();
            std::os::unix::fs::symlink("../optional", root.join("output/value")).unwrap();
            assert!(capture_tree(&root.join("output")).is_err());
            std::os::unix::fs::symlink("output", root.join("output-link")).unwrap();
            assert!(capture_tree(&root.join("output-link")).is_err());
        })
    }
}
