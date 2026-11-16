//! Stored-byte Cargo DATA transfer under the original cache locks.
//! Only generated bare Git metadata and sparse crates.io cache DATA are admitted.
//! No source authentication or persistent ownership is transferred.

use super::*;
use std::os::unix::ffi::OsStrExt as _;

mod checkout;
mod selected;
pub(in super::super) use selected::import_selected;

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
struct Routing {
    dl: String,
    api: String,
    #[serde(default)]
    auth_required: bool,
}

const REGISTRY_CONFIG: &[u8] =
    b"{\"dl\":\"https://static.crates.io/crates\",\"api\":\"https://crates.io\"}\n";

#[derive(Default, Debug)]
pub(in super::super) struct Stats {
    pub files: usize,
    pub bytes: u64,
    pub cloned_bytes: u64,
    pub streamed_bytes: u64,
    pub stored_entries: usize,
    pub checkout_entries: usize,
    pub checkout_files: usize,
    pub checkout_bytes: u64,
    pub checkout_cloned_bytes: u64,
    pub checkout_streamed_bytes: u64,
}

#[derive(Clone, Copy)]
enum DataKind {
    Objects,
    SparseIndex,
    Archives,
}

impl DataKind {
    fn accepts(self, relative: &Path) -> bool {
        let Some(text) = relative.to_str() else {
            return false;
        };
        match self {
            Self::Objects => {
                let Some((directory, name)) = text.split_once('/') else {
                    return false;
                };
                let hex = |text: &str| {
                    text.bytes()
                        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                };
                let loose = directory.len() == 2 && hex(directory) && name.len() == 38 && hex(name);
                let pack = name
                    .strip_prefix("pack-")
                    .and_then(|name| name.rsplit_once('.'))
                    .is_some_and(|(oid, suffix)| {
                        oid.len() == 40 && hex(oid) && matches!(suffix, "pack" | "idx" | "rev")
                    });
                loose || (directory == "pack" && pack)
            }
            Self::SparseIndex => {
                let Some(name) = relative.file_name().and_then(OsStr::to_str) else {
                    return false;
                };
                !name.is_empty()
                    && name.bytes().all(|b| {
                        b.is_ascii_lowercase() || b.is_ascii_digit() || matches!(b, b'_' | b'-')
                    })
                    && text == cargo_util::registry::make_dep_path(name, false)
            }
            Self::Archives => {
                relative.components().count() == 1
                    && text.ends_with(".crate")
                    && text.bytes().all(|b| {
                        b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'.' | b'+')
                    })
            }
        }
    }
}

/// This live owner retains the original source descriptions and observations.
/// A failed bookend is sticky, including a later restoration of the old name.
struct Tree {
    source: ObjectSource,
}

impl Tree {
    fn capture(root: Directory) -> CargoResult<Self> {
        let mut source = ObjectSource {
            root,
            directories: BTreeMap::new(),
            files: Vec::new(),
            forbidden: Vec::new(),
            failed: Cell::new(false),
            depth_limit: 4,
        };
        ObjectSource::walk(&source.root, 0, &mut source.directories, &mut source.files)?;
        source.check_current()?;
        Ok(Self { source })
    }

    fn copy(
        &self,
        output: &mut Output,
        prefix: &Path,
        kind: DataKind,
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<()> {
        self.source.check_current()?;
        output.directory(prefix)?;
        for (path, before) in &self.source.files {
            let relative = path.strip_prefix(&self.source.root.path)?;
            ensure!(kind.accepts(relative), "unsupported cache DATA file layout");
            let target = prefix.join(relative);
            let parent = path.parent().context("DATA file parent unavailable")?;
            self.source.with_directory(parent, |directory| {
                let mut input = File::from(rustix::fs::openat(
                    &directory.file,
                    path.file_name().context("DATA file name unavailable")?,
                    OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                    Mode::empty(),
                )?);
                self.source.observe(|| {
                    ensure!(
                        stamp(before, &input.metadata()?),
                        "DATA source changed before copy"
                    );
                    Ok(())
                })?;
                let result = output.copy(&target, &mut input, before.len(), stats, budget);
                let after = self.source.observe(|| {
                    ensure!(
                        stamp(before, &input.metadata()?),
                        "DATA source changed during copy"
                    );
                    Ok(())
                });
                result.and(after)
            })?;
        }
        self.source.check_current()
    }
}

/// Actual retained registry descriptions shared by both DATA profiles.
struct RegistryCopy {
    routing: (File, Metadata, PathBuf),
    parents: Vec<Directory>,
    trees: Vec<Tree>,
}
impl RegistryCopy {
    fn copy(
        cache: &Cache,
        registry: &str,
        output: &mut Output,
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<Self> {
        let root = cache.home.child(OsStr::new("registry"))?;
        let indexes = root.child(OsStr::new("index"))?;
        let index = indexes.child(OsStr::new(registry))?;
        let caches = root.child(OsStr::new("cache"))?;
        let mut config = File::from(rustix::fs::openat(
            &index.file,
            "config.json",
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
            Mode::empty(),
        )?);
        let before = config.metadata()?;
        ensure!(
            before.is_file() && before.len() <= 16 * 1024,
            "unsupported registry routing DATA"
        );
        let mut bytes = Vec::new();
        std::io::Read::by_ref(&mut config)
            .take(16 * 1024 + 1)
            .read_to_end(&mut bytes)?;
        let parsed: Routing = serde_json::from_slice(&bytes)
            .map_err(|_| anyhow::anyhow!("unsupported registry routing DATA schema"))?;
        ensure!(
            parsed.dl == "https://static.crates.io/crates"
                && parsed.api == "https://crates.io"
                && !parsed.auth_required,
            "registry routing does not match configured sparse crates.io"
        );
        ensure!(
            stamp(&before, &config.metadata()?),
            "registry routing DATA changed"
        );
        let prefix = PathBuf::from("registry/index").join(registry);
        output.generated(&prefix.join("config.json"), REGISTRY_CONFIG, stats, budget)?;
        let mut trees = Vec::new();
        for (source, prefix, kind) in [
            (
                index.child(OsStr::new(".cache"))?,
                prefix.join(".cache"),
                DataKind::SparseIndex,
            ),
            (
                caches.child(OsStr::new(registry))?,
                PathBuf::from("registry/cache").join(registry),
                DataKind::Archives,
            ),
        ] {
            let tree = Tree::capture(source)?;
            tree.copy(output, &prefix, kind, stats, budget)?;
            trees.push(tree);
        }
        index.current()?;
        root.current()?;
        let routing = (config, before, index.path.join("config.json"));
        let result = Self {
            routing,
            parents: vec![root, indexes, index, caches],
            trees,
        };
        result.check_current()?;
        Ok(result)
    }
    fn check_current(&self) -> CargoResult<()> {
        for tree in &self.trees {
            tree.source.check_current()?;
        }
        for parent in &self.parents {
            parent.current()?;
        }
        let (file, before, path) = &self.routing;
        ensure!(
            stamp(before, &file.metadata()?) && stamp(before, &std::fs::symlink_metadata(path)?),
            "registry routing DATA changed before publication"
        );
        Ok(())
    }
}

// Stored byte DATA keeps its original namespace cap. Expanded selected
// worktrees use the existing expanded Git-object envelope independently; this
// does not increase raw-provider/stored limits or reset a consumed counter.
const MAX_CHECKOUT_ENTRIES: usize = super::super::MAX_OBJECTS;
#[derive(Default)]
struct EntryBudget {
    stored: usize,
    checkouts: usize,
}
impl EntryBudget {
    fn reserve(&mut self, path: &Path) -> CargoResult<()> {
        let (counter, limit) = if path.starts_with("git/checkouts") {
            (&mut self.checkouts, MAX_CHECKOUT_ENTRIES)
        } else {
            (&mut self.stored, MAX_ENTRIES)
        };
        ensure!(
            *counter < limit,
            "DATA destination {:?} entry bound exceeded",
            if path.starts_with("git/checkouts") {
                "expanded checkout"
            } else {
                "stored"
            }
        );
        *counter += 1;
        Ok(())
    }
}

/// The original private root owns fresh descendants transitively. Factory
/// metadata records identify children; scoped NOFOLLOW opens retain only the
/// bounded ancestry during each operation. Records cannot recreate this owner.
struct Output {
    root: Directory,
    directories: BTreeMap<PathBuf, Metadata>,
    files: Vec<(PathBuf, Metadata)>,
    depth_limit: usize,
    entries: EntryBudget,
}

impl Output {
    fn new(stage: &Stage) -> CargoResult<Self> {
        stage.validate_namespace()?;
        Ok(Self {
            root: Directory {
                path: stage.path().to_owned(),
                file: stage.cache.home.file.try_clone()?,
                before: stage.cache.home.before.clone(),
            },
            directories: BTreeMap::new(),
            files: Vec::new(),
            depth_limit: 12,
            entries: EntryBudget::default(),
        })
    }

    fn with_directory(
        &self,
        path: &Path,
        operation: impl FnOnce(&Directory) -> CargoResult<()>,
    ) -> CargoResult<()> {
        ensure!(
            path.components().count() <= self.depth_limit,
            "DATA directory depth exceeds bound"
        );
        self.descend(&self.root, Path::new(""), &mut path.components(), operation)
    }

    fn descend(
        &self,
        directory: &Directory,
        relative: &Path,
        components: &mut std::path::Components<'_>,
        operation: impl FnOnce(&Directory) -> CargoResult<()>,
    ) -> CargoResult<()> {
        OwnedView::check_directory(directory, false)?;
        let result = match components.next() {
            None => operation(directory),
            Some(std::path::Component::Normal(name)) => {
                let relative = relative.join(name);
                let mut child = directory.child(name)?;
                child.before = self
                    .directories
                    .get(&relative)
                    .cloned()
                    .context("original DATA directory creation unavailable")?;
                self.descend(&child, &relative, components, operation)
            }
            Some(_) => bail!("noncanonical DATA destination component"),
        };
        let after = OwnedView::check_directory(directory, false);
        result.and(after)
    }

    fn directory(&mut self, path: &Path) -> CargoResult<()> {
        let mut relative = PathBuf::new();
        for component in path.components() {
            let std::path::Component::Normal(name) = component else {
                bail!("noncanonical DATA destination component");
            };
            let parent = relative.clone();
            relative.push(name);
            if !self.directories.contains_key(&relative) {
                self.entries.reserve(&relative)?;
                let mut created = None;
                self.with_directory(&parent, |directory| {
                    created = Some(directory.create_child(name)?.before);
                    Ok(())
                })?;
                self.directories.insert(
                    relative.clone(),
                    created.context("DATA directory not created")?,
                );
            }
        }
        self.with_directory(path, |_| Ok(()))
    }

    fn copy(
        &mut self,
        path: &Path,
        input: &mut File,
        len: u64,
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<()> {
        self.copy_mode(path, input, len, None, stats, budget)
    }

    fn copy_mode(
        &mut self,
        path: &Path,
        input: &mut File,
        len: u64,
        mode: Option<u32>,
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<()> {
        self.entries.reserve(path)?;
        let next = stats
            .bytes
            .checked_add(len)
            .context("stored DATA byte overflow")?;
        ensure!(
            next <= super::super::MAX_TOTAL_BYTES,
            "stored DATA exceeds 32 GiB"
        );
        let parent = path.parent().context("DATA output parent unavailable")?;
        self.directory(parent)?;
        let mut created = None;
        self.with_directory(parent, |directory| {
            let name = path.file_name().context("DATA output leaf unavailable")?;
            #[cfg(target_os = "macos")]
            let cloned = {
                let name = std::ffi::CString::new(name.as_bytes())?;
                // SAFETY: original input and live private directory, valid C string.
                (unsafe {
                    libc::fclonefileat(
                        input.as_raw_fd(),
                        directory.file.as_raw_fd(),
                        name.as_ptr(),
                        0,
                    )
                }) == 0
            };
            #[cfg(target_os = "linux")]
            let cloned = false;
            let mut output = File::from(rustix::fs::openat(
                &directory.file,
                name,
                if cloned {
                    OFlags::RDONLY
                } else {
                    OFlags::RDWR | OFlags::CREATE | OFlags::EXCL
                } | OFlags::NOFOLLOW
                    | OFlags::NONBLOCK
                    | OFlags::CLOEXEC,
                Mode::from_bits_truncate(0o600),
            )?);
            #[cfg(target_os = "linux")]
            // SAFETY: original input and fresh exclusive private output.
            let cloned =
                unsafe { libc::ioctl(output.as_raw_fd(), libc::FICLONE, input.as_raw_fd()) } == 0;
            if cloned {
                stats.cloned_bytes += len;
            } else {
                budget.reserve(len)?;
                let copied = std::io::copy(&mut (&mut *input).take(len), &mut output)?;
                let mut extra = [0];
                ensure!(
                    copied == len && input.read(&mut extra)? == 0,
                    "DATA source length changed"
                );
                stats.streamed_bytes += copied;
            }
            ensure!(
                output.metadata()?.is_file() && output.metadata()?.len() == len,
                "DATA output length/type mismatch"
            );
            if let Some(mode) = mode {
                use std::os::unix::fs::PermissionsExt as _;
                output.set_permissions(std::fs::Permissions::from_mode(mode))?;
            }
            output.sync_all()?;
            let metadata = output.metadata()?;
            let named = File::from(rustix::fs::openat(
                &directory.file,
                name,
                OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                Mode::empty(),
            )?);
            ensure!(stamp(&metadata, &named.metadata()?), "DATA output replaced");
            directory.private_current()?;
            created = Some(metadata);
            Ok(())
        })?;
        self.files
            .push((path.to_owned(), created.context("DATA output not created")?));
        stats.bytes = next;
        stats.files += 1;
        Ok(())
    }

    /// Fresh exact link DATA, never an opened target or a source owner.
    fn link(
        &mut self,
        path: &Path,
        target: &[u8],
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<()> {
        self.entries.reserve(path)?;
        let next = stats
            .bytes
            .checked_add(target.len() as u64)
            .context("link DATA byte overflow")?;
        ensure!(
            next <= super::super::MAX_TOTAL_BYTES,
            "link DATA exceeds32GiB"
        );
        budget.reserve(target.len() as u64)?;
        let parent = path.parent().context("link DATA parent unavailable")?;
        self.directory(parent)?;
        let mut created = None;
        self.with_directory(parent, |directory| {
            let name = path.file_name().context("link DATA leaf unavailable")?;
            rustix::fs::symlinkat(OsStr::from_bytes(target), &directory.file, name)?;
            let before = std::fs::symlink_metadata(directory.path.join(name))?;
            ensure!(
                before.file_type().is_symlink(),
                "fresh link DATA type differs"
            );
            let mut bytes = [0_u8; 4097];
            let len = rustix::fs::readlinkat_raw(&directory.file, name, &mut bytes[..])?;
            ensure!(
                len <= 4096
                    && &bytes[..len] == target
                    && stamp(
                        &before,
                        &std::fs::symlink_metadata(directory.path.join(name))?
                    ),
                "fresh link DATA changed"
            );
            directory.private_current()?;
            created = Some(before);
            Ok(())
        })?;
        self.files
            .push((path.to_owned(), created.context("link DATA not created")?));
        stats.bytes = next;
        stats.streamed_bytes += target.len() as u64;
        stats.files += 1;
        Ok(())
    }

    fn generated(
        &mut self,
        path: &Path,
        bytes: &[u8],
        stats: &mut Stats,
        budget: &mut CopyBudget,
    ) -> CargoResult<()> {
        // A private anonymous file supplies generated metadata to the SAME
        // bounded copy path. It never reads donor configuration.
        let mut input = tempfile::tempfile()?;
        input.write_all(bytes)?;
        input.rewind()?;
        self.copy(path, &mut input, bytes.len() as u64, stats, budget)
    }

    fn check_current(&self) -> CargoResult<()> {
        self.with_directory(Path::new(""), |directory| {
            directory.file.sync_all()?;
            Ok(())
        })?;
        for path in self.directories.keys() {
            self.with_directory(path, |directory| {
                directory.file.sync_all()?;
                Ok(())
            })?;
        }
        for (path, before) in &self.files {
            self.with_directory(
                path.parent().context("DATA parent unavailable")?,
                |directory| {
                    if before.file_type().is_symlink() {
                        ensure!(
                            stamp(
                                before,
                                &std::fs::symlink_metadata(directory.path.join(
                                    path.file_name().context("link DATA leaf unavailable")?
                                ))?
                            ),
                            "private link DATA changed"
                        );
                        return Ok(());
                    }
                    let file = File::from(rustix::fs::openat(
                        &directory.file,
                        path.file_name().context("DATA leaf unavailable")?,
                        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                        Mode::empty(),
                    )?);
                    ensure!(
                        stamp(before, &file.metadata()?),
                        "private DATA output changed"
                    );
                    Ok(())
                },
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
