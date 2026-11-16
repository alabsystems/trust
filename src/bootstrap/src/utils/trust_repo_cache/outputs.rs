//! Trust: generated artifacts and declared sysroot source aliases are distinct namespaces.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::path::{Component, Path, PathBuf};

use sha2::{Digest, Sha256};

use super::{NamespaceRouteLink, add, finish, namespace_route_links, same_snapshot};

/// An actual Git source observation, retained through artifact finalization.
/// Its digest cannot be supplied by a caller in place of observing the repository.
#[derive(Debug)]
pub(crate) struct RepositorySnapshot {
    directory: DirectoryObservation,
    route: Vec<NamespaceRouteLink>,
    digest: String,
}

impl RepositorySnapshot {
    pub(crate) fn observe(root: &Path, jobs: usize) -> Result<Self, String> {
        let route = namespace_route_links([root], 1024)?;
        let directory =
            DirectoryObservation::open(&fs::canonicalize(root).map_err(io_error(root))?)?;
        let digest = super::repository_digest(&directory.path, jobs)?;
        let observed = Self { directory, route, digest };
        observed.check()?;
        Ok(observed)
    }

    pub(crate) fn digest(&self) -> &str {
        &self.digest
    }

    fn check(&self) -> Result<(), String> {
        self.directory.check()?;
        check_route(&self.route)
    }
}

/// The full input key and the source observation actually folded into it.
#[derive(Debug)]
pub(crate) struct InputSnapshot {
    pub(super) digest: String,
    repository: Option<RepositorySnapshot>,
}

impl InputSnapshot {
    // Trust: a producer may record this observation, never manufacture its authority.
    pub(crate) fn digest(&self) -> &str {
        &self.digest
    }

    pub(crate) fn new(digest: String, repository: RepositorySnapshot) -> Self {
        Self { digest, repository: Some(repository) }
    }
}

impl PartialEq for InputSnapshot {
    fn eq(&self, other: &Self) -> bool {
        self.digest == other.digest
    }
}

impl Eq for InputSnapshot {}

#[cfg(test)]
impl From<String> for InputSnapshot {
    fn from(digest: String) -> Self {
        Self { digest, repository: None }
    }
}

#[cfg(test)]
impl From<&str> for InputSnapshot {
    fn from(digest: &str) -> Self {
        Self::from(digest.to_owned())
    }
}

/// Production declares the generated host tree, repository and owning sysroot aliases.
/// A raw tree is available only to controlled cache fixtures, never repo mode.
#[derive(Clone, Copy)]
pub(crate) enum OutputNamespace<'a> {
    GeneratedHost {
        root: &'a Path,
        repository: &'a Path,
        source_aliases: &'a [PathBuf],
    },
    // Trust: WP's maintained private wrapper writes here even with CARGO_TARGET_DIR set.
    TrustWp {
        repository: &'a Path,
    },
    #[cfg(test)]
    Fixture(&'a Path),
}

#[cfg(test)]
impl<'a> From<&'a PathBuf> for OutputNamespace<'a> {
    fn from(root: &'a PathBuf) -> Self {
        Self::Fixture(root)
    }
}

impl OutputNamespace<'_> {
    #[cfg(test)]
    pub(super) fn digest(&self, inputs: &InputSnapshot, controls: &Path) -> Result<String, String> {
        self.observe(inputs, controls)?.digest()
    }

    #[cfg(test)]
    fn digest_with_hook(
        &self,
        inputs: &InputSnapshot,
        controls: &Path,
        after_open: impl FnOnce(),
    ) -> Result<String, String> {
        self.observe(inputs, controls)?.digest_with_hook(after_open)
    }

    pub(super) fn observe<'a>(
        &self,
        inputs: &'a InputSnapshot,
        controls: &Path,
    ) -> Result<OutputObservation<'a>, String> {
        match self {
            Self::TrustWp { repository } => {
                let source = inputs
                    .repository
                    .as_ref()
                    .ok_or("WP artifacts require an observed repository input snapshot")?;
                source.check()?;
                if fs::canonicalize(repository).map_err(io_error(repository))?
                    != source.directory.path
                {
                    return Err("WP artifacts name a different source repository".into());
                }
                let path = source.directory.path.join("first-party/trust-wp/target");
                let root_route = namespace_route_links([path.as_path()], 1024)?;
                let root = DirectoryObservation::open(&path)?;
                let controls = fs::canonicalize(controls).map_err(io_error(controls))?;
                if fs::canonicalize(&path).map_err(io_error(&path))? != path
                    || controls.starts_with(&path)
                    || path.starts_with(&controls)
                {
                    return Err("WP target must be its own generated directory, disjoint from execution controls".into());
                }
                Ok(OutputObservation::Generated(GeneratedObservation {
                    root,
                    root_route,
                    controls,
                    aliases: Vec::new(),
                    source,
                }))
            }
            Self::GeneratedHost { root, repository, source_aliases } => {
                let source = inputs.repository.as_ref().ok_or(
                    "generated host artifacts require an observed repository input snapshot",
                )?;
                source.check()?;
                if fs::canonicalize(repository).map_err(io_error(repository))?
                    != source.directory.path
                {
                    return Err("generated artifacts name a different source repository".into());
                }
                let mut declared = BTreeSet::new();
                for alias in *source_aliases {
                    let relative = alias.strip_prefix(root).map_err(|_| {
                        format!(
                            "source alias is outside generated host artifacts: {}",
                            alias.display()
                        )
                    })?;
                    if relative.as_os_str().is_empty()
                        || relative.components().any(|part| !matches!(part, Component::Normal(_)))
                        || !declared.insert(relative.to_owned())
                    {
                        return Err(
                            "source aliases must be distinct normalized artifact leaves".into()
                        );
                    }
                }
                if declared.is_empty() {
                    return Err(
                        "generated host artifacts require declared sysroot source aliases".into()
                    );
                }
                let root_route = namespace_route_links([*root], 1024)?;
                let root =
                    DirectoryObservation::open(&fs::canonicalize(root).map_err(io_error(root))?)?;
                let controls = fs::canonicalize(controls).map_err(io_error(controls))?;
                if root.path == source.directory.path
                    || !root.path.starts_with(&source.directory.path)
                    || controls.starts_with(&root.path)
                    || root.path.starts_with(&controls)
                {
                    return Err(
                        "generated artifacts must be disjoint from source and execution controls"
                            .into(),
                    );
                }
                // Validate the declaration before any traversal. A replaced
                // parent must not redirect the special leaf into another tree.
                let aliases = declared
                    .iter()
                    .map(|relative| SourceAlias::open(&root.path, relative, source))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(OutputObservation::Generated(GeneratedObservation {
                    root,
                    root_route,
                    controls,
                    aliases,
                    source,
                }))
            }
            #[cfg(test)]
            Self::Fixture(root) => Ok(OutputObservation::Fixture(root.to_path_buf())),
        }
    }
}

/// Retain the same directory descriptors and alias identities across BOTH
/// artifact hashes and the intervening full input observation/publication.
pub(super) enum OutputObservation<'a> {
    Generated(GeneratedObservation<'a>),
    #[cfg(test)]
    Fixture(PathBuf),
}

impl OutputObservation<'_> {
    pub(super) fn digest(&self) -> Result<String, String> {
        self.digest_with_hook(|| {})
    }

    fn digest_with_hook(&self, after_open: impl FnOnce()) -> Result<String, String> {
        match self {
            Self::Generated(observed) => {
                let context = GeneratedContext {
                    aliases: &observed.aliases,
                    source: observed.source,
                    controls: &observed.controls,
                    visited: RefCell::new(BTreeSet::new()),
                };
                after_open();
                self.check_namespace()?;
                let mut hash = Sha256::new();
                add(&mut hash, b"trust.generated-host-artifacts/v2");
                super::hash_path(
                    &mut hash,
                    &observed.root.path,
                    &mut Default::default(),
                    super::TreeInputs::Generated(&context),
                )?;
                if context.visited.borrow().len() != observed.aliases.len() {
                    return Err("a declared sysroot source alias was not inventoried".into());
                }
                self.check_namespace()?;
                Ok(finish(hash))
            }
            #[cfg(test)]
            Self::Fixture(root) => {
                after_open();
                super::tree_digest(root)
            }
        }
    }

    pub(super) fn check_namespace(&self) -> Result<(), String> {
        match self {
            Self::Generated(observed) => {
                for alias in &observed.aliases {
                    alias.check()?;
                }
                observed.root.check()?;
                check_route(&observed.root_route)
            }
            #[cfg(test)]
            Self::Fixture(_) => Ok(()),
        }
    }
}

pub(super) struct GeneratedObservation<'a> {
    root: DirectoryObservation,
    root_route: Vec<NamespaceRouteLink>,
    controls: PathBuf,
    aliases: Vec<SourceAlias<'a>>,
    source: &'a RepositorySnapshot,
}

pub(super) struct GeneratedContext<'a> {
    aliases: &'a [SourceAlias<'a>],
    source: &'a RepositorySnapshot,
    controls: &'a Path,
    visited: RefCell<BTreeSet<PathBuf>>,
}

impl GeneratedContext<'_> {
    pub(super) fn leaf(&self, path: &Path) -> Result<Option<String>, String> {
        if path.starts_with(self.controls) {
            return Err(format!(
                "execution controls are not generated host artifacts: {}",
                path.display()
            ));
        }
        if let Some(alias) = self.aliases.iter().find(|alias| path == alias.path) {
            let digest = alias.digest()?;
            self.visited.borrow_mut().insert(path.to_owned());
            return Ok(Some(digest));
        }
        if path == self.source.directory.path {
            return Err(format!(
                "undeclared source-root route is not generated host artifacts: {}",
                path.display()
            ));
        }
        Ok(None)
    }
}

struct SourceAlias<'a> {
    path: PathBuf,
    metadata: fs::Metadata,
    target: PathBuf,
    parents: Vec<DirectoryObservation>,
    route: Vec<NamespaceRouteLink>,
    source: &'a RepositorySnapshot,
}

impl<'a> SourceAlias<'a> {
    fn open(root: &Path, relative: &Path, source: &'a RepositorySnapshot) -> Result<Self, String> {
        let path = root.join(relative);
        let mut parents = Vec::new();
        let mut parent = root.to_owned();
        for component in relative.parent().unwrap().components() {
            parent.push(component);
            parents.push(DirectoryObservation::open(&parent)?);
        }
        let metadata = fs::symlink_metadata(&path).map_err(io_error(&path))?;
        if !metadata.file_type().is_symlink() {
            return Err(format!("expected a declared sysroot source alias: {}", path.display()));
        }
        let target = fs::read_link(&path).map_err(io_error(&path))?;
        let route = namespace_route_links([path.as_path()], 1024)?;
        let observed = Self { path, metadata, target, parents, route, source };
        observed.check()?;
        Ok(observed)
    }

    fn check(&self) -> Result<(), String> {
        self.source.check()?;
        for directory in &self.parents {
            directory.check()?;
        }
        if !same_snapshot(
            &self.metadata,
            &fs::symlink_metadata(&self.path).map_err(io_error(&self.path))?,
        ) || fs::read_link(&self.path).map_err(io_error(&self.path))? != self.target
            || fs::canonicalize(&self.path).map_err(io_error(&self.path))?
                != self.source.directory.path
        {
            return Err(format!(
                "declared sysroot source alias moved or has the wrong target: {}",
                self.path.display()
            ));
        }
        check_route(&self.route)
    }

    fn digest(&self) -> Result<String, String> {
        self.check()?;
        let mut hash = Sha256::new();
        add(&mut hash, b"trust.stage1-rust-source-alias/v1");
        add(&mut hash, self.path.as_os_str().as_encoded_bytes());
        add(&mut hash, self.target.as_os_str().as_encoded_bytes());
        add(&mut hash, self.source.directory.path.as_os_str().as_encoded_bytes());
        add(&mut hash, self.source.digest());
        add_permissions(&mut hash, &self.metadata);
        add_permissions(&mut hash, &self.source.directory.metadata);
        for link in &self.route {
            add(&mut hash, link.path.as_os_str().as_encoded_bytes());
            add(&mut hash, link.target.as_os_str().as_encoded_bytes());
            add_permissions(&mut hash, &link.metadata);
        }
        self.check()?;
        Ok(finish(hash))
    }
}

#[derive(Debug)]
struct DirectoryObservation {
    path: PathBuf,
    metadata: fs::Metadata,
    descriptor: File,
}

impl DirectoryObservation {
    fn open(path: &Path) -> Result<Self, String> {
        let metadata = fs::symlink_metadata(path).map_err(io_error(path))?;
        if !metadata.is_dir() || metadata.file_type().is_symlink() {
            return Err(format!(
                "expected an exact artifact/source namespace directory: {}",
                path.display()
            ));
        }
        let mut options = OpenOptions::new();
        options.read(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK);
        }
        let descriptor = options.open(path).map_err(io_error(path))?;
        let observed = Self { path: path.to_owned(), metadata, descriptor };
        observed.check()?;
        Ok(observed)
    }

    fn check(&self) -> Result<(), String> {
        if !same_snapshot(
            &self.metadata,
            &self.descriptor.metadata().map_err(io_error(&self.path))?,
        ) || !same_snapshot(
            &self.metadata,
            &fs::symlink_metadata(&self.path).map_err(io_error(&self.path))?,
        ) || fs::canonicalize(&self.path).map_err(io_error(&self.path))? != self.path
        {
            return Err(format!(
                "artifact/source namespace directory moved: {}",
                self.path.display()
            ));
        }
        Ok(())
    }
}

fn check_route(route: &[NamespaceRouteLink]) -> Result<(), String> {
    for link in route {
        if !same_snapshot(
            &link.metadata,
            &fs::symlink_metadata(&link.path).map_err(io_error(&link.path))?,
        ) || fs::read_link(&link.path).map_err(io_error(&link.path))? != link.target
            || !same_snapshot(
                &link.metadata,
                &fs::symlink_metadata(&link.path).map_err(io_error(&link.path))?,
            )
        {
            return Err(format!("artifact/source namespace route moved: {}", link.path.display()));
        }
    }
    Ok(())
}

fn add_permissions(hash: &mut Sha256, metadata: &fs::Metadata) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        add(hash, metadata.permissions().mode().to_le_bytes());
    }
    #[cfg(not(unix))]
    add(hash, [u8::from(metadata.permissions().readonly())]);
}

fn io_error(path: &Path) -> impl FnOnce(std::io::Error) -> String + '_ {
    move |error| format!("{}: {error}", path.display())
}

#[cfg(test)]
mod tests;
