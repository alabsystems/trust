// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Complete original package namespace inputs, distinct from SDK/Manager custody.
//! No ignored/hidden/cache exclusions, writer freeze, build or proof grant.
//! Admission is supplied separately by the original native Root's budget.

use super::target_sysroot::{Namespace, NamespacePlan, package_budget};
use super::*;

/// Original namespace observation DATA. Relative empty path is the package root.
#[derive(Clone, Debug)]
pub struct PackageEntry {
    pub path: PathBuf,
    pub directory: bool,
    pub mode: u32,
    pub uid: u32,
    pub gid: u32,
    pub bytes: u64,
    pub sha256: Option<String>,
}
impl PackageEntry {
    pub(super) fn from_metadata(path: &Path, metadata: &Metadata, sha256: Option<&str>) -> Self {
        Self {
            path: path.into(),
            directory: metadata.is_dir(),
            mode: metadata.mode(),
            uid: metadata.uid(),
            gid: metadata.gid(),
            bytes: metadata.len(),
            sha256: sha256.map(str::to_owned),
        }
    }
}
struct Parents {
    path: PathBuf,
    selected: PathBuf,
    directories: BTreeMap<PathBuf, HeldDirectory>,
}
impl Parents {
    fn parent(&self) -> &File {
        &self.directories[self.path.parent().unwrap()].file
    }
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        for (path, held) in &self.directories {
            time(deadline)?;
            let current = directory(path, deadline)?;
            if !same_directory(&held.before, &owned(&held.file, true, false)?, false)
                || !same_directory(&held.before, &owned(&current, true, false)?, false)
            {
                return Err(refused("original package ancestor changed"));
            }
        }
        time(deadline)
    }
}
/// Live original-directory planning; no saved inventory can construct this.
pub struct PackageSourcePlan {
    parents: Parents,
    namespace: NamespacePlan,
}
/// Retains every original file, empty directory and selected negative lookup.
/// It covers one finite package tree only, not arbitrary Rust dependency closure.
pub struct HeldPackageSource {
    parents: Parents,
    namespace: Namespace,
    entries: Vec<PackageEntry>,
    content_digest: [u8; 32],
}
impl PackageSourcePlan {
    pub fn capture(path: &Path, deadline: Instant) -> io::Result<Self> {
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        {
            let _ = (path, deadline);
            return Err(io::ErrorKind::Unsupported.into());
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            canonical(path)?;
            if std::fs::canonicalize(path)? != path {
                return Err(refused(
                    "package input requires its exact canonical selected path",
                ));
            }
            let parent = path
                .parent()
                .ok_or_else(|| refused("package root has no parent"))?;
            let selected = PathBuf::from(
                path.file_name()
                    .ok_or_else(|| refused("package root has no name"))?,
            );
            let mut directories = BTreeMap::new();
            // Every ancestor is outside this selected package. Retain identity,
            // modes/ACLs, but do not freeze unrelated sibling timestamps.
            hold_directory(&mut directories, parent, path, deadline)?;
            let parents = Parents {
                path: path.into(),
                selected,
                directories,
            };
            parents.validate(deadline)?;
            let namespace = NamespacePlan::capture_package(
                parents.parent(),
                parent,
                parents.selected.clone(),
                deadline,
                package_budget()?,
            )?;
            let result = Self { parents, namespace };
            result.descriptor_demand(deadline)?;
            Ok(result)
        }
    }
    pub fn descriptor_demand(&self, deadline: Instant) -> io::Result<usize> {
        let deadline = deadline.min(self.namespace.original_deadline());
        self.namespace.checked(|| {
            self.parents.validate(deadline)?;
            self.namespace.validate(self.parents.parent(), deadline)?;
            self.parents.validate(deadline)
        })?;
        Ok(self.namespace.additional_descriptors())
    }
    /// Consume once after external native admission; never raises the limit.
    pub fn materialize(self, deadline: Instant) -> io::Result<HeldPackageSource> {
        let deadline = deadline.min(self.namespace.original_deadline());
        self.descriptor_demand(deadline)?;
        let Self { parents, namespace } = self;
        let namespace = namespace.materialize(parents.parent(), deadline, package_budget()?)?;
        let entries = namespace.package_entries(&parents.selected);
        let content_digest = namespace.package_digest()?;
        let result = HeldPackageSource {
            parents,
            namespace,
            entries,
            content_digest,
        };
        result.validate(deadline)?;
        Ok(result)
    }
}
impl HeldPackageSource {
    /// Identity DATA from the actual retained package-root directory. This is
    /// a negative containment input, never source/SDK or execution authority.
    pub fn original_root_identity(&self, deadline: Instant) -> io::Result<(u64, u64)> {
        self.validate(deadline)?;
        self.namespace
            .original_directory_identity(&self.parents.selected)
    }
    pub fn path(&self) -> &Path {
        &self.parents.path
    }
    /// Complete original-content identity in Targo's existing v1 namespace
    /// scope; unchanged digest bytes gain no proof, cache or writer authority.
    pub fn content_digest(&self) -> &[u8; 32] {
        &self.content_digest
    }
    pub fn entries(&self) -> &[PackageEntry] {
        &self.entries
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.namespace.checked(|| {
            self.parents.validate(deadline)?;
            self.namespace.validate(self.parents.parent(), deadline)?;
            self.parents.validate(deadline)
        })
    }
    /// Original positional bytes only. No path-selected replacement is opened.
    pub fn read(&self, relative: &Path, deadline: Instant) -> io::Result<Vec<u8>> {
        let mut result = None;
        self.namespace.checked(|| {
            self.validate(deadline)?;
            if relative.as_os_str().is_empty()
                || relative
                    .components()
                    .any(|part| !matches!(part, Component::Normal(_)))
            {
                return Err(refused("package read is not a selected canonical file"));
            }
            let bytes = self
                .namespace
                .read_package_file(&self.parents.selected.join(relative), deadline)?;
            self.validate(deadline)?;
            result = Some(bytes);
            Ok(())
        })?;
        Ok(result.unwrap())
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests;
