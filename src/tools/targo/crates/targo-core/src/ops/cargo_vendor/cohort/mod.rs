//! Inspect a resolved path dependency cohort bound to one Git commit.
//! Records describe source and resolution, without execution or proof authority.
//! Package trees and declared assets do not establish a compiler/build-script
//! read closure. Dynamic and external Rust includes require observed inputs.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::path::{Component, Path, PathBuf};

use anyhow::{Context as _, bail, ensure};
use cargo_util::Sha256;
use serde::{Deserialize, Serialize};

use crate::ops;
use crate::resolver::Resolve;
use crate::util::CargoResult;
use crate::util::cache_lock::CacheLockMode;
use crate::workspace::{PackageId, PackageIdSpec, PackageIdSpecQuery, SourceId, Workspace};

const SCHEMA: &str = "targo-vendor-cohort-v1";
const MAX_PACKAGES: usize = 1024;
const MAX_FILES: usize = 100_000;
const MAX_BYTES: u64 = 512 * 1024 * 1024;
const MAX_RECORD_BYTES: u64 = 32 * 1024 * 1024;
const MAX_ROOTS: usize = 64;
const MAX_WORKSPACES: usize = 64;
const MAX_RESOLVED_NODES: usize = 16_384;

#[cfg(test)]
mod tests;

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Record {
    schema: String,
    resolution: String,
    git_commit: String,
    git_tree: String,
    gitlinks: Vec<Gitlink>,
    selection: Vec<String>,
    roots: Vec<Identity>,
    workspaces: Vec<Resolution>,
    files: Vec<SourceFile>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Gitlink {
    path: String,
    commit: String,
    tree: String,
}

struct Located {
    repo: git2::Repository,
    prefix: PathBuf,
    relative: PathBuf,
    tree: git2::Oid,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Resolution {
    manifest: String,
    roots: Vec<Identity>,
    packages: Vec<Package>,
}

struct Frame {
    resolve: Resolve,
    local: BTreeMap<PackageId, crate::workspace::Package>,
    roots: BTreeSet<PackageId>,
    visited: BTreeSet<PackageId>,
    captured: Vec<Package>,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
struct Identity {
    name: String,
    version: String,
    source: String,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Package {
    identity: Identity,
    normalized_manifest: Option<String>,
    dependencies: Vec<Edge>,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
struct Edge {
    name: String,
    kind: String,
    target: Option<String>,
    optional: bool,
    default_features: bool,
    features: Vec<String>,
    declared_source: String,
    resolved: Identity,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct SourceFile {
    path: String,
    mode: i32,
    bytes: u64,
    sha256: String,
}

struct Source<'repo> {
    repo: &'repo git2::Repository,
    root: PathBuf,
    commit: git2::Oid,
    tree: git2::Oid,
    files: BTreeMap<String, SourceFile>,
    bytes: u64,
    watched: BTreeMap<PathBuf, BTreeSet<String>>,
    gitlinks: BTreeMap<PathBuf, Gitlink>,
}

/// Plan the complete resolved graph from explicit roots and inventory every
/// reachable path package. Resolution includes optional, target and dev edges.
pub fn vendor_cohort_plan(ws: &Workspace<'_>, selection: &[String]) -> CargoResult<String> {
    let record = capture(ws, selection)?;
    let encoded = serde_json::to_string_pretty(&record)?;
    ensure!(
        encoded.len() as u64 <= MAX_RECORD_BYTES,
        "source cohort record exceeds 32 MiB"
    );
    Ok(encoded)
}

/// Compare a bounded record with a fresh resolution and actual Git-bound files.
pub fn vendor_cohort_check(ws: &Workspace<'_>, input: &Path) -> CargoResult<String> {
    let mut bytes = Vec::new();
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let file = options.open(input)?;
    ensure!(
        file.metadata()?.is_file(),
        "source cohort record must be a regular file"
    );
    file.take(MAX_RECORD_BYTES + 1).read_to_end(&mut bytes)?;
    ensure!(
        bytes.len() as u64 <= MAX_RECORD_BYTES,
        "source cohort record exceeds 32 MiB"
    );
    let expected: Record =
        serde_json::from_slice(&bytes).context("invalid source cohort record")?;
    ensure!(
        expected.schema == SCHEMA,
        "unsupported source cohort record schema"
    );
    let actual = capture(ws, &expected.selection)?;
    ensure!(
        expected == actual,
        "source cohort does not match the actual resolved source"
    );
    Ok(format!(
        "Source cohort matches {} ({} packages, {} files)",
        actual.git_commit,
        actual
            .workspaces
            .iter()
            .map(|frame| frame.packages.len())
            .sum::<usize>(),
        actual.files.len()
    ))
}

fn capture(ws: &Workspace<'_>, selection: &[String]) -> CargoResult<Record> {
    ensure!(
        ws.gctx().locked_flag().is_some(),
        "source cohort inspection requires --locked"
    );
    ensure!(
        ws.require_optional_deps(),
        "source cohort inspection requires full workspace dependency resolution"
    );
    ensure!(
        ws.gctx()
            .paths_overrides()?
            .is_none_or(|paths| paths.val.is_empty()),
        "source cohort inspection does not support configured paths overrides"
    );
    ensure!(
        !selection.is_empty() && selection.len() <= MAX_ROOTS,
        "source cohort requires 1 to 64 explicit packages"
    );
    let mut selection = selection.to_vec();
    selection.sort();
    selection.dedup();
    let repo =
        git2::Repository::discover(ws.root()).context("source cohort requires a Git worktree")?;
    let mut source = Source::open(&repo)?;
    let _cache = ws
        .gctx()
        .acquire_package_cache_lock(CacheLockMode::DownloadExclusive)?;
    let primary = ws.root_manifest().canonicalize()?;
    let frame = Frame::capture(ws, &mut source)?;
    let mut pending = Vec::new();
    for spec in &selection {
        pending.push((
            primary.clone(),
            PackageIdSpec::query_str(spec, frame.resolve.iter())?,
        ));
    }
    let mut roots = pending
        .iter()
        .map(|(_, id)| source.identity(*id))
        .collect::<CargoResult<Vec<_>>>()?;
    roots.sort();
    roots.dedup();
    for root in &roots {
        ensure!(
            root.source.starts_with("path:"),
            "source cohort roots must be path packages"
        );
    }
    let mut frames = BTreeMap::from([(primary.clone(), frame)]);
    for (_, id) in &pending {
        frames.get_mut(&primary).unwrap().roots.insert(*id);
    }
    let mut visited = 0;
    while let Some((context, id)) = pending.pop() {
        let frame = frames.get_mut(&context).unwrap();
        if !frame.visited.insert(id) {
            continue;
        }
        visited += 1;
        ensure!(
            visited <= MAX_PACKAGES,
            "source cohort exceeds 1024 package contexts"
        );
        let mut edges = Vec::new();
        for (dependency, declarations) in frame.resolve.deps(id) {
            pending.push((context.clone(), dependency));
            for declaration in declarations {
                let mut features = declaration
                    .features()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                features.sort();
                edges.push(Edge {
                    name: declaration.name_in_toml().to_string(),
                    kind: declaration.kind().kind_table().to_owned(),
                    target: declaration.platform().map(ToString::to_string),
                    optional: declaration.is_optional(),
                    default_features: declaration.uses_default_features(),
                    features,
                    declared_source: source.source_id(declaration.source_id())?,
                    resolved: source.identity(dependency)?,
                });
            }
        }
        edges.sort();
        let local = frame.local.get(&id).cloned();
        let normalized_manifest = if let Some(package) = &local {
            source.package(package)?;
            Some(package.manifest().to_normalized_contents()?)
        } else {
            None
        };
        frame.captured.push(Package {
            identity: source.identity(id)?,
            normalized_manifest,
            dependencies: edges,
        });
        if let Some(package) = local {
            let owner = Workspace::new(package.manifest_path(), ws.gctx())?;
            let key = owner.root_manifest().canonicalize()?;
            if !frames.contains_key(&key) {
                ensure!(
                    frames.len() < MAX_WORKSPACES,
                    "source cohort exceeds 64 workspaces"
                );
                frames.insert(key.clone(), Frame::capture(&owner, &mut source)?);
            }
            let original = owner.current()?.package_id();
            frames.get_mut(&key).unwrap().roots.insert(original);
            pending.push((key, original));
        }
    }
    // Every watched repository is the root or one of these distinct pinned
    // gitlink paths. Report phase progress only, never one row per file.
    ws.gctx().shell().status(
        "Checking",
        format_args!(
            "source cohort Git state (repository count {})",
            source.gitlinks.len() + 1
        ),
    )?;
    source.check_current()?;
    let mut workspaces = Vec::new();
    for (manifest, mut frame) in frames {
        frame.captured.sort_by(|a, b| a.identity.cmp(&b.identity));
        let mut roots = frame
            .roots
            .iter()
            .map(|id| source.identity(*id))
            .collect::<CargoResult<Vec<_>>>()?;
        roots.sort();
        workspaces.push(Resolution {
            manifest: portable(&source.relative(&manifest)?)?,
            roots,
            packages: frame.captured,
        });
    }
    Ok(Record {
        schema: SCHEMA.to_owned(),
        resolution: "owning-workspace-all-features-all-targets-with-dev".to_owned(),
        git_commit: source.commit.to_string(),
        git_tree: source.tree.to_string(),
        gitlinks: source.gitlinks.into_values().collect(),
        selection,
        roots,
        workspaces,
        files: source.files.into_values().collect(),
    })
}

impl Frame {
    fn capture(ws: &Workspace<'_>, source: &mut Source<'_>) -> CargoResult<Self> {
        let manifest = portable(&source.relative(ws.root_manifest())?)?;
        // At most two status rows per bounded owning-workspace frame. Shell
        // status is visible in piped logs and already honors --quiet.
        ws.gctx().shell().status(
            "Resolving",
            format_args!("source cohort workspace {manifest}"),
        )?;
        ensure!(
            ws.root_patch()?
                .values()
                .flatten()
                .all(|patch| matches!(patch.loc, crate::workspace::PatchLocation::Manifest(_))),
            "source cohort inspection does not support configured patches"
        );
        source.file(ws.root_manifest())?;
        source.loaded_input(ws.root_manifest(), ws.root_maybe().contents())?;
        let (packages, resolve) = ops::resolve_ws(ws, false)?;
        let (lock, contents) = resolve
            .lockfile_source()
            .context("source cohort requires an original committed lockfile")?;
        source.file(lock)?;
        source.loaded_input(lock, Some(contents))?;
        ensure!(
            resolve.len() <= MAX_RESOLVED_NODES,
            "source cohort workspace exceeds 16384 resolved nodes"
        );
        ws.gctx()
            .shell()
            .status("Inspecting", "source cohort inputs and package files")?;
        let mut local = BTreeMap::new();
        for id in resolve.iter().filter(|id| id.source_id().is_path()) {
            let package = packages.get_one(id)?.clone();
            // Every local summary can constrain resolution, including a member
            // outside the selected dependency closure. Bind its consumed inputs
            // without including that member's unrelated source inventory.
            source.package_inputs(&package)?;
            local.insert(id, package);
        }
        Ok(Self {
            resolve,
            local,
            roots: BTreeSet::new(),
            visited: BTreeSet::new(),
            captured: Vec::new(),
        })
    }
}

impl<'repo> Source<'repo> {
    fn open(repo: &'repo git2::Repository) -> CargoResult<Self> {
        let root = repo
            .workdir()
            .context("source cohort requires a Git worktree")?
            .canonicalize()?;
        let commit = repo.head()?.peel_to_commit()?;
        let (commit, tree) = (commit.id(), commit.tree_id());
        Ok(Self {
            repo,
            root,
            commit,
            tree,
            files: BTreeMap::new(),
            bytes: 0,
            watched: BTreeMap::new(),
            gitlinks: BTreeMap::new(),
        })
    }

    /// Follow only gitlinks from the original committed trees. Each child is
    /// source DATA pinned by its parent, never authority to adopt an artifact.
    fn locate(&mut self, relative: &Path) -> CargoResult<Located> {
        let mut prefix = PathBuf::new();
        let mut relative = relative.to_owned();
        let mut commit = self.commit;
        loop {
            let root = self.root.join(&prefix);
            let repo = git2::Repository::open(&root)?;
            ensure!(
                repo.workdir().map(Path::canonicalize).transpose()?.as_ref() == Some(&root),
                "source cohort repository root changed: {}",
                root.display()
            );
            ensure!(
                repo.head()?.peel_to_commit()?.id() == commit,
                "source cohort repository is not at its pinned commit: {}",
                root.display()
            );
            let tree = repo.find_commit(commit)?.tree()?;
            let mut scanned = PathBuf::new();
            let mut next = None;
            for component in relative.components() {
                scanned.push(component.as_os_str());
                let entry = tree.get_path(&scanned)?;
                if entry.filemode() == 0o160000 {
                    let index = repo.index()?;
                    let pinned = entry.id();
                    ensure!(
                        index
                            .get_path(&scanned, 0)
                            .is_some_and(|entry| entry.id == pinned && entry.mode == 0o160000),
                        "source cohort staged gitlink differs from Git"
                    );
                    next = Some((scanned.clone(), entry.id()));
                    break;
                }
            }
            let tree_id = tree.id();
            drop(tree);
            if let Some((path, pinned)) = next {
                let child = prefix.join(&path);
                relative = relative.strip_prefix(&path)?.to_owned();
                ensure!(
                    self.gitlinks.len() < MAX_WORKSPACES || self.gitlinks.contains_key(&child),
                    "source cohort exceeds 64 gitlink repositories"
                );
                let child_repo = git2::Repository::open(self.root.join(&child))?;
                let child_tree = child_repo.find_commit(pinned)?.tree_id();
                let record = Gitlink {
                    path: portable(&child)?,
                    commit: pinned.to_string(),
                    tree: child_tree.to_string(),
                };
                if let Some(previous) = self.gitlinks.insert(child.clone(), record.clone()) {
                    ensure!(
                        previous == record,
                        "source cohort gitlink changed during inspection"
                    );
                }
                prefix = child;
                commit = pinned;
            } else {
                return Ok(Located {
                    repo,
                    prefix,
                    relative,
                    tree: tree_id,
                });
            }
        }
    }

    fn watch(&mut self, located: &Located) -> CargoResult<()> {
        self.watched
            .entry(located.prefix.clone())
            .or_default()
            .insert(portable(&located.relative)?);
        Ok(())
    }

    fn relative(&self, path: &Path) -> CargoResult<PathBuf> {
        let relative = path.strip_prefix(&self.root).with_context(|| {
            format!(
                "source cohort path is outside its Git worktree: {}",
                path.display()
            )
        })?;
        ensure!(
            relative
                .components()
                .all(|part| matches!(part, Component::Normal(_))),
            "source cohort path is not normalized"
        );
        Ok(relative.to_owned())
    }

    fn source_id(&self, id: SourceId) -> CargoResult<String> {
        if id.is_path() {
            let path = id
                .url()
                .to_file_path()
                .map_err(|_| anyhow::anyhow!("invalid path package source"))?
                .canonicalize()?;
            Ok(format!("path:{}", portable(&self.relative(&path)?)?))
        } else {
            Ok(id.as_url().to_string())
        }
    }

    fn identity(&self, id: PackageId) -> CargoResult<Identity> {
        Ok(Identity {
            name: id.name().to_string(),
            version: id.version().to_string(),
            source: self.source_id(id.source_id())?,
        })
    }

    fn package(&mut self, package: &crate::workspace::Package) -> CargoResult<()> {
        let root = package.root().canonicalize()?;
        let relative = self.relative(&root)?;
        let located = self.locate(&relative)?;
        let repo = git2::Repository::discover(&root)?;
        ensure!(
            repo.workdir().map(Path::canonicalize).transpose()?.as_ref()
                == Some(&self.root.join(&located.prefix)),
            "source cohort crosses an unpinned Git repository boundary"
        );
        self.watch(&located)?;
        let tree = located.repo.find_tree(located.tree)?;
        let tree = if located.relative.as_os_str().is_empty() {
            tree
        } else {
            tree.get_path(&located.relative)?
                .to_object(&located.repo)?
                .peel_to_tree()?
        };
        self.tree(&located.repo, &tree, &relative, 0)?;
        self.package_inputs(package)?;
        for asset in [
            package.manifest().metadata().license_file.as_ref(),
            package.manifest().metadata().readme.as_ref(),
        ]
        .into_iter()
        .flatten()
        {
            self.file(&cargo_util::paths::normalize_path(
                &package.root().join(asset),
            ))?;
        }
        for target in package.targets() {
            let path = target
                .src_path()
                .path()
                .context("source cohort cannot inventory a generated target")?;
            let path = portable(&self.relative(path)?)?;
            ensure!(
                self.files.contains_key(&path),
                "declared source cohort target is absent from Git: {path}"
            );
        }
        Ok(())
    }

    fn package_inputs(&mut self, package: &crate::workspace::Package) -> CargoResult<()> {
        self.file(package.manifest_path())?;
        self.loaded_input(package.manifest_path(), package.manifest().contents())?;
        for (path, contents) in package.manifest().normalization_sources() {
            self.file(path)?;
            self.loaded_input(path, Some(contents))?;
        }
        Ok(())
    }

    fn loaded_input(&self, path: &Path, contents: Option<&str>) -> CargoResult<()> {
        let name = portable(&self.relative(path)?)?;
        let contents = contents.context("source cohort input has no original contents")?;
        let digest = Sha256::new().update(contents.as_bytes()).finish_hex();
        ensure!(
            self.files
                .get(&name)
                .is_some_and(|file| file.sha256 == digest),
            "loaded source cohort input differs from its Git source: {name}"
        );
        Ok(())
    }

    fn tree(
        &mut self,
        repo: &git2::Repository,
        tree: &git2::Tree<'_>,
        prefix: &Path,
        depth: usize,
    ) -> CargoResult<()> {
        ensure!(depth < 128, "source cohort directory nesting exceeds 128");
        for entry in tree.iter() {
            let path = prefix.join(
                entry
                    .name()
                    .context("source cohort requires UTF-8 Git paths")?,
            );
            if entry.kind() == Some(git2::ObjectType::Tree) {
                self.tree(repo, &repo.find_tree(entry.id())?, &path, depth + 1)?;
            } else if entry.filemode() == 0o160000 {
                let located = self.locate(&path)?;
                self.watch(&located)?;
                self.tree(
                    &located.repo,
                    &located.repo.find_tree(located.tree)?,
                    &path,
                    depth + 1,
                )?;
            } else {
                self.entry(repo, &path, entry.id(), entry.filemode())?;
            }
        }
        Ok(())
    }

    fn file(&mut self, path: &Path) -> CargoResult<()> {
        let relative = self.relative(path)?;
        let located = self
            .locate(&relative)
            .with_context(|| format!("source cohort input is not committed: {}", path.display()))?;
        self.watch(&located)?;
        let tree = located.repo.find_tree(located.tree)?;
        let entry = tree
            .get_path(&located.relative)
            .with_context(|| format!("source cohort input is not committed: {}", path.display()))?;
        self.entry(&located.repo, &relative, entry.id(), entry.filemode())
    }

    fn entry(
        &mut self,
        repo: &git2::Repository,
        path: &Path,
        oid: git2::Oid,
        mode: i32,
    ) -> CargoResult<()> {
        let name = portable(path)?;
        if self.files.contains_key(&name) {
            return Ok(());
        }
        ensure!(
            self.files.len() < MAX_FILES,
            "source cohort exceeds 100000 files"
        );
        ensure!(
            matches!(mode, 0o100644 | 0o100755 | 0o120000),
            "unsupported source cohort entry: {name}"
        );
        let (size, kind) = repo.odb()?.read_header(oid)?;
        ensure!(
            kind == git2::ObjectType::Blob,
            "source cohort entry is not a blob: {name}"
        );
        self.bytes = self
            .bytes
            .checked_add(size as u64)
            .context("source cohort byte count overflow")?;
        ensure!(self.bytes <= MAX_BYTES, "source cohort exceeds 512 MiB");
        let blob = repo.find_blob(oid)?;
        let actual = self.root.join(path);
        let metadata = fs::symlink_metadata(&actual)
            .with_context(|| format!("source cohort file is absent: {name}"))?;
        let sha256 = if mode == 0o120000 {
            ensure!(
                metadata.is_symlink(),
                "source cohort symlink changed: {name}"
            );
            let target = fs::read_link(&actual)?;
            ensure!(
                target.as_os_str().as_encoded_bytes() == blob.content(),
                "source cohort symlink differs from Git: {name}"
            );
            Sha256::new().update(blob.content()).finish_hex()
        } else {
            ensure!(
                metadata.is_file(),
                "source cohort file type changed: {name}"
            );
            let mut options = OpenOptions::new();
            options.read(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
                ensure!(
                    (metadata.mode() & 0o111 != 0) == (mode == 0o100755),
                    "source cohort executable mode differs from Git: {name}"
                );
                options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
            }
            let mut file = options.open(&actual)?;
            ensure!(
                file.metadata()?.is_file(),
                "source cohort file type changed: {name}"
            );
            let mut digest = Sha256::new();
            let mut offset = 0_usize;
            let mut buffer = [0; 64 * 1024];
            loop {
                let read = file.read(&mut buffer)?;
                if read == 0 {
                    break;
                }
                let end = offset
                    .checked_add(read)
                    .context("source cohort file size overflow")?;
                ensure!(
                    blob.content().get(offset..end) == Some(&buffer[..read]),
                    "source cohort file differs from Git: {name}"
                );
                digest.update(&buffer[..read]);
                offset = end;
            }
            ensure!(
                offset == blob.size(),
                "source cohort file differs from Git: {name}"
            );
            digest.finish_hex()
        };
        self.files.insert(
            name.clone(),
            SourceFile {
                path: name,
                mode,
                bytes: blob.size() as u64,
                sha256,
            },
        );
        Ok(())
    }

    fn check_current(&self) -> CargoResult<()> {
        ensure!(
            self.repo.head()?.peel_to_commit()?.id() == self.commit,
            "source cohort Git HEAD changed during inspection"
        );
        for (prefix, paths) in &self.watched {
            let root = self.root.join(prefix);
            let repo = git2::Repository::open(&root)?;
            ensure!(
                repo.workdir().map(Path::canonicalize).transpose()?.as_ref() == Some(&root),
                "source cohort pinned repository root changed during inspection"
            );
            let expected = if prefix.as_os_str().is_empty() {
                self.commit
            } else {
                git2::Oid::from_str(&self.gitlinks[prefix].commit)?
            };
            ensure!(
                repo.head()?.peel_to_commit()?.id() == expected,
                "source cohort pinned repository HEAD changed during inspection"
            );
            let mut options = git2::StatusOptions::new();
            options
                .include_untracked(true)
                .recurse_untracked_dirs(true)
                .disable_pathspec_match(true);
            // `.` is our repository-root marker, not a literal Git filename.
            // With literal matching enabled it matches no source descendants.
            // A root package inventories the entire repository, so query all
            // status entries instead of installing a pathspec in that case.
            if !paths.contains(".") {
                for path in paths {
                    options.pathspec(path);
                }
            }
            ensure!(
                repo.statuses(Some(&mut options))?.is_empty(),
                "source cohort contains staged, modified or untracked source inputs"
            );
        }
        for (prefix, link) in &self.gitlinks {
            // An intermediate gitlink need not contain a watched file itself.
            // Its original commit still anchors every deeper source identity.
            let root = self.root.join(prefix);
            let child = git2::Repository::open(&root)?;
            ensure!(
                child
                    .workdir()
                    .map(Path::canonicalize)
                    .transpose()?
                    .as_ref()
                    == Some(&root),
                "source cohort pinned repository root changed during inspection"
            );
            let pinned = git2::Oid::from_str(&link.commit)?;
            ensure!(
                child.head()?.peel_to_commit()?.id() == pinned,
                "source cohort pinned repository HEAD changed during inspection"
            );
            let parent = self
                .gitlinks
                .keys()
                .filter(|path| *path != prefix && prefix.starts_with(path))
                .max_by_key(|path| path.components().count())
                .map(PathBuf::as_path)
                .unwrap_or(Path::new(""));
            let repo = git2::Repository::open(self.root.join(parent))?;
            let index = repo.index()?;
            ensure!(
                index
                    .get_path(prefix.strip_prefix(parent)?, 0)
                    .is_some_and(|entry| entry.id == pinned && entry.mode == 0o160000),
                "source cohort staged gitlink differs from Git"
            );
        }
        Ok(())
    }
}

fn portable(path: &Path) -> CargoResult<String> {
    if path.as_os_str().is_empty() {
        return Ok(".".to_owned());
    }
    path.components()
        .map(|part| match part {
            Component::Normal(value) => {
                value.to_str().context("source cohort requires UTF-8 paths")
            }
            _ => bail!("source cohort path is not normalized"),
        })
        .collect::<CargoResult<Vec<_>>>()
        .map(|parts| parts.join("/"))
}
