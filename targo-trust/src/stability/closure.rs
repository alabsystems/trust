//! What a copy of the caller's workspace carries (DECISION_QUEUE T4.7-16,
//! T4.7-17, STABILITY-COPY-1): the workspace's PATH CLOSURE, every package
//! directory its resolve reads by path, each at its position below the nearest
//! directory that holds them all, so that a copy is a second checkout of the
//! same tree at another absolute path.
//!
//! The closure is read from the manifests, the way Cargo reads them before it
//! resolves anything: the workspace root's members (`members` globs, less
//! `exclude`) and `default-members`, its `[patch]` and `[replace]` tables, and
//! each package's dependency tables, each also under `[target.<cfg>]`, a
//! `workspace = true` dependency through the `[workspace.dependencies]` of the
//! workspace root Cargo's search finds for that package (the package's own
//! manifest when it declares `[workspace]`), transitively. A WORKSPACE MEMBER
//! (the root package, a `members` entry, and a path dependency of a member
//! that Cargo makes a member: inside the root's directory, or naming the root
//! as its own, and not excluded; `Workspace::find_path_deps`) is followed
//! through `[dependencies]`, `[build-dependencies]` and `[dev-dependencies]`;
//! any other package through the first two alone, since the resolver never
//! reads a non-member's dev-dependencies. That is the set Cargo's lockfile
//! resolve reads, which takes every feature and platform and loads every
//! `[patch]` entry used or not; `targo metadata` lists only the packages of the
//! resolve its feature flags select and leaves an unused patch out (measured
//! 2026-10-14 on `crates/`: 73 path packages outside the root, and
//! `trust-ir-conformance`, an unused patch the resolver still reads, absent).
//! Beside the package directories a copy carries the files Cargo reads on the
//! way to them: the workspace-root manifest each package inherits from, every
//! `Cargo.toml` above a package directory up to the closure's root (Cargo's
//! workspace-root search reads them), and, in each directory from that root
//! down to the workspace, its `.cargo/config.toml` and `.cargo/config` (but
//! `$CARGO_HOME`'s, which Cargo reads wherever it runs) and its
//! `rust-toolchain.toml` or `rust-toolchain`.
//!
//! What a copy carries is the original's bytes at the original's relative
//! positions, and what it does not carry is missing, never different. A HARD
//! read of something missing (a file outside every package directory that an
//! `include_str!`, a `[lib] path` or a configuration's own `[patch]` names)
//! fails in the copy, so that leg could not run and says so. A read that
//! TOLERATES a missing file does not fail: a build script that tests whether a
//! path exists, or reads git state (every copy leaves `.git` out), runs on in
//! the copy with other inputs than in the original, so a leg in a copy can
//! differ from the base leg for that alone (crates/'s `trust-thir-lower` and
//! `trust-vc-core` build scripts are two). An absolute symlink inside a carried
//! directory that points into the closure's root would read the original from
//! every copy: the copy refuses it, naming it (that leg could not run).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};

use crate::project_root::lexically_normalized;

/// The dependency tables Cargo resolves for every package, in both of its
/// spellings.
const DEPENDENCY_TABLES: [&str; 3] = ["dependencies", "build-dependencies", "build_dependencies"];

/// The dependency tables Cargo resolves for a workspace member alone.
const DEV_DEPENDENCY_TABLES: [&str; 2] = ["dev-dependencies", "dev_dependencies"];

/// What a copy of the workspace carries, relative to [`PathClosure::root`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PathClosure {
    /// The directory a copy is made of: the nearest common ancestor of the
    /// workspace root and of every package directory and file it carries.
    pub(crate) root: PathBuf,
    /// The workspace root, relative to `root` (empty when it is `root`).
    pub(crate) workspace: PathBuf,
    /// The package directories copied whole, relative to `root`, none inside
    /// another: the workspace root's (or one holding it) and each one outside
    /// it.
    pub(crate) trees: Vec<PathBuf>,
    /// The single files copied besides, relative to `root`: manifests and
    /// Cargo configuration Cargo reads on the way to the trees.
    pub(crate) files: Vec<PathBuf>,
    /// Every package the closure read, sorted by manifest.
    pub(crate) packages: Vec<ClosurePackage>,
    /// What placed `root` above the workspace: each read outside the
    /// workspace that no nearer directory holds together with it, as
    /// "`<path>` (<what reads it>)". Empty when `root` is the workspace.
    pub(crate) reached_through: Vec<String>,
}

/// A package of the closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClosurePackage {
    /// Its `[package] name`.
    pub(crate) name: String,
    /// Its manifest, relative to [`PathClosure::root`].
    pub(crate) manifest: PathBuf,
    /// Whether it is a member of the workspace (whose dev-dependencies Cargo
    /// resolves).
    pub(crate) member: bool,
}

impl PathClosure {
    /// Whether the workspace reads nothing by path outside its own root.
    pub(crate) fn is_self_contained(&self) -> bool {
        self.workspace.as_os_str().is_empty() && self.trees.len() == 1 && self.files.is_empty()
    }
}

/// The path closure of the workspace whose root is `workspace_root` (a
/// directory named through the file system's own names). Refused, naming the
/// dependency: a path dependency written as an absolute path (every copy would
/// read the one directory, so no axis could move it), a closure that reaches
/// the file system's root (a copy would be of everything), and a manifest of
/// the closure that cannot be read, or whose workspace root cannot be found.
pub(crate) fn path_closure(workspace_root: &Path) -> Result<PathClosure, String> {
    let root_manifest = crate::config::discover_manifest(workspace_root).ok_or_else(|| {
        format!("the workspace root `{}` has no manifest", workspace_root.display())
    })?;
    let mut walk = Walk::default();
    walk.trees.insert(workspace_root.to_path_buf());
    walk.workspace_root(&root_manifest)?;
    while let Some((manifest, member)) = walk.pending.pop() {
        walk.package(&manifest, member)?;
    }
    let mut trees: Vec<PathBuf> = Vec::new();
    for tree in &walk.trees {
        // `walk.trees` is sorted, so a directory comes before those inside it.
        if !trees.iter().any(|kept| tree.starts_with(kept)) {
            trees.push(tree.clone());
        }
    }
    // Each read that places the root, with the directory it anchors.
    let mut anchors: Vec<(&Path, &Path)> =
        trees.iter().map(|tree| (tree.as_path(), tree.as_path())).collect();
    anchors.extend(walk.files.iter().filter_map(|file| Some((file.parent()?, file.as_path()))));
    let root = anchors
        .iter()
        .fold(workspace_root.to_path_buf(), |common, (dir, _)| common_ancestor(&common, dir));
    let reached_through: Vec<String> = anchors
        .iter()
        .filter(|(dir, _)| !dir.starts_with(workspace_root))
        .filter(|(dir, _)| common_ancestor(workspace_root, dir) == root)
        .map(|(_, read)| {
            let why = walk.reasons.get(*read).map_or("read by path", String::as_str);
            format!("`{}` ({why})", read.display())
        })
        .collect();
    if root.parent().is_none() {
        return Err(format!(
            "the workspace `{}` reads by path as far up as `{}`, the file system's root, through \
             {}: a copy of it would be a copy of everything; place what it reads below a nearer \
             common directory",
            workspace_root.display(),
            root.display(),
            reached_through.join(", ")
        ));
    }
    // On the way from the root down: every manifest above a tree (Cargo's
    // workspace-root search reads them), and the Cargo configuration and
    // toolchain file of each directory above the workspace (Cargo and rustup
    // read them for a command run there), but `$CARGO_HOME`'s configuration,
    // which Cargo reads wherever it runs, so a copy must not carry it too.
    let mut files = walk.files.clone();
    let below_root = |dir: &&Path| dir.starts_with(&root);
    for tree in &trees {
        for dir in tree.ancestors().skip(1).take_while(below_root) {
            files.extend(crate::config::MANIFEST_NAMES.map(|name| dir.join(name)));
        }
    }
    let cargo_home = crate::config::cargo_home().map(|home| home.canonicalize().unwrap_or(home));
    for dir in workspace_root.ancestors().skip(1).take_while(below_root) {
        let cargo_dir = dir.join(".cargo");
        if cargo_home.as_ref() != Some(&cargo_dir) {
            files.extend(["config.toml", "config"].map(|name| cargo_dir.join(name)));
        }
        files.extend(["rust-toolchain.toml", "rust-toolchain"].map(|name| dir.join(name)));
    }
    let relative = |path: &Path| path.strip_prefix(&root).unwrap_or(path).to_path_buf();
    let files = files
        .into_iter()
        .filter(|file| file.is_file() && !trees.iter().any(|tree| file.starts_with(tree)))
        .map(|file| relative(&file))
        .collect();
    let packages = walk
        .packages
        .iter()
        .map(|(manifest, name)| ClosurePackage {
            name: name.clone(),
            manifest: relative(manifest),
            member: walk.members.contains(manifest),
        })
        .collect();
    Ok(PathClosure {
        workspace: relative(workspace_root),
        trees: trees.iter().map(|tree| relative(tree)).collect(),
        files,
        packages,
        reached_through,
        root,
    })
}

/// The longest path both `a` and `b` start with, component by component.
fn common_ancestor(a: &Path, b: &Path) -> PathBuf {
    a.components().zip(b.components()).take_while(|(x, y)| x == y).map(|(x, _)| x).collect()
}

/// The workspace root's `[workspace]` rules that decide which path
/// dependencies of a member are members too.
struct Membership {
    /// The root manifest, normalized.
    manifest: PathBuf,
    /// Its directory.
    dir: PathBuf,
    members: Vec<String>,
    exclude: Vec<String>,
}

impl Membership {
    /// Cargo's `is_excluded`: under an `exclude` path and under no `members`
    /// entry, as written.
    fn excluded(&self, manifest: &Path) -> bool {
        self.exclude.iter().any(|ex| manifest.starts_with(self.dir.join(ex)))
            && !self.members.iter().any(|member| manifest.starts_with(self.dir.join(member)))
    }

    /// Whether a path dependency of a member at `dir` is a member: Cargo's
    /// `find_path_deps`, which takes one inside the root's directory, or one
    /// whose own workspace-root search names this root, unless it is excluded.
    fn takes(&self, dir: &Path) -> bool {
        if self.excluded(&dir.join("Cargo.toml")) {
            return false;
        }
        dir.starts_with(&self.dir)
            || crate::config::policy_manifest(dir)
                .ok()
                .flatten()
                .is_some_and(|root| lexically_normalized(&root) == self.manifest)
    }
}

/// The manifests read so far and what they name.
#[derive(Default)]
struct Walk {
    /// Parsed manifests, by their normalized path.
    read: BTreeMap<PathBuf, toml::Table>,
    /// Package manifests whose dependencies are still to follow, each with
    /// whether it is a workspace member.
    pending: Vec<(PathBuf, bool)>,
    /// Every package manifest ever queued.
    queued: BTreeSet<PathBuf>,
    /// Those queued as workspace members.
    members: BTreeSet<PathBuf>,
    /// The workspace's membership rules, when its root declares `[workspace]`
    /// (a package in no workspace is its only member).
    membership: Option<Membership>,
    /// Package directories (and the workspace root).
    trees: BTreeSet<PathBuf>,
    /// Workspace-root manifests a package inherits from.
    files: BTreeSet<PathBuf>,
    /// Each package's name, by its manifest.
    packages: BTreeMap<PathBuf, String>,
    /// What first read each package directory and inherited root manifest.
    reasons: BTreeMap<PathBuf, String>,
}

impl Walk {
    fn table(&mut self, manifest: &Path) -> Result<&toml::Table, String> {
        if !self.read.contains_key(manifest) {
            let text = std::fs::read_to_string(manifest).map_err(|error| {
                format!(
                    "cannot read `{}`, a manifest the workspace reads by path: {error}",
                    manifest.display()
                )
            })?;
            let table = text.parse::<toml::Table>().map_err(|error| {
                format!(
                    "`{}`, a manifest the workspace reads by path, does not parse: {error}",
                    manifest.display()
                )
            })?;
            self.read.insert(manifest.to_path_buf(), table);
        }
        Ok(&self.read[manifest])
    }

    /// Queue the package whose directory a path names, if there is one (a
    /// path that names nothing is read by Cargo only to fail, in the original
    /// as in a copy), and record `why` it is read. A package first queued as a
    /// non-member and later reached as a member is followed again, as one.
    fn queue(&mut self, dir: &Path, member: bool, why: impl FnOnce() -> String) {
        let Some(manifest) = crate::config::discover_manifest(dir) else {
            return;
        };
        let manifest = lexically_normalized(&manifest);
        let first = self.queued.insert(manifest.clone());
        let promoted = member && self.members.insert(manifest.clone());
        if first || promoted {
            self.reasons.entry(lexically_normalized(dir)).or_insert_with(why);
            self.pending.push((manifest, member));
        }
    }

    /// A dependency `name` of the package whose manifest is `manifest`, at
    /// `path`, written in `declared_in` relative to `base`; `member` is the
    /// package's membership.
    fn dependency(
        &mut self,
        member: bool,
        declared_in: &Path,
        name: &str,
        base: &Path,
        path: &str,
    ) -> Result<(), String> {
        if Path::new(path).is_absolute() {
            return Err(format!(
                "`{}`: the path dependency `{name}` names the absolute path `{path}`, which every \
                 copy would read in place, so no axis could move it: write it relative to the \
                 manifest",
                declared_in.display()
            ));
        }
        let dir = lexically_normalized(&base.join(path));
        let member = member && self.membership.as_ref().is_some_and(|rules| rules.takes(&dir));
        self.queue(&dir, member, || {
            format!("the path dependency `{name}` of `{}`", declared_in.display())
        });
        Ok(())
    }

    /// The workspace root's own reads: its members and default members, and
    /// its `[patch]` and `[replace]` tables; then the root as a package.
    fn workspace_root(&mut self, manifest: &Path) -> Result<(), String> {
        let manifest = lexically_normalized(manifest);
        let dir = manifest.parent().unwrap_or(Path::new("")).to_path_buf();
        let table = self.table(&manifest)?.clone();
        if let Some(workspace) = table.get("workspace").and_then(toml::Value::as_table) {
            let strings = |key: &str| -> Vec<String> {
                workspace
                    .get(key)
                    .and_then(toml::Value::as_array)
                    .map(|items| {
                        items.iter().filter_map(toml::Value::as_str).map(str::to_string).collect()
                    })
                    .unwrap_or_default()
            };
            let rules = Membership {
                manifest: manifest.clone(),
                dir: dir.clone(),
                members: strings("members"),
                exclude: strings("exclude"),
            };
            for pattern in rules.members.iter().chain(strings("default-members").iter()) {
                for member in expand_member(&dir, pattern)? {
                    if !rules.excluded(&member.join("Cargo.toml")) {
                        self.queue(&member, true, || {
                            format!("the workspace member `{pattern}` of `{}`", manifest.display())
                        });
                    }
                }
            }
            self.membership = Some(rules);
        }
        for (section, entries) in ["patch", "replace"]
            .into_iter()
            .filter_map(|key| table.get(key).and_then(toml::Value::as_table).map(|t| (key, t)))
        {
            // `[patch.<source>]` holds one table of entries per source;
            // `[replace]` is one table of entries.
            let groups: Vec<&toml::Table> = if section == "patch" {
                entries.values().filter_map(toml::Value::as_table).collect()
            } else {
                vec![entries]
            };
            for group in groups {
                for (name, spec) in group {
                    if let Some(path) = spec.get("path").and_then(toml::Value::as_str) {
                        // A patch is resolved as a dependency, not a member.
                        self.dependency(false, &manifest, name, &dir, path)?;
                    }
                }
            }
        }
        self.queued.insert(manifest.clone());
        if self.members.insert(manifest.clone()) {
            self.pending.push((manifest, true));
        }
        Ok(())
    }

    /// A package's own reads: its directory, its dependency tables (with the
    /// dev-dependencies of a workspace member), and the workspace root it
    /// inherits from, which is its own manifest when it declares `[workspace]`.
    fn package(&mut self, manifest: &Path, member: bool) -> Result<(), String> {
        let dir = manifest.parent().unwrap_or(Path::new("")).to_path_buf();
        let table = self.table(manifest)?.clone();
        if let Some(package) = table.get("package").and_then(toml::Value::as_table) {
            self.trees.insert(dir.clone());
            if let Some(name) = package.get("name").and_then(toml::Value::as_str) {
                self.packages.insert(manifest.to_path_buf(), name.to_string());
            }
        }
        let inherited_root = if inherits(&table) {
            let root = crate::config::policy_manifest(&dir).map_err(|error| {
                format!(
                    "`{}` inherits from its workspace root, which cannot be found: {error}",
                    manifest.display()
                )
            })?;
            root.map(|root| lexically_normalized(&root))
        } else {
            None
        };
        if let Some(root) = inherited_root.as_ref().filter(|root| *root != manifest) {
            self.files.insert(root.clone());
            self.reasons.entry(root.clone()).or_insert_with(|| {
                format!("the workspace root `{}` inherits from", manifest.display())
            });
        }
        let kinds: Vec<&str> = if member {
            DEPENDENCY_TABLES.iter().chain(DEV_DEPENDENCY_TABLES.iter()).copied().collect()
        } else {
            DEPENDENCY_TABLES.to_vec()
        };
        let mut tables: Vec<&toml::Table> = kinds
            .iter()
            .filter_map(|key| table.get(*key).and_then(toml::Value::as_table))
            .collect();
        if let Some(targets) = table.get("target").and_then(toml::Value::as_table) {
            for target in targets.values().filter_map(toml::Value::as_table) {
                tables.extend(
                    kinds.iter().filter_map(|key| target.get(*key).and_then(toml::Value::as_table)),
                );
            }
        }
        let mut deps: Vec<(String, toml::Table)> = Vec::new();
        for deps_table in tables {
            for (name, spec) in deps_table {
                if let Some(spec) = spec.as_table() {
                    deps.push((name.clone(), spec.clone()));
                }
            }
        }
        for (name, spec) in deps {
            if let Some(path) = spec.get("path").and_then(toml::Value::as_str) {
                self.dependency(member, manifest, &name, &dir, path)?;
            } else if spec.get("workspace").and_then(toml::Value::as_bool) == Some(true) {
                // `inherits` saw this key, so the root was looked for and
                // found; Cargo fails a dependency its root does not declare,
                // in the original as in a copy.
                let Some(root) = inherited_root.clone() else { continue };
                let root_dir = root.parent().unwrap_or(Path::new("")).to_path_buf();
                let path = self
                    .table(&root)?
                    .get("workspace")
                    .and_then(|workspace| workspace.get("dependencies"))
                    .and_then(|deps| deps.get(&name))
                    .and_then(|spec| spec.get("path"))
                    .and_then(toml::Value::as_str)
                    .map(str::to_string);
                if let Some(path) = path {
                    self.dependency(member, &root, &name, &root_dir, &path)?;
                }
            }
        }
        Ok(())
    }
}

/// Whether a manifest inherits from a workspace root (a `workspace = true`
/// anywhere outside its own `[workspace]` table, or a `package.workspace`
/// pointer), so that Cargo reads that root for it.
fn inherits(table: &toml::Table) -> bool {
    fn any_inherited(value: &toml::Value) -> bool {
        match value {
            toml::Value::Table(table) => table.iter().any(|(key, value)| {
                (key == "workspace" && value.as_bool() == Some(true)) || any_inherited(value)
            }),
            toml::Value::Array(items) => items.iter().any(any_inherited),
            _ => false,
        }
    }
    let pointer = table
        .get("package")
        .and_then(|package| package.get("workspace"))
        .is_some_and(toml::Value::is_str);
    pointer || table.iter().any(|(key, value)| key != "workspace" && any_inherited(value))
}

/// The member directories a `members` entry names, as Cargo expands it
/// (`members_paths`): a glob relative to the root, each directory it matches;
/// the entry itself when nothing matches.
fn expand_member(dir: &Path, pattern: &str) -> Result<Vec<PathBuf>, String> {
    let joined = dir.join(pattern);
    let Some(text) = joined.to_str() else {
        return Ok(Vec::new());
    };
    let matches = glob::glob(text)
        .map_err(|error| format!("workspace member pattern `{pattern}`: {error}"))?
        .filter_map(Result::ok)
        .filter(|path| path.is_dir())
        .map(|path| lexically_normalized(&path))
        .collect::<Vec<_>>();
    Ok(if matches.is_empty() { vec![lexically_normalized(&joined)] } else { matches })
}

/// Copy `closure` to `to` (which must not exist): each tree whole but for
/// version-control state, Cargo's build output and the `exclude`d
/// directories (`legs::copy_tree`), and each file, every one at its position
/// relative to the closure's root.
pub(crate) fn copy_closure(closure: &PathClosure, to: &Path, exclude: &[&Path]) -> io::Result<()> {
    if to.exists() {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!("`{}` already exists", to.display()),
        ));
    }
    std::fs::create_dir_all(to)?;
    for tree in &closure.trees {
        super::legs::copy_tree(&closure.root.join(tree), &to.join(tree), exclude, &closure.root)?;
    }
    for file in &closure.files {
        let target = to.join(file);
        if let Some(parent) = target.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::copy(closure.root.join(file), &target)?;
    }
    Ok(())
}
