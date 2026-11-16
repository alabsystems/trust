//! Frozen Git and resolved dependency source binding for paired qualification.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha1::{Digest as _, Sha1};
use trust_sha2::{Digest as _, Sha256};

use crate::tree::{self, Fingerprint};
use crate::{Git, Result, canonical_hex, refusal};

pub const SCOPE: &str = "trust.qualification.source-content.v1";
pub const DEPENDENCY_SCOPE: &str = "trust.qualification.dependency-content.v1";
const MAX_REPOSITORIES: usize = 1024;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceIdentity {
    pub path: PathBuf,
    pub commit: String,
    pub tree: String,
    pub working_sha256: String,
    pub scope: String,
    pub lock_sha256: Option<String>,
    pub cargo_checkout_marker: Option<MarkerIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MarkerIdentity {
    pub sha256: String,
    stamp: Fingerprint,
}

/// Bind Cargo's single empty checkout-complete marker without following a
/// replaced link or blocking on a FIFO. It is never an exception for sources.
pub fn cargo_checkout_marker(root: &Path) -> Result<Option<MarkerIdentity>> {
    marker_after_inspection(root, || {})
}

pub(crate) fn marker_after_inspection(
    root: &Path,
    after_inspection: impl FnOnce(),
) -> Result<Option<MarkerIdentity>> {
    let path = root.join(".cargo-ok");
    let before = match fs::symlink_metadata(&path) {
        Ok(m) => m,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    };
    if !before.file_type().is_file() || before.len() != 0 {
        return Err(refusal(format!("invalid Cargo checkout marker: {}", path.display())));
    }
    let stamp = Fingerprint::of(&before);
    after_inspection();
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(&path)?;
    let mut byte = [0];
    if Fingerprint::of(&file.metadata()?) != stamp
        || file.read(&mut byte)? != 0
        || Fingerprint::of(&file.metadata()?) != stamp
        || Fingerprint::of(&fs::symlink_metadata(&path)?) != stamp
    {
        return Err(refusal(format!("Cargo checkout marker changed: {}", path.display())));
    }
    Ok(Some(MarkerIdentity { sha256: tree::hash_bytes(b""), stamp }))
}

pub fn identity(
    git: &impl Git,
    root: &Path,
    require_lock: bool,
    cargo_checkout: bool,
) -> Result<SourceIdentity> {
    let mut visited = BTreeSet::new();
    identity_inner(git, root, require_lock, cargo_checkout, &mut visited)
}

fn text(git: &impl Git, root: &Path, args: &[&str]) -> Result<String> {
    let bytes = git.probe(root, args)?;
    let bytes = bytes.strip_suffix(b"\n").unwrap_or(&bytes);
    String::from_utf8(bytes.to_vec()).map_err(|_| refusal("non-UTF8 Git identity"))
}

fn nul_records<'a>(bytes: &'a [u8], context: &str) -> Result<Vec<&'a [u8]>> {
    if bytes.is_empty() {
        return Ok(Vec::new());
    }
    let bytes =
        bytes.strip_suffix(&[0]).ok_or_else(|| refusal(format!("{context} lacks terminal NUL")))?;
    let records = bytes.split(|b| *b == 0).collect::<Vec<_>>();
    if records.iter().any(|row| row.is_empty()) {
        return Err(refusal(format!("{context} contains empty row")));
    }
    Ok(records)
}

fn identity_inner(
    git: &impl Git,
    root: &Path,
    require_lock: bool,
    cargo_checkout: bool,
    visited: &mut BTreeSet<PathBuf>,
) -> Result<SourceIdentity> {
    let root = fs::canonicalize(root)?;
    if !visited.insert(root.clone()) || visited.len() > MAX_REPOSITORIES {
        return Err(refusal("source repository closure is cyclic or exceeds 1024 repositories"));
    }
    git.validate_repository(&root)?;
    if Path::new(&text(git, &root, &["rev-parse", "--show-toplevel"])?) != root {
        return Err(refusal(format!("not an exact repository root: {}", root.display())));
    }
    let marker = if cargo_checkout { cargo_checkout_marker(&root)? } else { None };
    let before_commit = text(git, &root, &["rev-parse", "HEAD"])?;
    let before_tree = text(git, &root, &["rev-parse", "HEAD^{tree}"])?;
    if !canonical_hex(&before_commit, 40) || !canonical_hex(&before_tree, 40) {
        return Err(refusal(
            "paired qualification currently requires canonical SHA-1 Git identities",
        ));
    }
    let status = git.probe(
        &root,
        &["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none"],
    )?;
    for row in nul_records(&status, "source status")? {
        if !(cargo_checkout && marker.is_some() && row == b"?? .cargo-ok") {
            return Err(refusal(format!("source is dirty: {}", root.display())));
        }
    }
    let flags = git.probe(&root, &["ls-files", "-v", "-z"])?;
    for row in nul_records(&flags, "index visibility")? {
        if row.len() < 3 || row[1] != b' ' || row[0].is_ascii_lowercase() || row[0] == b'S' {
            return Err(refusal(format!(
                "source has hidden or malformed index paths: {}",
                root.display()
            )));
        }
    }
    let inventory = git.probe(&root, &["ls-tree", "-r", "-z", "HEAD"])?;
    let mut rows = Vec::new();
    let mut bound_files = BTreeSet::new();
    for row in nul_records(&inventory, "HEAD tree")? {
        let separator = row
            .iter()
            .position(|b| *b == b'\t')
            .ok_or_else(|| refusal("malformed Git tree row"))?;
        let header = std::str::from_utf8(&row[..separator])
            .map_err(|_| refusal("non-ASCII Git tree header"))?;
        let fields = header.split(' ').collect::<Vec<_>>();
        if fields.len() != 3 || !canonical_hex(fields[2], 40) {
            return Err(refusal("malformed Git tree fields"));
        }
        let relative = PathBuf::from(OsStr::from_bytes(&row[separator + 1..]));
        let path = tree::no_link_ancestors(&root, &relative)?;
        if fields[1] == "blob" && fields[0] != "120000" {
            bound_files.insert(path.clone());
        }
        rows.push((fields[0], fields[1], fields[2], relative, path));
    }
    let mut digest = Sha256::new();
    digest.update(SCOPE);
    digest.update([0]);
    for (mode, kind, oid, relative, path) in rows {
        let metadata = fs::symlink_metadata(&path)?;
        let mut resolved_target = Vec::new();
        let contents = match (mode, kind) {
            ("160000", "commit") => {
                if !metadata.file_type().is_dir() {
                    return Err(refusal("source submodule is not an exact directory"));
                }
                let child = identity_inner(git, &path, false, false, visited)?;
                if child.commit != oid {
                    return Err(refusal(format!(
                        "source submodule disagrees with its pin: {}",
                        path.display()
                    )));
                }
                serde_json::to_vec(&child)
                    .map_err(|e| refusal(format!("cannot encode source closure: {e}")))?
            }
            ("120000", "blob") => {
                let contents = tree::path_bytes(&tree::read_link(&path)?);
                let target = fs::canonicalize(&path)?;
                if !bound_files.contains(&target)
                    || !fs::symlink_metadata(&target)?.file_type().is_file()
                {
                    return Err(refusal(format!(
                        "source link escapes the fully bound regular-file closure: {}",
                        path.display()
                    )));
                }
                // A committed link can traverse an ignored intermediate hop.
                // Binding all regular files does not identify WHICH one that
                // hop selected. Keep original link bytes for Git's blob check,
                // and separately bind the selected file's canonical identity.
                resolved_target = tree::path_bytes(
                    target
                        .strip_prefix(&root)
                        .map_err(|_| refusal("resolved source link escaped its root"))?,
                );
                contents
            }
            ("100644" | "100755", "blob") => {
                let actual = if metadata.mode() & 0o111 != 0 { "100755" } else { "100644" };
                if actual != mode {
                    return Err(refusal(format!(
                        "source executable mode differs from HEAD: {}",
                        path.display()
                    )));
                }
                tree::read_file(&path)?
            }
            _ => return Err(refusal(format!("unsupported source tree entry: {}", path.display()))),
        };
        if kind == "blob" {
            let mut blob = Sha1::new();
            blob.update(format!("blob {}\0", contents.len()).as_bytes());
            blob.update(&contents);
            if format!("{:x}", blob.finalize()) != oid {
                return Err(refusal(format!(
                    "working source bytes differ from HEAD: {}",
                    path.display()
                )));
            }
        }
        for field in
            [mode.as_bytes(), tree::path_bytes(&relative).as_slice(), &contents, &resolved_target]
        {
            digest.update((field.len() as u64).to_be_bytes());
            digest.update(field);
        }
    }
    if text(git, &root, &["rev-parse", "HEAD"])? != before_commit
        || text(git, &root, &["rev-parse", "HEAD^{tree}"])? != before_tree
        || (cargo_checkout && cargo_checkout_marker(&root)? != marker)
    {
        return Err(refusal("source identity changed while binding"));
    }
    let lock = root.join("Cargo.lock");
    let lock_sha256 =
        if require_lock || lock.try_exists()? { Some(tree::hash_file(&lock)?) } else { None };
    Ok(SourceIdentity {
        path: root,
        commit: before_commit,
        tree: before_tree,
        working_sha256: format!("{:x}", digest.finalize()),
        scope: SCOPE.into(),
        lock_sha256,
        cargo_checkout_marker: marker,
    })
}

pub fn path_package_bound(git: &impl Git, manifest: &Path, root: &Path) -> Result<()> {
    let root = fs::canonicalize(root)?;
    let manifest = fs::canonicalize(manifest)?;
    let relative = manifest
        .strip_prefix(&root)
        .map_err(|_| refusal("path package is outside frozen source"))?;
    let tracked = git.probe(&root, &["ls-files", "-z"])?;
    if !nul_records(&tracked, "tracked path package")?.contains(&relative.as_os_str().as_bytes()) {
        return Err(refusal(format!("unbound path-package manifest: {}", manifest.display())));
    }
    let package = relative.parent().ok_or_else(|| refusal("path package has no parent"))?;
    let package = package.to_str().ok_or_else(|| refusal("path package is not UTF8"))?;
    let package = if package.is_empty() { "." } else { package };
    let ignored = git.probe(
        &root,
        &["ls-files", "--others", "--ignored", "--exclude-standard", "-z", "--", package],
    )?;
    for name in nul_records(&ignored, "ignored package inputs")? {
        if !name.starts_with(b"target/")
            && name != b".cargo/config"
            && name != b".cargo/config.toml"
        {
            return Err(refusal(format!(
                "unbound ignored path-package input: {}",
                root.join(OsStr::from_bytes(name)).display()
            )));
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DependencyIdentity {
    pub path: PathBuf,
    pub sha256: String,
    pub scope: String,
}

pub fn dependency_identity(root: &Path) -> Result<DependencyIdentity> {
    let root = fs::canonicalize(root)?;
    let before = tree::stats(&root, true, &[])?;
    let entries = tree::entries(&root, true, &[])?;
    let resolved_links = tree::closed_links(&root, &entries)?;
    let mut digest = Sha256::new();
    digest.update(DEPENDENCY_SCOPE);
    digest.update([0]);
    for relative in entries {
        let path = tree::no_link_ancestors(&root, &relative)?;
        let metadata = fs::symlink_metadata(&path)?;
        let contents = if metadata.file_type().is_symlink() {
            tree::path_bytes(&tree::read_link(&path)?)
        } else if metadata.file_type().is_file() {
            tree::hash_file(&path)?.into_bytes()
        } else if metadata.file_type().is_dir() {
            Vec::new()
        } else {
            return Err(refusal("unsupported dependency source entry"));
        };
        for field in [
            tree::path_bytes(&relative).as_slice(),
            metadata.mode().to_string().as_bytes(),
            &contents,
            &resolved_links.get(&relative).map(|path| tree::path_bytes(path)).unwrap_or_default(),
        ] {
            digest.update((field.len() as u64).to_be_bytes());
            digest.update(field);
        }
    }
    if tree::stats(&root, true, &[])? != before {
        return Err(refusal("dependency tree changed while binding"));
    }
    Ok(DependencyIdentity {
        path: root,
        sha256: format!("{:x}", digest.finalize()),
        scope: DEPENDENCY_SCOPE.into(),
    })
}
