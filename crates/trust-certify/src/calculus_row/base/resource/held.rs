// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Descriptor-relative DATA staging on Darwin and Linux. All input validation
//! and both ancestry checks precede the first mkdir. Each later name lookup is
//! relative to a held directory and rejects symlinks and special files.
//! Mutation parents exclude foreign-UID writers through modes and ACLs. Root
//! and this UID are trusted; the directory lock coordinates cooperating
//! stagers, while Bootstrap's caller owns its exclusive build lifecycle lease.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::fs::{File, Metadata, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use nix::libc;
use trust_resource_provenance::data_directory;
use sha2::{Digest, Sha256};

use super::super::{MANIFEST, MAX_CAPTURE_BYTES, MAX_MODULES, MAX_PART_BYTES, Manifest};
use super::StageReport;

const RESOURCE: &str = "vf5-base-v1";
const MAX_ENTRIES: usize = MAX_MODULES * 16;
const MAX_DEPTH: usize = 128;
static NEXT_STAGE: AtomicU64 = AtomicU64::new(0);

fn refused(reason: &str) -> io::Error { io::Error::other(reason) }
fn identity(meta: &Metadata) -> (u64, u64) { (meta.dev(), meta.ino()) }
fn open_at(parent: &File, leaf: &OsStr, directory: bool) -> io::Result<File> {
    if directory { data_directory::open_directory_at(parent, leaf) }
    else { data_directory::open_regular_at(parent, leaf) }
}
fn mkdir_at(parent: &File, leaf: &OsStr) -> io::Result<()> {
    data_directory::create_directory_at(parent, leaf)
}

struct Root {
    file: File,
    path: PathBuf,
    original: (u64, u64),
    bindings: Vec<(PathBuf, (u64, u64), Option<PathBuf>)>,
}
impl Root {
    fn open(path: &Path) -> io::Result<Self> {
        if path.components().any(|part| matches!(part, Component::ParentDir | Component::CurDir)) {
            return Err(refused("non-normal VF5 root"));
        }
        let path = if path.is_absolute() { path.to_owned() } else { std::env::current_dir()?.join(path) };
        let mut bindings = Vec::new();
        let mut prefix = PathBuf::new();
        let mut aliases = 0;
        for component in path.components() {
            prefix.push(component.as_os_str());
            let metadata = std::fs::symlink_metadata(&prefix)?;
            let target = if metadata.file_type().is_symlink() {
                let target = std::fs::read_link(&prefix)?;
                let sibling = prefix.parent().unwrap_or(Path::new("/")).join("build.noindex");
                if prefix == path || prefix.file_name() != Some(OsStr::new("build"))
                    || aliases != 0 || (target != Path::new("build.noindex") && target != sibling)
                    || !std::fs::symlink_metadata(&sibling)?.is_dir()
                { return Err(refused("VF5 root has an unlicensed ancestor alias")); }
                aliases += 1;
                Some(target)
            } else {
                if !metadata.is_dir() { return Err(refused("VF5 root ancestor is not a directory")); }
                None
            };
            bindings.push((prefix.clone(), identity(&metadata), target));
        }
        // Only Bootstrap's literal build -> sibling build.noindex ancestor
        // alias is accepted for an output. Every ancestor/alias identity and
        // target is bookended. All other package/output aliases refuse.
        let file = OpenOptions::new().read(true).custom_flags(
            libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK,
        ).open(&path)?;
        let original = identity(&file.metadata()?);
        let root = Self { file, path, original, bindings };
        root.check()?;
        Ok(root)
    }
    fn check(&self) -> io::Result<()> {
        for (path, original, target) in &self.bindings {
            let metadata = std::fs::symlink_metadata(path)?;
            if identity(&metadata) != *original
                || metadata.file_type().is_symlink() != target.is_some()
                || target.as_ref().is_some_and(|target| std::fs::read_link(path).ok().as_ref() != Some(target))
            { return Err(refused("VF5 root ancestor or build alias changed")); }
        }
        let current = OpenOptions::new().read(true).custom_flags(
            libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK,
        ).open(&self.path)?;
        if identity(&current.metadata()?) != self.original
            || identity(&self.file.metadata()?) != self.original
        { return Err(refused("VF5 original root or selected name changed")); }
        Ok(())
    }

    // Protect the namespace naming the output root as well as the output
    // directory itself. Root/current-UID ancestors are trusted. A public
    // sticky ancestor (e.g. /tmp) protects only a root/current-UID child;
    // nonsticky public write or an ACL grant refuses before any mkdir.
    fn check_mutation_namespace(&self) -> io::Result<()> {
        self.check()?;
        for (index, (path, original, alias)) in self.bindings.iter().enumerate() {
            let selected = match alias {
                Some(target) if target.is_absolute() => target.clone(),
                Some(target) => path.parent().unwrap_or(Path::new("/")).join(target),
                None => path.clone(),
            };
            let directory = OpenOptions::new().read(true).custom_flags(
                libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK,
            ).open(selected)?;
            let metadata = directory.metadata()?;
            if !metadata.is_dir() || ![0, data_directory::effective_uid()].contains(&metadata.uid())
                || (alias.is_none() && identity(&metadata) != *original)
            { return Err(refused("VF5 output namespace belongs to an untrusted principal")); }
            trust_resource_provenance::require_no_acl_grants(&directory)?;
            if metadata.mode() & 0o022 != 0 {
                let child = self.bindings.get(index + 1)
                    .ok_or_else(|| refused("VF5 output root has public write access"))?;
                let child_uid = std::fs::symlink_metadata(&child.0)?.uid();
                if metadata.mode() & 0o1000 == 0
                    || ![0, data_directory::effective_uid()].contains(&child_uid)
                { return Err(refused("VF5 output namespace permits a foreign writer")); }
            }
        }
        owned_directory(&self.file)?;
        self.check()
    }
}

fn same_child(parent: &File, leaf: &OsStr, original: &File) -> io::Result<()> {
    let current = open_at(parent, leaf, true)?;
    if identity(&current.metadata()?) != identity(&original.metadata()?) {
        return Err(refused("VF5 held directory's parent name changed"));
    }
    Ok(())
}

fn ancestor(ancestor: &File, child: &File) -> io::Result<bool> {
    let expected = identity(&ancestor.metadata()?);
    let mut child = open_at(child, OsStr::new("."), true)?;
    for _ in 0..1024 {
        let here = identity(&child.metadata()?);
        if here == expected { return Ok(true); }
        let parent = open_at(&child, OsStr::new(".."), true)?;
        if identity(&parent.metadata()?) == here { return Ok(false); }
        child = parent;
    }
    Err(refused("VF5 ancestry exceeds descriptor walk bound"))
}

fn disjoint(source: &Root, output: &Root) -> io::Result<()> {
    source.check()?;
    output.check()?;
    if ancestor(&source.file, &output.file)? || ancestor(&output.file, &source.file)? {
        return Err(refused("VF5 source and output trees overlap"));
    }
    source.check()?;
    output.check()
}

fn names(directory: &File) -> io::Result<Vec<OsString>> {
    data_directory::names(directory, MAX_ENTRIES)
}

fn read_at(parent: &File, leaf: &OsStr) -> io::Result<Vec<u8>> {
    let file = open_at(parent, leaf, false)?;
    let before = file.metadata()?;
    if before.len() > MAX_PART_BYTES { return Err(refused("oversized VF5 DATA member")); }
    let mut bytes = Vec::new();
    (&file).take(MAX_PART_BYTES + 1).read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if bytes.len() as u64 != before.len() || bytes.len() as u64 > MAX_PART_BYTES
        || identity(&before) != identity(&after) || before.len() != after.len()
        || before.mtime() != after.mtime() || before.mtime_nsec() != after.mtime_nsec()
        || before.ctime() != after.ctime() || before.ctime_nsec() != after.ctime_nsec()
        || identity(&open_at(parent, leaf, false)?.metadata()?) != identity(&before)
    { return Err(refused("VF5 input changed during descriptor read")); }
    Ok(bytes)
}

#[derive(PartialEq, Eq)]
struct Snapshot {
    files: BTreeMap<PathBuf, Vec<u8>>,
    directories: BTreeSet<PathBuf>,
    modules: usize,
}
impl Snapshot {
    fn capture(root: &File, digest: &str) -> io::Result<Self> {
        let manifest_bytes = read_at(root, OsStr::new(MANIFEST))?;
        if format!("{:x}", Sha256::digest(&manifest_bytes)) != digest {
            return Err(refused("VF5 raw manifest digest differs from request"));
        }
        let manifest: Manifest = serde_json::from_slice(&manifest_bytes)
            .map_err(|error| refused(&format!("invalid VF5 manifest: {error}")))?;
        super::super::validate_manifest(&manifest)
            .map_err(|error| refused(&format!("invalid VF5 package: {error:?}")))?;
        let mut expected = BTreeMap::from([(PathBuf::from(MANIFEST), Some(digest.to_owned()))]);
        let mut directories = BTreeSet::from([PathBuf::from("modules")]);
        for module in &manifest.modules {
            let base = Path::new("modules").join(&module.path);
            if base.components().count() > MAX_DEPTH {
                return Err(refused("VF5 module path exceeds depth bound"));
            }
            for (path, digest) in [
                (base.clone(), Some(&module.base_sha256)),
                (base.with_extension("olean.server"), module.server_sha256.as_ref()),
                (base.with_extension("olean.private"), module.private_sha256.as_ref()),
                (base.with_extension("ir"), module.ir_sha256.as_ref()),
            ] {
                if expected.insert(path.clone(), digest.cloned()).is_some() {
                    return Err(refused("colliding VF5 package member names"));
                }
                let mut parent = path.parent();
                while let Some(path) = parent.filter(|path| !path.as_os_str().is_empty()) {
                    directories.insert(path.to_owned());
                    parent = path.parent();
                }
            }
        }
        if expected.len() + directories.len() > MAX_ENTRIES {
            return Err(refused("VF5 package inventory exceeds entry bound"));
        }
        let mut snapshot = Self { files: BTreeMap::new(), directories: BTreeSet::new(), modules: manifest.modules.len() };
        let mut bytes = 0usize;
        snapshot.walk(root, Path::new(""), &expected, &directories, &mut bytes)?;
        let present = expected.values().filter(|digest| digest.is_some()).count();
        if snapshot.files.len() != present || snapshot.directories != directories {
            return Err(refused("VF5 package is missing an inventoried member"));
        }
        if snapshot.files.get(Path::new(MANIFEST)) != Some(&manifest_bytes) {
            return Err(refused("VF5 manifest changed during package capture"));
        }
        Ok(snapshot)
    }

    fn walk(
        &mut self, parent: &File, relative: &Path,
        expected: &BTreeMap<PathBuf, Option<String>>, directories: &BTreeSet<PathBuf>,
        bytes: &mut usize,
    ) -> io::Result<()> {
        for leaf in names(parent)? {
            let path = relative.join(&leaf);
            if directories.contains(&path) {
                let child = open_at(parent, &leaf, true)?;
                self.directories.insert(path.clone());
                self.walk(&child, &path, expected, directories, bytes)?;
                same_child(parent, &leaf, &child)?;
            } else {
                let digest = expected.get(&path).and_then(Option::as_ref)
                    .ok_or_else(|| refused("VF5 package has an unlisted or absent-slot member"))?;
                let contents = read_at(parent, &leaf)?;
                *bytes = bytes.checked_add(contents.len()).filter(|count| *count <= MAX_CAPTURE_BYTES)
                    .ok_or_else(|| refused("VF5 package bytes exceed capture bound"))?;
                if format!("{:x}", Sha256::digest(&contents)) != *digest {
                    return Err(refused("VF5 member digest differs from raw manifest"));
                }
                self.files.insert(path, contents);
            }
        }
        Ok(())
    }
    fn report(&self, digest: &str, reused: bool) -> StageReport {
        StageReport {
            manifest_sha256: digest.into(), modules: self.modules, files: self.files.len(),
            bytes: self.files.values().map(|bytes| bytes.len() as u64).sum(), reused,
        }
    }
}

fn owned_directory(file: &File) -> io::Result<()> {
    data_directory::require_owner_mutation_scope(file)
}

fn child(parent: &File, leaf: &OsStr) -> io::Result<File> {
    let file = match open_at(parent, leaf, true) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            mkdir_at(parent, leaf)?;
            open_at(parent, leaf, true)?
        }
        Err(error) => return Err(error),
    };
    owned_directory(&file)?;
    same_child(parent, leaf, &file)?;
    Ok(file)
}

fn descend(root: &File, relative: &Path) -> io::Result<File> {
    owned_directory(root)?;
    let mut directory = open_at(root, OsStr::new("."), true)?;
    for part in relative.components() {
        let Component::Normal(part) = part else { return Err(refused("non-normal VF5 output member")); };
        directory = open_at(&directory, part, true)?;
        owned_directory(&directory)?;
    }
    Ok(directory)
}

fn write_at(parent: &File, leaf: &OsStr, bytes: &[u8]) -> io::Result<()> {
    data_directory::write_new_at(parent, leaf, bytes)
}
fn publish(parent: &File, temporary: &OsStr, staging: &File) -> io::Result<()> {
    data_directory::publish_directory_exclusive_at(parent, temporary, staging, OsStr::new(RESOURCE))
}

pub(super) fn stage(package: &Path, digest: &str, sysroot: &Path) -> Result<StageReport, String> {
    stage_with_hook(package, digest, sysroot, || {}).map_err(|error| error.to_string())
}

fn stage_with_hook(
    package: &Path, digest: &str, sysroot: &Path, before_copy: impl FnOnce(),
) -> io::Result<StageReport> {
    stage_with_hooks(package, digest, sysroot, before_copy, |_, _| {})
}

fn stage_with_hooks(
    package: &Path, digest: &str, sysroot: &Path, before_copy: impl FnOnce(),
    before_publish: impl FnOnce(&File, &OsStr),
) -> io::Result<StageReport> {
    let source = Root::open(package)?;
    let output = Root::open(sysroot)?;
    owned_directory(&output.file)?;
    output.check_mutation_namespace()?;
    let _directory_lease = data_directory::try_lock_owner_directory(&output.file)?;
    disjoint(&source, &output)?;
    let snapshot = Snapshot::capture(&source.file, digest)?;
    disjoint(&source, &output)?;
    // No filesystem mutation has occurred before complete DATA and ancestry
    // admission. Bootstrap passes only the already owned sysroot endpoint.
    let lib = child(&output.file, OsStr::new("lib"))?;
    output.check()?;
    disjoint(&source, &output)?;
    same_child(&output.file, OsStr::new("lib"), &lib)?;
    let trust = child(&lib, OsStr::new("trust"))?;
    let check = || -> io::Result<()> {
        disjoint(&source, &output)?;
        output.check_mutation_namespace()?;
        owned_directory(&lib)?;
        owned_directory(&trust)?;
        same_child(&output.file, OsStr::new("lib"), &lib)?;
        same_child(&lib, OsStr::new("trust"), &trust)
    };
    check()?;
    match open_at(&trust, OsStr::new(RESOURCE), true) {
        Ok(existing) => {
            let installed = Snapshot::capture(&existing, digest)?;
            if installed != snapshot { return Err(refused("existing VF5 resource differs from input")); }
            same_child(&trust, OsStr::new(RESOURCE), &existing)?;
            if Snapshot::capture(&source.file, digest)? != snapshot {
                return Err(refused("VF5 source changed during reuse"));
            }
            check()?;
            return Ok(snapshot.report(digest, true));
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    let temporary = OsString::from(format!(".vf5-base-v1-stage-{}-{}",
        std::process::id(), NEXT_STAGE.fetch_add(1, Ordering::Relaxed)));
    mkdir_at(&trust, &temporary)?;
    let staging = open_at(&trust, &temporary, true)?;
    owned_directory(&staging)?;
    // Failed attempts retain their bounded, uniquely created staging DATA;
    // no cleanup path ever traverses a possibly swapped projected name.
    before_copy();
    check()?;
    same_child(&trust, &temporary, &staging)?;
    for path in &snapshot.directories {
        check()?;
        same_child(&trust, &temporary, &staging)?;
        let parent = descend(&staging, path.parent().unwrap_or(Path::new("")))?;
        mkdir_at(&parent, path.file_name().ok_or_else(|| refused("missing VF5 directory name"))?)?;
        parent.sync_all()?;
    }
    for (path, bytes) in &snapshot.files {
        check()?;
        same_child(&trust, &temporary, &staging)?;
        let parent = descend(&staging, path.parent().unwrap_or(Path::new("")))?;
        write_at(&parent, path.file_name().ok_or_else(|| refused("missing VF5 file name"))?, bytes)?;
        parent.sync_all()?;
    }
    if Snapshot::capture(&staging, digest)? != snapshot
        || Snapshot::capture(&source.file, digest)? != snapshot
    { return Err(refused("VF5 source or staged DATA changed before publication")); }
    check()?;
    same_child(&trust, &temporary, &staging)?;
    staging.sync_all()?;
    // Test injection occupies the exact old outer-check/rename window. The
    // protected primitive re-admits its parent and expected source FD before
    // name-based rename; foreign UIDs cannot mutate that admitted parent.
    before_publish(&trust, &temporary);
    publish(&trust, &temporary, &staging)?;
    trust.sync_all()?;
    same_child(&trust, OsStr::new(RESOURCE), &staging)?;
    check()?;
    if Snapshot::capture(&staging, digest)? != snapshot {
        return Err(refused("VF5 published DATA changed before completion"));
    }
    Ok(snapshot.report(digest, false))
}

#[cfg(test)]
mod tests;
