//! Explicit immutable compiler-test input. This owner never selects the build
//! compiler, authenticates source, changes proof authority, or grants execution.
//! The supported closure is native arm64 macOS plus Apple's system runtime TCB.

use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use sha2::{Digest, Sha256};

const MAX_FILES: usize = 100_000;
const MAX_BYTES: u64 = 32 * 1024 * 1024 * 1024;
const HOST_TARGET: &str = "aarch64-apple-darwin";
// Source is compiled from the separately selected checkout, never this SDK's
// packaged source data. Omitting these complete namespaces also avoids treating
// LLVM's foreign/corrupt loader test fixtures as compiler runtime libraries.
const SOURCE_NAMESPACES: &[&str] =
    &["lib/rustlib/src/rust", "lib/rustlib/rustc-src/rust", "lib/rustlib/source-snapshot"];
static NEXT: AtomicU64 = AtomicU64::new(0);

/// Original runtime inputs, without copying or reconstructing a completed
/// producer. The only completion owner is Bootstrap's native runtime Step.
/// This input guard supplies no execution, compatibility, SDK or proof grant.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) struct HeldRuntimeInputs {
    root: PathBuf,
    root_file: File,
    root_stamp: Vec<u64>,
    inventory: Vec<Entry>,
    files: Vec<(File, Vec<u64>, String)>,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) struct OriginalRuntimeEntry<'a> {
    pub(crate) logical: &'a Path,
    pub(crate) target: &'a Path,
    pub(crate) alias: Option<&'a Path>,
    pub(crate) directory: bool,
    pub(crate) executable: bool,
    pub(crate) bytes: Option<u64>,
    pub(crate) sha256: Option<&'a str>,
    pub(crate) descriptor: std::os::fd::BorrowedFd<'a>,
}

/// Input observations borrowed only from the actual retained complete owner.
/// No record/deserializer or arbitrary File constructor creates this offer.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) struct OriginalRuntimeDescriptions<'a> {
    pub(crate) root: &'a Path,
    pub(crate) root_descriptor: std::os::fd::BorrowedFd<'a>,
    pub(crate) entries: Vec<OriginalRuntimeEntry<'a>>,
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl OriginalRuntimeDescriptions<'_> {
    pub(crate) fn count(&self) -> usize {
        1 + self.entries.len()
    }

    fn check_shape(&self) -> Result<(), String> {
        use std::collections::BTreeSet;
        use std::os::fd::AsRawFd as _;
        let readonly = |descriptor| {
            // SAFETY: read-only queries on the actual borrowed original.
            let flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
            let close = unsafe { libc::fcntl(descriptor, libc::F_GETFD) };
            flags >= 0
                && flags & libc::O_ACCMODE == libc::O_RDONLY
                && close >= 0
                && close & libc::FD_CLOEXEC != 0
        };
        if !readonly(self.root_descriptor.as_raw_fd()) {
            return Err("runtime root offer lost original readonly/CLOEXEC custody".into());
        }
        let mut descriptors = BTreeSet::from([self.root_descriptor.as_raw_fd()]);
        for entry in &self.entries {
            if !descriptors.insert(entry.descriptor.as_raw_fd())
                || entry.logical.is_absolute()
                || entry.logical.as_os_str().is_empty()
                || entry
                    .logical
                    .components()
                    .any(|part| !matches!(part, std::path::Component::Normal(_)))
                || !entry.target.starts_with(self.root)
                || entry
                    .alias
                    .is_some_and(|alias| alias.as_os_str().as_encoded_bytes().len() > 4096)
                || if entry.directory {
                    entry.executable || entry.bytes.is_some() || entry.sha256.is_some()
                } else {
                    entry.bytes.is_none()
                        || !entry.sha256.is_some_and(|value| {
                            value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
                        })
                }
            {
                return Err(
                    "original runtime offer has an incomplete or aliased descriptor census".into(),
                );
            }
            // Observe only original open descriptions. Never modify their
            // flags/cursors, reopen their paths, or infer owner authority.
            if !readonly(entry.descriptor.as_raw_fd()) {
                return Err("runtime offer lost original readonly/CLOEXEC input custody".into());
            }
        }
        Ok(())
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl HeldRuntimeInputs {
    pub(crate) fn original_descriptions(&self) -> Result<OriginalRuntimeDescriptions<'_>, String> {
        use std::os::fd::AsFd as _;
        self.check()?;
        if self.files.len() != self.inventory.len()
            || self.files.len().checked_add(1).is_none_or(|count| count > 4096)
        {
            return Err("complete runtime original descriptor census exceeds bound".into());
        }
        let entries = self
            .inventory
            .iter()
            .zip(&self.files)
            .map(|(entry, (file, _, _))| OriginalRuntimeEntry {
                logical: &entry.path,
                target: &entry.target,
                alias: entry.alias.as_deref(),
                directory: entry.directory,
                executable: !entry.directory && entry.executable,
                bytes: (!entry.directory).then_some(entry.bytes),
                sha256: (!entry.directory).then_some(entry.digest.as_str()),
                descriptor: file.as_fd(),
            })
            .collect();
        let original = OriginalRuntimeDescriptions {
            root: &self.root,
            root_descriptor: self.root_file.as_fd(),
            entries,
        };
        original.check_shape()?;
        Ok(original)
    }
    pub(crate) fn capture(root: &Path, host: &str) -> Result<Self, String> {
        use std::os::unix::fs::OpenOptionsExt;
        require_platform(host)?;
        if fs::canonicalize(root).map_err(error)? != root {
            return Err("live runtime root must be its canonical original directory".into());
        }
        let open = |path: &Path| {
            OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK)
                .open(path)
                .map_err(error)
        };
        let root_file = open(root)?;
        let root_stamp = file_stamp(&root_file.metadata().map_err(error)?);
        let inventory = inventory(root, false)?;
        validate_runtime(root, &inventory)?;
        // A live owner holds every selected original description. Refuse a
        // population beyond this profile rather than dropping descriptions.
        if inventory.len().checked_add(1).is_none_or(|count| count > 4096) {
            return Err("live runtime descriptor population exceeds bound".into());
        }
        let mut files = Vec::with_capacity(inventory.len());
        for entry in &inventory {
            let file = open(&entry.target)?;
            let observed = file_stamp(&file.metadata().map_err(error)?);
            if observed != entry.stamp {
                return Err("runtime input changed while opening its original descriptor".into());
            }
            files.push((file, observed, entry.digest.clone()));
        }
        let held = Self { root: root.to_owned(), root_file, root_stamp, inventory, files };
        held.check()?;
        Ok(held)
    }

    pub(crate) fn require_executables(&self, paths: &[PathBuf]) -> Result<(), String> {
        self.check()?;
        for path in paths {
            let relative = path.strip_prefix(&self.root).map_err(error)?;
            if !self
                .inventory
                .iter()
                .any(|entry| entry.path == relative && !entry.directory && entry.executable)
            {
                return Err(format!("completed runtime member is absent: {}", path.display()));
            }
        }
        Ok(())
    }

    pub(crate) fn root(&self) -> &Path {
        &self.root
    }

    pub(crate) fn check(&self) -> Result<(), String> {
        use std::os::unix::fs::FileExt;
        if fs::canonicalize(&self.root).map_err(error)? != self.root
            || file_stamp(&self.root_file.metadata().map_err(error)?) != self.root_stamp
            || file_stamp(&fs::symlink_metadata(&self.root).map_err(error)?) != self.root_stamp
        {
            return Err("original live runtime root changed".into());
        }
        for (file, stamp, expected) in &self.files {
            let before = file.metadata().map_err(error)?;
            if file_stamp(&before) != *stamp {
                return Err("original live runtime descriptor changed".into());
            }
            if before.is_file() {
                // Positional reads leave the original OFD cursor unchanged.
                let mut hash = Sha256::new();
                let mut offset = 0_u64;
                let mut bytes = [0_u8; 64 * 1024];
                loop {
                    let read = file.read_at(&mut bytes, offset).map_err(error)?;
                    if read == 0 {
                        break;
                    }
                    hash.update(&bytes[..read]);
                    offset = offset.checked_add(read as u64).ok_or("runtime size overflow")?;
                    if offset > before.len() {
                        return Err("original live runtime grew while hashing".into());
                    }
                }
                if offset != before.len() || format!("{:x}", hash.finalize()) != *expected {
                    return Err("original live runtime descriptor bytes changed".into());
                }
            }
            if file_stamp(&file.metadata().map_err(error)?) != *stamp {
                return Err("original live runtime changed during hashing".into());
            }
        }
        if inventory(&self.root, false)? != self.inventory {
            return Err("original live runtime namespace or input bytes changed".into());
        }
        validate_runtime(&self.root, &self.inventory)?;
        Ok(())
    }
}

/// Non-cloneable lifetime of one independently copied fixture. Read-only modes
/// detect accidental writes; they are not a same-UID sandbox or an attestation.
pub(crate) struct RetainedCompilerTestFixture {
    root: PathBuf,
    driver: PathBuf,
    receipt: PathBuf,
    identity: String,
    inventory: Vec<Entry>,
    version: String,
    host: String,
}

#[derive(Debug, PartialEq, Eq)]
struct Entry {
    path: PathBuf,
    target: PathBuf,
    directory: bool,
    executable: bool,
    bytes: u64,
    digest: String,
    stamp: Vec<u64>,
    alias: Option<PathBuf>,
}

impl RetainedCompilerTestFixture {
    pub(crate) fn capture(
        source: &Path,
        owned_cache: &Path,
        expected_host: &str,
    ) -> Result<Self, String> {
        require_platform(expected_host)?;
        let source_root = fs::canonicalize(source).map_err(error)?;
        if source != source_root || !source_root.is_dir() {
            return Err("retained compiler source must be its actual canonical directory".into());
        }
        // Bind the complete namespace before running even a compiler query.
        let before = inventory(&source_root, false)?;
        let driver_relative = validate_runtime(&source_root, &before)?;
        let version = probe(&source_root, expected_host)?;
        if inventory(&source_root, false)? != before {
            return Err("compiler fixture changed during native probes".into());
        }
        fs::create_dir_all(owned_cache).map_err(error)?;
        let cache = fs::canonicalize(owned_cache).map_err(error)?;
        if cache.starts_with(&source_root) || source_root.starts_with(&cache) {
            return Err("fixture cache and source must be disjoint directories".into());
        }
        // create_dir is exclusive. No preexisting snapshot is ever adopted.
        let root = loop {
            let name = format!(
                "retained-compiler-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            );
            let candidate = cache.join(name);
            match fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(error(e)),
            }
        };
        let result = (|| {
            copy_inputs(&source_root, &root, &before)?;
            if inventory(&source_root, false)? != before {
                return Err("compiler fixture source changed during copy".into());
            }
            // Copy hashes must match source hashes, but targets/inodes must not.
            let copied = inventory(&root, false)?;
            if !same_contents(&before, &copied) {
                return Err("retained compiler copy differs from original inputs".into());
            }
            validate_runtime(&root, &copied)?;
            if probe(&root, expected_host)? != version {
                return Err("retained compiler copy reports a different compiler identity".into());
            }
            make_readonly(&root)?;
            let retained = inventory(&root, true)?;
            if !same_contents(&before, &retained) || inventory(&source_root, false)? != before {
                return Err("compiler fixture drifted before retained handoff".into());
            }
            let mut digest = Sha256::new();
            add(&mut digest, b"trust.retained-compiler-test-input/v2");
            add(&mut digest, version.as_bytes());
            add(&mut digest, expected_host.as_bytes());
            for entry in &retained {
                add(&mut digest, entry.path.as_os_str().as_encoded_bytes());
                add(&mut digest, &[entry.directory as u8, entry.executable as u8]);
                add(&mut digest, &entry.bytes.to_be_bytes());
                add(&mut digest, entry.digest.as_bytes());
            }
            let identity = format!("{:x}", digest.finalize());
            let receipt = root.with_extension("receipt.json");
            let observations = retained.iter().map(|entry| serde_json::json!({
                "path":entry.path,"directory":entry.directory,"executable":entry.executable,
                "bytes":entry.bytes,"sha256":entry.digest,"original_snapshot_stamp":entry.stamp,
            })).collect::<Vec<_>>();
            let bytes = serde_json::to_vec_pretty(&serde_json::json!({
                "schema":"trust.retained-compiler-test-input/v2", "authority":"test-input-data-only",
                "identity":identity, "source_root":source_root, "snapshot_root":root,
                "host":expected_host,"compiler_version":version,
                "excluded_source_namespaces":SOURCE_NAMESPACES,
                "foreign_target_inputs":"hashed/copied data; never selected host runtime",
                "source_commit":version.lines().find_map(|line| line.strip_prefix("commit-hash: ")),
                "compiler":root.join("bin/trustc"),"loaded_driver":root.join(driver_relative),
                "default_backend_probe":"actual --print cfg; native-host runtime and foreign input hashes bound, no plugin presumed",
                "system_runtime":"Apple system runtime/shared cache TCB; no attestation",
                "inventory":observations,
            })).map_err(error)?;
            let mut receipt_file =
                OpenOptions::new().write(true).create_new(true).open(&receipt).map_err(error)?;
            receipt_file.write_all(&bytes).map_err(error)?;
            let mut permissions = receipt_file.metadata().map_err(error)?.permissions();
            permissions.set_readonly(true);
            receipt_file.set_permissions(permissions).map_err(error)?;
            Ok(Self {
                driver: root.join("bin/trustc"),
                receipt,
                root: root.clone(),
                identity,
                inventory: retained,
                version,
                host: expected_host.to_owned(),
            })
        })();
        if result.is_err() {
            remove_snapshot(&root);
        }
        result
    }

    pub(crate) fn sysroot(&self) -> &Path {
        &self.root
    }
    pub(crate) fn driver(&self) -> &Path {
        &self.driver
    }
    pub(crate) fn receipt_path(&self) -> &Path {
        &self.receipt
    }
    pub(crate) fn identity(&self) -> &str {
        &self.identity
    }
    pub(crate) fn source_commit(&self) -> &str {
        self.version.lines().find_map(|line| line.strip_prefix("commit-hash: ")).unwrap_or("")
    }

    /// Command-construction tests only. Never compiled into bootstrap software.
    #[cfg(test)]
    pub(crate) fn for_command_test(root: PathBuf) -> Self {
        Self {
            driver: root.join("bin/trustc"),
            receipt: root.join("test-input-only-receipt"),
            root,
            identity: "test-input-only".into(),
            inventory: Vec::new(),
            version: "commit-hash: test-input-only".into(),
            host: "test-input-only".into(),
        }
    }

    pub(crate) fn revalidate(&self) -> Result<(), String> {
        #[cfg(test)]
        if self.host == "test-input-only" {
            return Ok(());
        }
        require_platform(&self.host)?;
        if fs::canonicalize(&self.root).map_err(error)? != self.root
            || inventory(&self.root, true)? != self.inventory
        {
            return Err("retained compiler fixture namespace or bytes changed".into());
        }
        validate_runtime(&self.root, &self.inventory)?;
        if probe(&self.root, &self.host)? != self.version
            || inventory(&self.root, true)? != self.inventory
        {
            return Err("retained compiler fixture changed during revalidation".into());
        }
        Ok(())
    }
}

// Successful snapshots and their receipts remain immutable audit inputs after
// the live owner ends. Only incomplete capture namespaces are removed below.

fn error(e: impl std::fmt::Display) -> String {
    e.to_string()
}
fn add(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_be_bytes());
    hash.update(bytes);
}
fn require_platform(host: &str) -> Result<(), String> {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) || host != "aarch64-apple-darwin" {
        Err("retained compiler closure currently supports only native aarch64-apple-darwin".into())
    } else {
        Ok(())
    }
}
fn omitted(path: &Path) -> bool {
    SOURCE_NAMESPACES.iter().any(|namespace| path == Path::new(namespace))
}
fn source_data(path: &Path) -> bool {
    SOURCE_NAMESPACES.iter().any(|namespace| path.starts_with(namespace))
}
// The SDK layout declares target-local inputs below rustlib/<target>/{lib,
// bin,codegen-backends}. Another target's files remain hashed and copied, but
// that namespace cannot supply a native host executable or loader dependency.
fn foreign_target_data(path: &Path) -> bool {
    let Ok(relative) = path.strip_prefix("lib/rustlib") else {
        return false;
    };
    let mut parts = relative.components();
    matches!(
        (parts.next(), parts.next()),
        (Some(std::path::Component::Normal(target)), Some(std::path::Component::Normal(directory)))
            if target != HOST_TARGET && matches!(directory.to_str(), Some("lib" | "bin" | "codegen-backends"))
    )
}
fn hash_file(path: &Path) -> Result<(u64, String), String> {
    let mut file = File::open(path).map_err(error)?;
    let before = file.metadata().map_err(error)?;
    if !before.is_file() || before.len() > MAX_BYTES {
        return Err("invalid fixture file".into());
    }
    let mut hash = Sha256::new();
    let mut total = 0;
    let mut buffer = [0u8; 128 * 1024];
    loop {
        let n = file.read(&mut buffer).map_err(error)?;
        if n == 0 {
            break;
        }
        total += n as u64;
        if total > MAX_BYTES {
            return Err("fixture file exceeds bound".into());
        }
        hash.update(&buffer[..n]);
    }
    let after = file.metadata().map_err(error)?;
    if total != before.len() || !same_file(&before, &after) {
        return Err("fixture file changed while hashing".into());
    }
    Ok((total, format!("{:x}", hash.finalize())))
}
fn same_file(a: &fs::Metadata, b: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        a.dev() == b.dev()
            && a.ino() == b.ino()
            && a.len() == b.len()
            && a.mode() == b.mode()
            && a.mtime() == b.mtime()
            && a.mtime_nsec() == b.mtime_nsec()
            && a.ctime() == b.ctime()
            && a.ctime_nsec() == b.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        a.len() == b.len() && a.modified().ok() == b.modified().ok()
    }
}
fn file_stamp(meta: &fs::Metadata) -> Vec<u64> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        vec![
            meta.dev(),
            meta.ino(),
            meta.mode() as u64,
            meta.len(),
            meta.mtime() as u64,
            meta.mtime_nsec() as u64,
            meta.ctime() as u64,
            meta.ctime_nsec() as u64,
        ]
    }
    #[cfg(not(unix))]
    {
        vec![meta.len()]
    }
}
fn executable(meta: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        meta.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        let _ = meta;
        false
    }
}
fn inventory(root: &Path, readonly: bool) -> Result<Vec<Entry>, String> {
    if !root.join("bin").is_dir() || !root.join("lib").is_dir() {
        return Err("fixture requires bin and lib".into());
    }
    if readonly && !fs::metadata(root).map_err(error)?.permissions().readonly() {
        return Err("fixture root is writable".into());
    }
    let mut entries = Vec::new();
    let mut total = 0u64;
    for directory in ["bin", "lib", "libexec"] {
        if directory == "libexec" && !root.join(directory).try_exists().map_err(error)? {
            continue;
        }
        let walk = walkdir::WalkDir::new(root.join(directory))
            .follow_links(true)
            .max_depth(64)
            .into_iter()
            .filter_entry(|entry| !omitted(entry.path().strip_prefix(root).unwrap()));
        for item in walk {
            let item = item.map_err(error)?;
            let relative = item.path().strip_prefix(root).map_err(error)?.to_owned();
            let target = fs::canonicalize(item.path()).map_err(error)?;
            if !target.starts_with(root) {
                return Err(format!("fixture runtime escapes root: {}", relative.display()));
            }
            let meta = fs::metadata(item.path()).map_err(error)?;
            if item.depth() == 64
                && meta.is_dir()
                && fs::read_dir(&target)
                    .map_err(error)?
                    .next()
                    .transpose()
                    .map_err(error)?
                    .is_some()
            {
                return Err("fixture directory depth exceeds inventory bound".into());
            }
            if readonly
                && (fs::symlink_metadata(item.path()).map_err(error)?.file_type().is_symlink()
                    || !meta.permissions().readonly())
            {
                return Err("retained fixture has an alias or writable entry".into());
            }
            let (bytes, digest) = if meta.is_dir() {
                (0, String::new())
            } else if meta.is_file() {
                hash_file(&target)?
            } else {
                return Err("fixture contains a non-file runtime entry".into());
            };
            total = total.checked_add(bytes).ok_or("fixture size overflow")?;
            if entries.len() >= MAX_FILES || total > MAX_BYTES {
                return Err("fixture inventory exceeds bound".into());
            }
            let alias =
                if fs::symlink_metadata(item.path()).map_err(error)?.file_type().is_symlink() {
                    Some(fs::read_link(item.path()).map_err(error)?)
                } else {
                    None
                };
            entries.push(Entry {
                path: relative,
                target,
                directory: meta.is_dir(),
                executable: executable(&meta),
                bytes,
                digest,
                stamp: file_stamp(&meta),
                alias,
            });
        }
    }
    entries.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(entries)
}
fn same_contents(a: &[Entry], b: &[Entry]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(a, b)| {
            a.path == b.path
                && a.directory == b.directory
                && a.executable == b.executable
                && a.bytes == b.bytes
                && a.digest == b.digest
        })
}
fn copy_inputs(source: &Path, root: &Path, entries: &[Entry]) -> Result<(), String> {
    for entry in entries {
        let destination = root.join(&entry.path);
        if entry.directory {
            fs::create_dir_all(destination).map_err(error)?;
            continue;
        }
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(error)?;
        }
        let selected = source.join(&entry.path);
        if fs::canonicalize(&selected).map_err(error)? != entry.target {
            return Err("fixture alias changed during copy".into());
        }
        let mut original = File::open(&entry.target).map_err(error)?;
        let before = original.metadata().map_err(error)?;
        let mut copy =
            OpenOptions::new().write(true).create_new(true).open(&destination).map_err(error)?;
        std::io::copy(&mut original, &mut copy).map_err(error)?;
        copy.flush().map_err(error)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::{MetadataExt, PermissionsExt};
            let copied = copy.metadata().map_err(error)?;
            if before.dev() == copied.dev() && before.ino() == copied.ino() {
                return Err("fixture copy shares a source inode".into());
            }
            fs::set_permissions(
                &destination,
                fs::Permissions::from_mode(if entry.executable { 0o755 } else { 0o644 }),
            )
            .map_err(error)?;
        }
        if !same_file(&before, &original.metadata().map_err(error)?)
            || hash_file(&destination)? != (entry.bytes, entry.digest.clone())
        {
            return Err("fixture source changed or copy hash differs".into());
        }
    }
    Ok(())
}
fn make_readonly(root: &Path) -> Result<(), String> {
    for entry in walkdir::WalkDir::new(root).contents_first(true) {
        let entry = entry.map_err(error)?;
        let mut permissions = entry.metadata().map_err(error)?.permissions();
        permissions.set_readonly(true);
        fs::set_permissions(entry.path(), permissions).map_err(error)?;
    }
    Ok(())
}
fn remove_snapshot(root: &Path) {
    // Only our exclusively created namespace is removed. Do not follow aliases.
    for entry in walkdir::WalkDir::new(root).follow_links(false).into_iter().flatten() {
        if entry.file_type().is_dir() {
            if let Ok(meta) = entry.metadata() {
                let mut mode = meta.permissions();
                mode.set_readonly(false);
                let _ = fs::set_permissions(entry.path(), mode);
            }
        }
    }
    let _ = fs::remove_dir_all(root);
}

#[cfg(unix)]
fn query(root: &Path, arguments: &[&str]) -> Result<String, String> {
    crate::utils::exec::require_standalone_process("retained compiler fixture query")
        .map_err(error)?;
    use std::os::fd::AsRawFd;
    use std::process::Stdio;
    use std::time::{Duration, Instant};
    let mut child = Command::new(root.join("bin/trustc"))
        .args(arguments)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(error)?;
    let result = (|| {
        let mut stdout = child.stdout.take().ok_or("native query has no stdout")?;
        let mut stderr = child.stderr.take().ok_or("native query has no stderr")?;
        for fd in [stdout.as_raw_fd(), stderr.as_raw_fd()] {
            // SAFETY: each borrowed pipe remains owned throughout this call.
            let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
            if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0
            {
                return Err(error(std::io::Error::last_os_error()));
            }
        }
        let mut out = Vec::new();
        let mut err = Vec::new();
        let mut out_eof = false;
        let mut err_eof = false;
        let mut status = None;
        let deadline = Instant::now() + Duration::from_secs(30);
        while status.is_none() || !out_eof || !err_eof {
            let drain =
                |pipe: &mut dyn Read, bytes: &mut Vec<u8>, eof: &mut bool| -> Result<(), String> {
                    let mut buffer = [0u8; 4096];
                    loop {
                        match pipe.read(&mut buffer) {
                            Ok(0) => {
                                *eof = true;
                                return Ok(());
                            }
                            Ok(n) => {
                                if bytes.len() + n > 64 * 1024 {
                                    return Err("native query exceeds output bound".into());
                                }
                                bytes.extend_from_slice(&buffer[..n]);
                            }
                            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => return Ok(()),
                            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                            Err(e) => return Err(error(e)),
                        }
                    }
                };
            drain(&mut stdout, &mut out, &mut out_eof)?;
            drain(&mut stderr, &mut err, &mut err_eof)?;
            if status.is_none() {
                status = child.try_wait().map_err(error)?;
            }
            if Instant::now() >= deadline {
                return Err("retained native compiler query timed out".into());
            }
            if status.is_none() || !out_eof || !err_eof {
                std::thread::sleep(Duration::from_millis(5));
            }
        }
        if !status.unwrap().success() {
            return Err(format!(
                "retained native compiler query failed: {arguments:?}: {}",
                String::from_utf8_lossy(&err)
            ));
        }
        String::from_utf8(out).map_err(error)
    })();
    if result.is_err() {
        let _ = child.kill();
        let _ = child.wait();
    }
    result
}
#[cfg(not(unix))]
fn query(_root: &Path, _arguments: &[&str]) -> Result<String, String> {
    Err("retained native compiler probes are unsupported on this host".into())
}
fn probe(root: &Path, host: &str) -> Result<String, String> {
    let version = query(root, &["-vV"])?;
    validate_version(&version, host)?;
    let sysroot = query(root, &["--print", "sysroot"])?;
    let stdlib = query(root, &["--print", "target-libdir", "--target", host])?;
    if Path::new(sysroot.trim()) != root
        || Path::new(stdlib.trim()) != root.join("lib/rustlib").join(host).join("lib")
    {
        return Err(
            "native compiler queries escaped the retained root or selected another host".into()
        );
    }
    // LLVM (and, in a full Trust compiler, TrustCG) is linked into the driver.
    // Do not require a nonexistent plugin or introduce a second compiler ABI.
    let cfg = query(root, &["--print", "cfg"])?;
    if !cfg.lines().any(|line| line == "target_arch=\"aarch64\"") {
        return Err("retained compiler default backend does not describe the native host".into());
    }
    Ok(version)
}

fn validate_version(version: &str, host: &str) -> Result<(), String> {
    let field = |prefix: &str| -> Result<&str, String> {
        let mut values = version.lines().filter_map(|line| line.strip_prefix(prefix));
        let value = values.next().ok_or_else(|| format!("compiler identity lacks {prefix}"))?;
        if values.next().is_some() {
            return Err("duplicate native compiler identity field".into());
        }
        Ok(value)
    };
    let commit = field("commit-hash: ")?;
    if !version
        .lines()
        .next()
        .is_some_and(|line| line.starts_with("rustc ") && line.contains("(trustc "))
        || field("binary: ")? != "trustc"
        || field("host: ")? != host
        || field("trust: ")?.is_empty()
        || !matches!(commit.len(), 40 | 64)
        || !commit.bytes().all(|c| c.is_ascii_hexdigit())
    {
        return Err("fixture is not the expected branded native Trust compiler".into());
    }
    Ok(())
}

// Parse native load commands directly. No shell parser, ldd execution, or
// developer search path can add a library outside the selected bin/lib tree.
fn u32at(bytes: &[u8], offset: usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(
        bytes.get(offset..offset + 4).ok_or("truncated Mach-O")?.try_into().map_err(error)?,
    ))
}
fn load_string(command: &[u8], offset: usize) -> Result<String, String> {
    let offset = u32at(command, offset)? as usize;
    let tail = command.get(offset..).ok_or("invalid Mach-O string")?;
    let n = tail.iter().position(|c| *c == 0).ok_or("unterminated Mach-O string")?;
    String::from_utf8(tail[..n].to_vec()).map_err(error)
}
fn expand(value: &str, binary: &Path, root: &Path) -> Result<PathBuf, String> {
    if let Some(rest) = value.strip_prefix("@loader_path/") {
        Ok(binary.parent().unwrap().join(rest))
    } else if value == "@loader_path" {
        Ok(binary.parent().unwrap().to_owned())
    } else if let Some(rest) = value.strip_prefix("@executable_path/") {
        Ok(root.join("bin").join(rest))
    } else if Path::new(value).is_absolute() {
        Ok(PathBuf::from(value))
    } else {
        Err(format!("unsupported native loader path {value}"))
    }
}
fn native_loads(path: &Path) -> Result<Option<(Vec<String>, Vec<String>)>, String> {
    let mut file = File::open(path).map_err(error)?;
    let mut header = [0u8; 32];
    let count = file.read(&mut header).map_err(error)?;
    if count < 4 || u32at(&header, 0)? != 0xfeedfacf {
        return Ok(None);
    }
    if count != 32 || u32at(&header, 4)? != 0x0100000c || !matches!(u32at(&header, 12)?, 2 | 6) {
        return Err("fixture has a non-native Mach-O runtime image".into());
    }
    let count = u32at(&header, 16)? as usize;
    let length = u32at(&header, 20)? as usize;
    if count > 4096 || length > 1024 * 1024 || count > length / 8 {
        return Err("native command bounds exceeded".into());
    }
    let mut bytes = vec![0; length];
    file.read_exact(&mut bytes).map_err(error)?;
    let mut offset = 0usize;
    let mut loads = Vec::new();
    let mut rpaths = Vec::new();
    for _ in 0..count {
        let kind = u32at(&bytes, offset)?;
        let size = u32at(&bytes, offset + 4)? as usize;
        if size < 8 || size % 8 != 0 {
            return Err("invalid native load command".into());
        }
        let command = bytes
            .get(offset..offset.checked_add(size).ok_or("command overflow")?)
            .ok_or("truncated native command")?;
        match kind {
            0xc | 0x80000018 | 0x8000001f | 0x20 | 0x80000023 => {
                loads.push(load_string(command, 8)?)
            }
            0x8000001c => rpaths.push(load_string(command, 8)?),
            0xe => {
                if load_string(command, 8)? != "/usr/lib/dyld" {
                    return Err("unsupported native loader".into());
                }
            }
            0x2 | 0xb | 0xd | 0x19 | 0x1a | 0x1b | 0x1d | 0x1e | 0x22 | 0x80000022 | 0x24
            | 0x26 | 0x80000028 | 0x29 | 0x2a | 0x2b | 0x2d | 0x2e | 0x32 | 0x80000033
            | 0x80000034 | 0x36 => {}
            _ => return Err(format!("unsupported native load command {kind:#x}")),
        }
        offset += size;
    }
    if offset != bytes.len() {
        return Err("native load-command census differs".into());
    }
    Ok(Some((loads, rpaths)))
}

// Native runtime roles must never turn an unknown/fat/corrupt image into
// uninspected data. Ordinary rlibs and other bound inputs remain data.
fn requires_native_inspection(entry: &Entry) -> bool {
    let shared_library =
        entry.path.extension().and_then(|extension| extension.to_str()).is_some_and(|extension| {
            ["dylib", "so", "dll"].iter().any(|expected| extension.eq_ignore_ascii_case(expected))
        });
    !entry.directory
        && !foreign_target_data(&entry.path)
        && (shared_library
            || (entry.executable
                && (entry.path.starts_with("bin")
                    || entry.path.starts_with("libexec")
                    || entry.path.starts_with("lib/rustlib/aarch64-apple-darwin"))))
}

fn validate_runtime(root: &Path, entries: &[Entry]) -> Result<PathBuf, String> {
    let hostlib = Path::new("lib/rustlib/aarch64-apple-darwin/lib");
    let drivers: Vec<_> = entries
        .iter()
        .filter(|e| {
            !e.directory
                && e.path.parent() == Some(Path::new("lib"))
                && e.path.file_name().unwrap().to_string_lossy().starts_with("librustc_driver-")
                && e.path.extension().is_some_and(|e| e == "dylib")
        })
        .collect();
    if drivers.len() != 1
        || !entries.iter().any(|e| {
            e.path.parent() == Some(hostlib)
                && e.path.file_name().unwrap().to_string_lossy().starts_with("libstd-")
                && e.path.extension().is_some_and(|x| x == "rlib")
        })
        || !entries.iter().any(|e| {
            e.path.parent() == Some(hostlib)
                && e.path.file_name().unwrap().to_string_lossy().starts_with("libcore-")
                && e.path.extension().is_some_and(|x| x == "rlib")
        })
    {
        return Err("fixture lacks one actual driver or complete host std/core inputs".into());
    }
    let paths: BTreeSet<_> =
        entries.iter().filter(|e| !e.directory).map(|e| root.join(&e.path)).collect();
    let mut compiler_loads_driver = false;
    for entry in entries.iter().filter(|e| !e.directory) {
        if foreign_target_data(&entry.path) {
            continue;
        }
        let target_relative = entry.target.strip_prefix(root).map_err(error)?;
        if foreign_target_data(target_relative) || source_data(target_relative) {
            return Err("selected host input aliases source or foreign target data".into());
        }
        let path = root.join(&entry.path);
        let native = native_loads(&path)?;
        if entry.path == Path::new("bin/trustc") && (!entry.executable || native.is_none()) {
            return Err("fixture trustc is not an actual native executable".into());
        }
        if requires_native_inspection(entry) && native.is_none() {
            return Err(format!(
                "fixture runtime is not an inspectable native image: {}",
                entry.path.display()
            ));
        }
        if let Some((loads, rpaths)) = native {
            for load in loads {
                if (load.starts_with("/usr/lib/") || load.starts_with("/System/Library/"))
                    && load
                        .split('/')
                        .skip(1)
                        .all(|part| !part.is_empty() && part != "." && part != "..")
                {
                    continue;
                }
                let selected = if let Some(suffix) = load.strip_prefix("@rpath/") {
                    let mut found = BTreeSet::new();
                    for rpath in &rpaths {
                        let candidate = expand(rpath, &path, root)?.join(suffix);
                        if let Ok(candidate) = fs::canonicalize(candidate) {
                            found.insert(candidate);
                        }
                    }
                    if found.len() != 1 {
                        return Err(format!("ambiguous/missing native runtime {load}"));
                    }
                    found.into_iter().next().unwrap()
                } else {
                    fs::canonicalize(expand(&load, &path, root)?).map_err(error)?
                };
                if !selected.starts_with(root) || !paths.contains(&selected) {
                    return Err(format!(
                        "native compiler runtime is outside fixture: {}",
                        selected.display()
                    ));
                }
                let selected_relative = selected.strip_prefix(root).map_err(error)?;
                if foreign_target_data(selected_relative) || source_data(selected_relative) {
                    return Err(
                        "native compiler runtime resolves to source or foreign target data".into(),
                    );
                }
                if native_loads(&selected)?.is_none() {
                    return Err(format!(
                        "native load target cannot be inspected: {}",
                        selected.display()
                    ));
                }
                if entry.path == Path::new("bin/trustc") && selected == root.join(&drivers[0].path)
                {
                    compiler_loads_driver = true;
                }
            }
        }
    }
    if !compiler_loads_driver {
        return Err("native trustc does not load the selected compiler driver".into());
    }
    Ok(drivers[0].path.clone())
}

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
mod tests;
