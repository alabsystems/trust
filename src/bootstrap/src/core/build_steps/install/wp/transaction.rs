//! Trust: descriptor-owned independent copies and atomic, no-replace publication.

use std::ffi::{CString, OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::{Builder, components, repo};
use crate::utils::trust_repo_cache as cache;

const MANIFEST: &str = "TRUST-WP-INSTALLATION.json";

mod source;

fn error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn name(name: &OsStr) -> Result<CString, String> {
    if name.is_empty() || name == "." || name == ".." || name.as_bytes().contains(&b'/') {
        return Err("expected one installation entry name".into());
    }
    CString::new(name.as_bytes()).map_err(error)
}

fn syscall(result: libc::c_int) -> Result<libc::c_int, String> {
    if result < 0 { Err(io::Error::last_os_error().to_string()) } else { Ok(result) }
}

fn same_inode(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.dev() == right.dev() && left.ino() == right.ino() && left.file_type() == right.file_type()
}

struct Directory {
    file: File,
    path: PathBuf,
}

impl Directory {
    fn open(path: &Path) -> Result<Self, String> {
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(path)
            .map_err(error)?;
        let result = Self { file, path: path.to_owned() };
        result.check()?;
        Ok(result)
    }

    fn check(&self) -> Result<(), String> {
        if !same_inode(
            &self.file.metadata().map_err(error)?,
            &fs::symlink_metadata(&self.path).map_err(error)?,
        ) || fs::canonicalize(&self.path).map_err(error)? != self.path
        {
            return Err(format!("installation namespace moved: {}", self.path.display()));
        }
        Ok(())
    }

    fn open_entry(&self, entry: &OsStr, flags: libc::c_int) -> Result<File, String> {
        let entry = name(entry)?;
        // SAFETY: valid retained directory FD and NUL-terminated single entry.
        let fd = unsafe {
            libc::openat(
                self.file.as_raw_fd(),
                entry.as_ptr(),
                flags | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                0o600,
            )
        };
        // SAFETY: a successful openat returns a new owned descriptor.
        Ok(unsafe { File::from_raw_fd(syscall(fd)?) })
    }

    fn child(&self, entry: &OsStr) -> Result<Self, String> {
        let file = self.open_entry(entry, libc::O_RDONLY | libc::O_DIRECTORY)?;
        let result = Self { file, path: self.path.join(entry) };
        result.check()?;
        Ok(result)
    }

    fn create_child(&self, entry: &OsStr) -> Result<Self, String> {
        let c_name = name(entry)?;
        // SAFETY: valid retained parent and single entry, no path traversal.
        let result = unsafe { libc::mkdirat(self.file.as_raw_fd(), c_name.as_ptr(), 0o700) };
        if result < 0 && io::Error::last_os_error().kind() != io::ErrorKind::AlreadyExists {
            return Err(io::Error::last_os_error().to_string());
        }
        self.child(entry)
    }

    fn entries(&self) -> Result<Vec<OsString>, String> {
        self.check()?;
        let mut entries = fs::read_dir(&self.path)
            .map_err(error)?
            .map(|entry| entry.map(|entry| entry.file_name()).map_err(error))
            .collect::<Result<Vec<_>, _>>()?;
        entries.sort();
        self.check()?;
        Ok(entries)
    }
}

fn file_hash(file: &mut File) -> Result<Vec<u8>, String> {
    file.rewind().map_err(error)?;
    let mut hash = Sha256::new();
    let mut buffer = [0; 65536];
    loop {
        let count = file.read(&mut buffer).map_err(error)?;
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
    }
    Ok(hash.finalize().to_vec())
}

fn same_contents_metadata(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    same_inode(left, right)
        && left.nlink() == right.nlink()
        && left.mode() == right.mode()
        && left.len() == right.len()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

// Absolute input paths matter to repository/tool identities. This artifact moves
// exactly once, so its identity frames relative entry names instead of its root.
fn artifact_digest(directory: &Directory) -> Result<String, String> {
    fn visit(directory: &Directory, hash: &mut Sha256) -> Result<(), String> {
        let before = directory.file.metadata().map_err(error)?;
        let entries = directory.entries()?;
        cache::add(hash, b"directory");
        cache::add(hash, (before.mode() & 0o777).to_le_bytes());
        cache::add(hash, entries.len().to_le_bytes());
        for entry in &entries {
            cache::add(hash, entry.as_bytes());
            let mut file = directory.open_entry(entry, libc::O_RDONLY)?;
            let before = file.metadata().map_err(error)?;
            if before.is_dir() {
                visit(&directory.child(entry)?, hash)?;
            } else if before.is_file() {
                if before.nlink() != 1 {
                    return Err("artifact file is not independently owned".into());
                }
                cache::add(hash, b"file");
                cache::add(hash, (before.mode() & 0o777).to_le_bytes());
                cache::add(hash, file_hash(&mut file)?);
            } else {
                return Err("artifact identity requires regular files and directories".into());
            }
            let named = directory.open_entry(entry, libc::O_RDONLY)?.metadata().map_err(error)?;
            if !same_contents_metadata(&before, &file.metadata().map_err(error)?)
                || !same_contents_metadata(&before, &named)
            {
                return Err("artifact entry changed during identity observation".into());
            }
        }
        if directory.entries()? != entries
            || !same_contents_metadata(&before, &directory.file.metadata().map_err(error)?)
        {
            return Err("artifact directory changed during identity observation".into());
        }
        directory.check()
    }
    let mut hash = Sha256::new();
    cache::add(&mut hash, b"trust.native-installation-artifact/v1");
    visit(directory, &mut hash)?;
    Ok(cache::finish(hash))
}

fn copy_image(source: &Directory, destination: &Directory) -> Result<(), String> {
    for entry in source.entries()? {
        let mut input = source.open_entry(&entry, libc::O_RDONLY)?;
        let before = input.metadata().map_err(error)?;
        if before.is_dir() {
            copy_image(&source.child(&entry)?, &destination.create_child(&entry)?)?;
        } else if before.is_file() {
            let expected = file_hash(&mut input)?;
            match destination.open_entry(&entry, libc::O_RDWR | libc::O_CREAT | libc::O_EXCL) {
                Ok(mut output) => {
                    if output.metadata().map_err(error)?.nlink() != 1 {
                        return Err("new component output is not independently owned".into());
                    }
                    input.rewind().map_err(error)?;
                    io::copy(&mut input, &mut output).map_err(error)?;
                    if file_hash(&mut output)? != expected {
                        return Err("component bytes changed during independent copy".into());
                    }
                    output
                        .set_permissions(fs::Permissions::from_mode(before.mode() & 0o777))
                        .map_err(error)?;
                    output.sync_all().map_err(error)?;
                }
                Err(_) => {
                    // Component overlap is legal only when bytes and executable bits agree.
                    let mut output = destination.open_entry(&entry, libc::O_RDONLY)?;
                    let metadata = output.metadata().map_err(error)?;
                    if !metadata.is_file()
                        || metadata.nlink() != 1
                        || file_hash(&mut output)? != expected
                        || metadata.mode() & 0o777 != before.mode() & 0o777
                    {
                        return Err(format!(
                            "conflicting component entry: {}",
                            destination.path.join(&entry).display()
                        ));
                    }
                }
            }
            let after = input.metadata().map_err(error)?;
            if !same_inode(&before, &after)
                || before.len() != after.len()
                || before.mode() != after.mode()
                || file_hash(&mut input)? != expected
            {
                return Err("component artifact changed during copy".into());
            }
        } else {
            return Err("component images must contain only regular files and directories".into());
        }
    }
    source.check()?;
    destination.check()
}

fn freeze(directory: &Directory) -> Result<(), String> {
    for entry in directory.entries()? {
        let file = directory.open_entry(&entry, libc::O_RDONLY)?;
        let metadata = file.metadata().map_err(error)?;
        if metadata.is_dir() {
            freeze(&directory.child(&entry)?)?;
        } else if metadata.is_file() {
            if metadata.nlink() != 1 {
                return Err("cannot freeze an externally linked artifact".into());
            }
            file.set_permissions(fs::Permissions::from_mode(metadata.mode() & 0o555))
                .map_err(error)?;
            file.sync_all().map_err(error)?;
        } else {
            return Err("cannot finalize a nonregular installation entry".into());
        }
    }
    directory.file.set_permissions(fs::Permissions::from_mode(0o555)).map_err(error)?;
    directory.file.sync_all().map_err(error)
}

/// Remove only the generated tree while its retained directory still owns its name.
fn cleanup(directory: &Directory) -> Result<(), String> {
    directory.check()?;
    directory.file.set_permissions(fs::Permissions::from_mode(0o700)).map_err(error)?;
    for entry in directory.entries()? {
        let file = directory.open_entry(&entry, libc::O_RDONLY)?;
        let metadata = file.metadata().map_err(error)?;
        let flags = if metadata.is_dir() {
            cleanup(&directory.child(&entry)?)?;
            libc::AT_REMOVEDIR
        } else {
            0
        };
        let entry = name(&entry)?;
        // SAFETY: unlink is confined to the retained owned generated directory.
        syscall(unsafe { libc::unlinkat(directory.file.as_raw_fd(), entry.as_ptr(), flags) })?;
    }
    Ok(())
}

struct Publication {
    parent: Directory,
    stage: Directory,
    destination: OsString,
    lock: File,
    lock_name: OsString,
    published: bool,
}

impl Publication {
    fn claim(destination: &Path) -> Result<Self, String> {
        let parent = Directory::open(destination.parent().ok_or("installation has no parent")?)?;
        let metadata = parent.file.metadata().map_err(error)?;
        // SAFETY: geteuid has no preconditions.
        if metadata.uid() != unsafe { libc::geteuid() } || metadata.mode() & 0o022 != 0 {
            return Err(
                "installation parent must be owned by this user and not writable by others".into(),
            );
        }
        let destination_name =
            destination.file_name().ok_or("installation has no final name")?.to_owned();
        name(&destination_name)?;
        let mut lock_name = OsString::from(".");
        lock_name.push(&destination_name);
        lock_name.push(".trust-wp-installation.lock");
        let lock = parent.open_entry(&lock_name, libc::O_RDWR | libc::O_CREAT)?;
        let metadata = lock.metadata().map_err(error)?;
        if !metadata.is_file()
            || metadata.nlink() != 1
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.mode() & 0o077 != 0
        {
            return Err("installation ownership file is not a private regular file".into());
        }
        lock.try_lock().map_err(|e| format!("installation destination is already owned: {e}"))?;
        match fs::symlink_metadata(destination) {
            Ok(_) => {
                return Err(
                    "installation destination already exists; never overwrite an installation"
                        .into(),
                );
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.to_string()),
        }
        let temporary = tempfile::Builder::new()
            .prefix(".trust-wp-pending-")
            .tempdir_in(&parent.path)
            .map_err(error)?;
        let stage = Directory::open(&temporary.keep())?;
        let result = Self {
            parent,
            stage,
            destination: destination_name,
            lock,
            lock_name,
            published: false,
        };
        result.check()?;
        Ok(result)
    }

    fn check(&self) -> Result<(), String> {
        self.parent.check()?;
        self.stage.check()?;
        let lock = self.parent.open_entry(&self.lock_name, libc::O_RDONLY)?;
        if !same_inode(&self.lock.metadata().map_err(error)?, &lock.metadata().map_err(error)?) {
            return Err("installation destination ownership moved".into());
        }
        Ok(())
    }

    fn publish(&mut self) -> Result<PathBuf, String> {
        self.check()?;
        let from = name(self.stage.path.file_name().unwrap())?;
        let to = name(&self.destination)?;
        #[cfg(target_os = "macos")]
        unsafe extern "C" {
            fn renameatx_np(
                fromfd: libc::c_int,
                from: *const libc::c_char,
                tofd: libc::c_int,
                to: *const libc::c_char,
                flags: libc::c_uint,
            ) -> libc::c_int;
        }
        // SAFETY: both names are single entries in the retained parent. EXCL/NOREPLACE
        // refuses even an empty competing directory; plain rename would overwrite it.
        #[cfg(target_os = "macos")]
        syscall(unsafe {
            renameatx_np(
                self.parent.file.as_raw_fd(),
                from.as_ptr(),
                self.parent.file.as_raw_fd(),
                to.as_ptr(),
                libc::RENAME_EXCL,
            )
        })?;
        #[cfg(target_os = "linux")]
        syscall(unsafe {
            libc::renameat2(
                self.parent.file.as_raw_fd(),
                from.as_ptr(),
                self.parent.file.as_raw_fd(),
                to.as_ptr(),
                libc::RENAME_NOREPLACE,
            )
        })?;
        self.published = true;
        self.stage.path = self.parent.path.join(&self.destination);
        self.check()?;
        self.parent.file.sync_all().map_err(error)?;
        Ok(self.stage.path.clone())
    }
}

impl Drop for Publication {
    fn drop(&mut self) {
        if !self.published && self.parent.check().is_ok() && cleanup(&self.stage).is_ok() {
            if let Ok(entry) = name(self.stage.path.file_name().unwrap()) {
                // SAFETY: cleanup checked the owned directory identity; remove no other tree.
                let _ = unsafe {
                    libc::unlinkat(self.parent.file.as_raw_fd(), entry.as_ptr(), libc::AT_REMOVEDIR)
                };
            }
        }
        // The private ownership file persists so another claimant cannot replace its inode.
    }
}

fn require_clean_source(root: &Path, expected: &str) -> Result<(), String> {
    let toplevel = cache::git(root, &["rev-parse", "--show-toplevel"])?;
    let toplevel = toplevel.strip_suffix(b"\n").ok_or("invalid Git worktree toplevel")?;
    if fs::canonicalize(Path::new(OsStr::from_bytes(toplevel))).map_err(error)?
        != fs::canonicalize(root).map_err(error)?
    {
        return Err("Git worktree differs from the observed installation source root".into());
    }
    if !cache::git(root, &["for-each-ref", "--format=%(refname)", "refs/replace/"])?.is_empty() {
        return Err(
            "Git replacement refs cannot establish raw committed installation sources".into()
        );
    }
    let head = cache::git(root, &["rev-parse", "--verify", "HEAD^{commit}"])?;
    if String::from_utf8_lossy(&head).trim() != expected {
        return Err("source HEAD moved from the compiler's selected current commit".into());
    }
    // Status trusts index flags. A committed-install claim cannot omit bytes
    // merely because assume-unchanged, skip-worktree or fsmonitor hides them.
    for flags in ["-v", "-f"] {
        let entries = cache::git(root, &["ls-files", flags, "-z"])?;
        for entry in entries.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
            if entry.len() < 3
                || entry[1] != b' '
                || entry[0].is_ascii_lowercase()
                || entry[0] == b'S'
            {
                return Err(format!(
                    "hidden or invalid index flags cannot establish clean installation sources at {}",
                    root.display()
                ));
            }
        }
    }
    let output = cache::git(
        root,
        &["status", "--porcelain=v1", "--untracked-files=normal", "--ignore-submodules=none"],
    )?;
    if !output.is_empty() {
        return Err("immutable current installation requires clean committed sources and matching submodules".into());
    }
    let index = cache::git(root, &["ls-files", "--stage", "-z"])?;
    for entry in index.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
        let text = std::str::from_utf8(entry).map_err(error)?;
        let (metadata, _) = text.split_once('\t').ok_or("invalid committed input inventory")?;
        let fields = metadata.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || fields[2] != "0" {
            return Err("unmerged index cannot establish committed installation sources".into());
        }
    }
    source::require_committed_tree(root, expected)?;
    if cache::git(root, &["rev-parse", "--verify", "HEAD^{commit}"])? != head {
        return Err("source HEAD moved while establishing clean installation sources".into());
    }
    Ok(())
}

fn require_clean(builder: &Builder<'_>) -> Result<(), String> {
    // Trust: the only caller that hands the observer this checkout refuses
    // under cfg(test), whoever calls it (see run()).
    if cfg!(test) {
        return Err("the complete-source observer never reads the checkout under cfg(test)".into());
    }
    require_clean_source(
        &builder.src,
        builder.version_info().sha().ok_or("current source commit is required")?,
    )
}

fn inputs_unchanged(
    before: &cache::InputSnapshot,
    after: &cache::InputSnapshot,
) -> Result<(), String> {
    if before != after {
        return Err(
            "source/config/native inputs changed during installation; no completion claim".into()
        );
    }
    Ok(())
}

pub(super) fn run(builder: &Builder<'_>) -> Result<(), String> {
    if builder.config.dry_run() {
        components(builder);
        builder.info("native immutable WP installation: fixed stage-2 components; no WP qualification or proof claim");
        return Ok(());
    }
    // Trust: a unit test never reaches the complete-source observer: past this
    // point it reads this checkout, every submodule and HEAD. The landing gate's
    // audit of this file (scripts/gates/land-escape-audits.toml) declares that
    // bootstrap's tests read none of them, and this makes it hold whoever calls.
    if cfg!(test) {
        return Err("the complete-source observer never reads the checkout under cfg(test)".into());
    }
    let mut publication = Publication::claim(builder.config.prefix.as_deref().unwrap())?;
    require_clean(builder)?;
    let before = repo::installation_inputs(builder)?;
    let components = components(builder);
    let images = components
        .iter()
        .map(|(name, component)| {
            let path =
                component.component_image().ok_or("component owner supplied no install image")?;
            Ok((*name, path, cache::tree_digest(path)?))
        })
        .collect::<Result<Vec<_>, String>>()?;
    for (_, path, _) in &images {
        copy_image(&Directory::open(path)?, &publication.stage)?;
    }
    let manifest = serde_json::json!({
        "schema": "trust.native-wp-installation/v1",
        "authority": "independently copied current native compiler/std/private/tool component images; no WP qualification, proof or release claim",
        "commit": builder.version_info().sha().ok_or("current source commit is required")?,
        "release": builder.rust_release(),
        "host": builder.host_target.triple.to_string(),
        "inputs": before.digest(),
        "components": images.iter().map(|(name, _, digest)| (*name, digest)).collect::<Vec<_>>(),
    });
    let mut manifest_file = publication
        .stage
        .open_entry(OsStr::new(MANIFEST), libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL)?;
    serde_json::to_writer_pretty(&mut manifest_file, &manifest).map_err(error)?;
    manifest_file.write_all(b"\n").map_err(error)?;
    manifest_file.sync_all().map_err(error)?;
    drop(manifest_file);
    freeze(&publication.stage)?;
    repo::check_wp_installation(builder, &publication.stage.path)?;
    let artifact = artifact_digest(&publication.stage)?;
    require_clean(builder)?;
    inputs_unchanged(&before, &repo::installation_inputs(builder)?)?;
    for (_, path, digest) in &images {
        if cache::tree_digest(path)? != *digest {
            return Err("component artifacts changed during installation; nothing published".into());
        }
    }
    if artifact_digest(&publication.stage)? != artifact {
        return Err("installation bytes changed before publication".into());
    }
    let installed = publication.publish()?;
    repo::check_wp_installation(builder, &installed)?;
    if artifact_digest(&publication.stage)? != artifact {
        return Err("installation changed at finalization; no completion claim".into());
    }
    require_clean(builder)?;
    inputs_unchanged(&before, &repo::installation_inputs(builder)?)?;
    builder.info(&format!("native immutable WP installation: {} (SHA-256 {artifact}); no WP qualification, proof or release claim", installed.display()));
    Ok(())
}

#[cfg(test)]
mod tests;
