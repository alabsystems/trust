//! Trust: isolate an untrusted retained OUT_DIR before running its producer.
//!
//! Only the selected cache entry is renamed. Cleanup concerns our exclusive
//! quarantine, never a recursive removal of the original selected pathname.

use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};

use crate::CargoResult;
use crate::util::file_identity::{
    OpenedFileIdentity, metadata_is_plain_directory, opened_file_identity,
};

const PREVIOUS: &str = "previous";

#[cfg(test)]
thread_local! {
    static CONFLICT_AT_CREATE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Trust: retains the old generation until the actual dirty job completes.
/// This is local filesystem custody, not a process-drain or proof receipt.
pub(in crate::compiler) struct RetiredGeneration {
    quarantine: Option<tempfile::TempDir>,
    parent: File,
    parent_path: PathBuf,
    parent_identity: OpenedFileIdentity,
    container: File,
    container_name: OsString,
    container_identity: OpenedFileIdentity,
    original: Option<Node>,
    owner: u32,
    cleanup_enabled: bool,
}

impl RetiredGeneration {
    fn validate(&self) -> CargoResult<()> {
        if self.owner != std::process::id() {
            bail!("retired generation belongs to another process");
        }
        let parent = open_directory(&self.parent_path)?;
        if !self
            .parent_identity
            .same_file(&opened_file_identity(&parent)?)
        {
            bail!("generation parent was replaced");
        }
        let quarantine = self
            .quarantine
            .as_ref()
            .context("quarantine already closed")?;
        let relative = open_directory_at(&self.parent, &self.container_name, quarantine.path())?;
        let named = open_directory(quarantine.path())?;
        if !self
            .container_identity
            .same_file(&opened_file_identity(&relative)?)
            || !self
                .container_identity
                .same_file(&opened_file_identity(&named)?)
            || !self
                .container_identity
                .same_file(&opened_file_identity(&self.container)?)
        {
            bail!("generation quarantine was replaced");
        }
        let moved = node_at(
            &self.container,
            OsStr::new(PREVIOUS),
            &quarantine.path().join(PREVIOUS),
        )?;
        match (&self.original, moved) {
            (None, None) => {}
            (Some(original), Some(moved)) if original.same(&moved)? => {}
            _ => bail!("retired generation entry was replaced"),
        }
        Ok(())
    }
}

impl Drop for RetiredGeneration {
    fn drop(&mut self) {
        let Some(quarantine) = &self.quarantine else {
            return;
        };
        let path = quarantine.path().to_owned();
        if !self.cleanup_enabled {
            tracing::debug!(path = %path.display(), "preserving incomplete build-script generation reset");
            return;
        }
        if let Err(error) = self.validate() {
            tracing::debug!(%error, path = %path.display(), "preserving retired build-script generation");
            return;
        }
        // Trust: the invalid tree may contain mounted or otherwise foreign
        // descendants. Never recursively traverse it, even through std's
        // symlink-safe remover. Keep nonempty retired output as evidence for
        // separately scoped reclamation. Only empty directories are removed.
        if self.original.is_some() {
            if let Err(error) = fs::remove_dir(path.join(PREVIOUS)) {
                tracing::debug!(%error, path = %path.display(), "preserving nonempty retired build-script generation");
                return;
            }
        }
        if let Err(error) = fs::remove_dir(&path) {
            tracing::debug!(%error, path = %path.display(), "could not remove empty generation quarantine");
        }
    }
}

pub(super) fn reset(out_dir: &Path) -> CargoResult<RetiredGeneration> {
    if !out_dir.is_absolute() {
        bail!("generated output directory must be absolute");
    }
    let parent_path = out_dir.parent().context("generated output has no parent")?;
    let name = out_dir
        .file_name()
        .context("generated output has no leaf")?;
    let parent = open_directory(parent_path)?;
    let parent_identity = opened_file_identity(&parent)?;
    let original = node_at(&parent, name, out_dir)?;
    let mut quarantine = tempfile::Builder::new()
        .prefix(".targo-retired-generation-")
        .tempdir_in(parent_path)?;
    // Trust: from this point every error must preserve the selected old entry.
    // In particular, a failed identity check must not recursively clean a path
    // that another actor may have replaced.
    quarantine.disable_cleanup(true);
    let kept_path = quarantine.path().to_owned();
    let result = (|| {
        let container_name = quarantine
            .path()
            .file_name()
            .context("quarantine has no leaf")?
            .to_owned();
        let container = open_directory_at(&parent, &container_name, quarantine.path())?;
        let container_identity = opened_file_identity(&container)?;
        let named = open_directory(quarantine.path())?;
        if !container_identity.same_file(&opened_file_identity(&named)?)
            || !parent_identity.same_file(&opened_file_identity(&open_directory(parent_path)?)?)
        {
            bail!("generation parent changed while creating quarantine");
        }
        // Trust: check the original entry again immediately before the anchored
        // rename. No missing or foreign entry is adopted as the old generation.
        let current = node_at(&parent, name, out_dir)?;
        match (&original, current) {
            (None, None) => {}
            (Some(original), Some(current)) if original.same(&current)? => {}
            _ => bail!("generated output changed before retirement"),
        }
        if original.is_some() {
            move_entry(
                &parent,
                name,
                out_dir,
                &container,
                &quarantine.path().join(PREVIOUS),
            )?;
        }
        let mut retired = RetiredGeneration {
            quarantine: Some(quarantine),
            parent,
            parent_path: parent_path.to_owned(),
            parent_identity,
            container,
            container_name,
            container_identity,
            original,
            owner: std::process::id(),
            cleanup_enabled: false,
        };
        retired.validate()?;
        #[cfg(test)]
        if CONFLICT_AT_CREATE.with(|conflict| conflict.replace(false)) {
            // Trust: model another creator winning the exclusive mkdir race.
            fs::create_dir(out_dir)?;
            fs::write(out_dir.join("foreign"), b"preserve")?;
        }
        create_directory_at(&retired.parent, name, out_dir)?;
        let fresh = open_directory_at(&retired.parent, name, out_dir)?;
        if !metadata_is_plain_directory(&fresh.metadata()?) {
            bail!("fresh generated output is not a plain directory");
        }
        // Trust: creation and opening are separate operations. Detect a named
        // replacement visible during setup; this is not confinement against
        // an uncooperative writer changing OUT_DIR after the last check.
        let fresh_identity = opened_file_identity(&fresh)?;
        let named = open_directory(out_dir)?;
        let relative = open_directory_at(&retired.parent, name, out_dir)?;
        if !fresh_identity.same_file(&opened_file_identity(&named)?)
            || !fresh_identity.same_file(&opened_file_identity(&relative)?)
        {
            bail!("fresh generated output was replaced during setup");
        }
        retired.validate()?;
        retired.cleanup_enabled = true;
        Ok(retired)
    })();
    if let Err(error) = &result {
        tracing::debug!(%error, path = %kept_path.display(), "preserving failed build-script generation reset");
    }
    result
}

fn open_directory(path: &Path) -> CargoResult<File> {
    if !metadata_is_plain_directory(&fs::symlink_metadata(path)?) {
        bail!("generation path is not a plain directory");
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC);
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt as _;
        options
            .share_mode(0x1 | 0x2 | 0x4)
            .custom_flags(0x0200_0000 | 0x0020_0000);
    }
    let file = options.open(path)?;
    if !metadata_is_plain_directory(&file.metadata()?) {
        bail!("opened generation path is not a plain directory");
    }
    Ok(file)
}

#[cfg(unix)]
fn name_cstr(name: &OsStr) -> CargoResult<std::ffi::CString> {
    use std::os::unix::ffi::OsStrExt as _;
    Ok(std::ffi::CString::new(name.as_bytes())?)
}

#[cfg(unix)]
fn open_directory_at(parent: &File, name: &OsStr, _path: &Path) -> CargoResult<File> {
    use std::os::fd::{AsRawFd as _, FromRawFd as _};
    let name = name_cstr(name)?;
    // SAFETY: both descriptor and C string remain live; success gives a new FD.
    let fd = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            name.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    Ok(unsafe { File::from_raw_fd(fd) })
}

#[cfg(not(unix))]
fn open_directory_at(_parent: &File, _name: &OsStr, path: &Path) -> CargoResult<File> {
    open_directory(path)
}

#[cfg(unix)]
struct Node {
    device: u64,
    inode: u64,
    kind: u32,
    // Trust: keep the original plain directory pinned through retirement.
    _handle: Option<File>,
}

#[cfg(unix)]
impl Node {
    fn same(&self, other: &Self) -> CargoResult<bool> {
        Ok((self.device, self.inode, self.kind) == (other.device, other.inode, other.kind))
    }
}

#[cfg(unix)]
fn node_at(parent: &File, name: &OsStr, path: &Path) -> CargoResult<Option<Node>> {
    use std::os::fd::AsRawFd as _;
    use std::os::unix::fs::MetadataExt as _;
    let encoded = name_cstr(name)?;
    let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: writable stat storage, held descriptor and terminated leaf name.
    if unsafe {
        libc::fstatat(
            parent.as_raw_fd(),
            encoded.as_ptr(),
            metadata.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        let error = std::io::Error::last_os_error();
        if error.kind() == std::io::ErrorKind::NotFound {
            return Ok(None);
        }
        return Err(error.into());
    }
    let metadata = unsafe { metadata.assume_init() };
    let kind = metadata.st_mode as u32 & libc::S_IFMT as u32;
    let flags = if kind == libc::S_IFDIR as u32 {
        Some(libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
    } else if kind == libc::S_IFREG as u32 {
        Some(libc::O_RDONLY | libc::O_NONBLOCK | libc::O_NOFOLLOW | libc::O_CLOEXEC)
    } else {
        #[cfg(any(target_os = "linux", target_os = "android"))]
        {
            Some(libc::O_PATH | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        }
        #[cfg(target_os = "macos")]
        {
            (kind == libc::S_IFLNK as u32)
                .then_some(libc::O_RDONLY | libc::O_SYMLINK | libc::O_CLOEXEC)
        }
        #[cfg(not(any(target_os = "linux", target_os = "android", target_os = "macos")))]
        {
            None
        }
    };
    let handle = if let Some(flags) = flags {
        // SAFETY: original held directory and terminated leaf remain live.
        let fd = unsafe { libc::openat(parent.as_raw_fd(), encoded.as_ptr(), flags) };
        if fd < 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        use std::os::fd::FromRawFd as _;
        let file = unsafe { File::from_raw_fd(fd) };
        let opened = file.metadata()?;
        if opened.dev() != metadata.st_dev as u64
            || opened.ino() != metadata.st_ino as u64
            || opened.mode() & libc::S_IFMT as u32 != kind
        {
            bail!("generated entry changed while opening");
        }
        Some(file)
    } else {
        None
    };
    let _ = path;
    Ok(Some(Node {
        device: metadata.st_dev as u64,
        inode: metadata.st_ino as u64,
        kind,
        _handle: handle,
    }))
}

#[cfg(not(unix))]
struct Node {
    identity: OpenedFileIdentity,
    _handle: File,
}

#[cfg(not(unix))]
impl Node {
    fn same(&self, other: &Self) -> CargoResult<bool> {
        Ok(self.identity.same_file(&other.identity))
    }
}

#[cfg(not(unix))]
fn node_at(_parent: &File, _name: &OsStr, path: &Path) -> CargoResult<Option<Node>> {
    match fs::symlink_metadata(path) {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(windows)]
    {
        use std::os::windows::fs::OpenOptionsExt as _;
        // Trust: open the reparse object itself, including a directory symlink.
        // DELETE sharing permits the owned rename while this handle stays live.
        options
            .share_mode(0x1 | 0x2 | 0x4)
            .custom_flags(0x0200_0000 | 0x0020_0000);
    }
    let handle = options.open(path)?;
    Ok(Some(Node {
        identity: opened_file_identity(&handle)?,
        _handle: handle,
    }))
}

#[cfg(unix)]
fn move_entry(
    parent: &File,
    name: &OsStr,
    _source: &Path,
    container: &File,
    _destination: &Path,
) -> CargoResult<()> {
    use std::os::fd::AsRawFd as _;
    let name = name_cstr(name)?;
    let previous = name_cstr(OsStr::new(PREVIOUS))?;
    // SAFETY: both original directories and leaf strings remain live.
    if unsafe {
        libc::renameat(
            parent.as_raw_fd(),
            name.as_ptr(),
            container.as_raw_fd(),
            previous.as_ptr(),
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error().into());
    }
    Ok(())
}

#[cfg(not(unix))]
fn move_entry(
    _parent: &File,
    _name: &OsStr,
    source: &Path,
    _container: &File,
    destination: &Path,
) -> CargoResult<()> {
    fs::rename(source, destination)?;
    Ok(())
}

#[cfg(unix)]
fn create_directory_at(parent: &File, name: &OsStr, _path: &Path) -> CargoResult<()> {
    use std::os::fd::AsRawFd as _;
    let name = name_cstr(name)?;
    // SAFETY: descriptor and terminated leaf remain live. mkdirat is exclusive.
    if unsafe { libc::mkdirat(parent.as_raw_fd(), name.as_ptr(), 0o755) } != 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    Ok(())
}

#[cfg(not(unix))]
fn create_directory_at(_parent: &File, _name: &OsStr, path: &Path) -> CargoResult<()> {
    fs::create_dir(path)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn old_generation_stays_owned_until_the_dirty_job_completes() {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().join("out");
        fs::create_dir(&root).unwrap();
        fs::write(root.join("generated"), b"poison").unwrap();
        let retired = reset(&root).unwrap();
        let quarantine = retired.quarantine.as_ref().unwrap().path().to_owned();
        assert_eq!(
            fs::read(quarantine.join("previous/generated")).unwrap(),
            b"poison"
        );
        assert_eq!(fs::read_dir(&root).unwrap().count(), 0);
        fs::write(root.join("generated"), b"regenerated").unwrap();
        drop(retired);
        assert_eq!(
            fs::read(quarantine.join("previous/generated")).unwrap(),
            b"poison"
        );
        assert_eq!(fs::read(root.join("generated")).unwrap(), b"regenerated");
    }

    #[test]
    fn empty_retired_directories_are_removed_without_recursive_cleanup() {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().join("out");
        fs::create_dir(&root).unwrap();
        let retired = reset(&root).unwrap();
        let quarantine = retired.quarantine.as_ref().unwrap().path().to_owned();
        drop(retired);
        assert!(!quarantine.exists());
        assert!(root.is_dir());
    }

    #[test]
    fn missing_generation_is_created_exclusively() {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().join("out");
        let retired = reset(&root).unwrap();
        assert!(metadata_is_plain_directory(
            &fs::symlink_metadata(&root).unwrap()
        ));
        assert!(retired.original.is_none());
    }

    #[test]
    fn replaced_quarantine_entry_is_preserved_instead_of_cleaned() {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().join("out");
        fs::create_dir(&root).unwrap();
        let retired = reset(&root).unwrap();
        let quarantine = retired.quarantine.as_ref().unwrap().path().to_owned();
        fs::rename(quarantine.join(PREVIOUS), quarantine.join("original")).unwrap();
        fs::create_dir(quarantine.join(PREVIOUS)).unwrap();
        fs::write(quarantine.join("previous/foreign"), b"preserve").unwrap();
        assert!(retired.validate().is_err());
        drop(retired);
        assert_eq!(
            fs::read(quarantine.join("previous/foreign")).unwrap(),
            b"preserve"
        );
        assert!(quarantine.join("original").is_dir());
    }

    #[test]
    fn failed_exclusive_fresh_creation_preserves_the_retired_generation() {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().join("out");
        fs::create_dir(&root).unwrap();
        fs::write(root.join("generated"), b"original").unwrap();
        CONFLICT_AT_CREATE.with(|conflict| conflict.set(true));
        assert!(reset(&root).is_err());
        assert_eq!(fs::read(root.join("foreign")).unwrap(), b"preserve");
        let quarantines = fs::read_dir(world.path())
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.file_name()
                    .unwrap()
                    .to_string_lossy()
                    .starts_with(".targo-retired-generation-")
            })
            .collect::<Vec<_>>();
        assert_eq!(quarantines.len(), 1);
        assert_eq!(
            fs::read(quarantines[0].join("previous/generated")).unwrap(),
            b"original"
        );
    }

    #[cfg(unix)]
    #[test]
    fn symlink_generation_is_moved_without_following_its_victim() {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().join("out");
        let victim = world.path().join("victim");
        fs::create_dir(&victim).unwrap();
        fs::write(victim.join("value"), b"untouched").unwrap();
        std::os::unix::fs::symlink(&victim, &root).unwrap();
        let retired = reset(&root).unwrap();
        assert_eq!(fs::read_dir(&root).unwrap().count(), 0);
        drop(retired);
        assert_eq!(fs::read(victim.join("value")).unwrap(), b"untouched");
    }
}
