//! No-replace publication of the native authority receipt.

#[cfg(unix)]
use std::ffi::CString;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io::{Read as _, Seek as _, Write as _};
#[cfg(unix)]
use std::os::fd::{AsRawFd as _, FromRawFd as _};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt as _;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;

#[cfg(unix)]
use sha2::{Digest as _, Sha256};

#[cfg(unix)]
use super::super::{CERTIFIED_MONITOR_MAX_IDENTITY_BYTES, same_stage2_file_identity};
#[cfg(unix)]
use super::payload::read_stable_certified_monitor_file;

#[cfg(not(unix))]
pub(in crate::script_cli) fn publish_certified_monitor_native_authority_receipt(
    _path: &Path,
    _bytes: &[u8],
) -> Result<String, String> {
    Err(
        "certified-monitor native authority is unsupported on this host: Unix owner and mode semantics are required"
            .to_string(),
    )
}

#[cfg(unix)]
pub(in crate::script_cli) fn publish_certified_monitor_native_authority_receipt(
    path: &Path,
    bytes: &[u8],
) -> Result<String, String> {
    if bytes.len() as u64 > CERTIFIED_MONITOR_MAX_IDENTITY_BYTES {
        return Err("native authority receipt exceeds its bounded size".to_string());
    }
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .ok_or_else(|| format!("native authority receipt has no parent: {}", path.display()))?;
    let canonical_parent = fs::canonicalize(parent).map_err(|error| {
        format!("cannot canonicalize native authority receipt parent {}: {error}", parent.display())
    })?;
    if canonical_parent != parent {
        return Err(format!(
            "native authority receipt parent contains a non-canonical or symlinked component: requested {}, canonical {}",
            parent.display(),
            canonical_parent.display()
        ));
    }
    if path.parent() != Some(canonical_parent.as_path()) {
        return Err(format!(
            "native authority receipt is not one direct child of {}: {}",
            canonical_parent.display(),
            path.display()
        ));
    }

    let (parent_directory, parent_identity) = open_exact_directory(&canonical_parent)?;
    let mut receipt = create_fresh_receipt_at(&parent_directory, path)?;
    receipt
        .write_all(bytes)
        .map_err(|error| format!("cannot write native authority receipt: {error}"))?;
    receipt
        .sync_all()
        .map_err(|error| format!("cannot sync native authority receipt bytes: {error}"))?;
    let mut permissions = receipt
        .metadata()
        .map_err(|error| format!("cannot inspect native authority receipt: {error}"))?
        .permissions();
    permissions.set_mode(0o400);
    receipt
        .set_permissions(permissions)
        .map_err(|error| format!("cannot seal native authority receipt: {error}"))?;
    receipt
        .sync_all()
        .map_err(|error| format!("cannot synchronize sealed native authority receipt: {error}"))?;
    parent_directory
        .sync_all()
        .map_err(|error| format!("cannot synchronize native authority receipt parent: {error}"))?;

    let held_metadata = receipt
        .metadata()
        .map_err(|error| format!("cannot inspect sealed native authority receipt: {error}"))?;
    require_exact_parent(&canonical_parent, &parent_identity, &parent_directory)?;
    require_held_receipt_path(path, &held_metadata)?;
    receipt.rewind().map_err(|error| format!("cannot rewind native authority receipt: {error}"))?;
    let mut held_bytes = Vec::with_capacity(bytes.len());
    (&mut receipt)
        .take(CERTIFIED_MONITOR_MAX_IDENTITY_BYTES.saturating_add(1))
        .read_to_end(&mut held_bytes)
        .map_err(|error| format!("cannot re-read held native authority receipt: {error}"))?;
    if held_bytes != bytes {
        return Err(
            "held native authority receipt bytes differ from canonical serialization".to_string()
        );
    }

    let (published, digest) = read_stable_certified_monitor_file(
        path,
        "native authority receipt",
        CERTIFIED_MONITOR_MAX_IDENTITY_BYTES,
    )?;
    require_exact_parent(&canonical_parent, &parent_identity, &parent_directory)?;
    require_held_receipt_path(path, &held_metadata)?;
    if published != bytes || format!("{:x}", Sha256::digest(&held_bytes)) != digest {
        return Err(
            "native authority receipt bytes or digest changed after publication".to_string()
        );
    }
    Ok(digest)
}

#[cfg(unix)]
fn open_exact_directory(path: &Path) -> Result<(fs::File, fs::Metadata), String> {
    let before = fs::symlink_metadata(path).map_err(|error| {
        format!("cannot inspect native authority receipt parent {}: {error}", path.display())
    })?;
    if before.file_type().is_symlink() || !before.file_type().is_dir() {
        return Err(format!(
            "native authority receipt parent is not an exact directory: {}",
            path.display()
        ));
    }
    let path = CString::new(path.as_os_str().as_bytes())
        .map_err(|_| "native authority receipt parent contains an interior NUL byte".to_string())?;
    let descriptor = unsafe {
        libc::open(
            path.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
        )
    };
    if descriptor < 0 {
        return Err(format!(
            "cannot open exact native authority receipt parent: {}",
            std::io::Error::last_os_error()
        ));
    }
    let directory = unsafe { fs::File::from_raw_fd(descriptor) };
    let opened = directory.metadata().map_err(|error| {
        format!("cannot inspect opened native authority receipt parent: {error}")
    })?;
    if !opened.file_type().is_dir() || !same_stage2_file_identity(&before, &opened) {
        return Err("native authority receipt parent changed while being opened".to_string());
    }
    Ok((directory, before))
}

#[cfg(unix)]
fn create_fresh_receipt_at(parent: &fs::File, path: &Path) -> Result<fs::File, String> {
    let leaf = path
        .file_name()
        .ok_or_else(|| format!("native authority receipt has no leaf name: {}", path.display()))?;
    let leaf = CString::new(leaf.as_bytes())
        .map_err(|_| "native authority receipt leaf contains an interior NUL byte".to_string())?;
    let descriptor = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            leaf.as_ptr(),
            libc::O_RDWR | libc::O_CREAT | libc::O_EXCL | libc::O_CLOEXEC | libc::O_NOFOLLOW,
            0o600,
        )
    };
    if descriptor < 0 {
        return Err(format!(
            "native authority receipt must be a fresh no-replace leaf {}: {}",
            path.display(),
            std::io::Error::last_os_error()
        ));
    }
    Ok(unsafe { fs::File::from_raw_fd(descriptor) })
}

#[cfg(unix)]
fn require_exact_parent(path: &Path, before: &fs::Metadata, held: &fs::File) -> Result<(), String> {
    let held = held
        .metadata()
        .map_err(|error| format!("cannot re-inspect held receipt parent: {error}"))?;
    let after = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot re-inspect receipt parent {}: {error}", path.display()))?;
    if after.file_type().is_symlink()
        || !after.file_type().is_dir()
        || !same_stage2_file_identity(before, &held)
        || !same_stage2_file_identity(before, &after)
    {
        return Err("native authority receipt parent changed during publication".to_string());
    }
    Ok(())
}

#[cfg(unix)]
fn require_held_receipt_path(path: &Path, held: &fs::Metadata) -> Result<(), String> {
    use std::os::unix::fs::MetadataExt as _;

    let observed = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect published native authority receipt: {error}"))?;
    if observed.file_type().is_symlink()
        || !observed.file_type().is_file()
        || observed.nlink() != 1
        || !same_stage2_file_identity(held, &observed)
    {
        return Err(
            "published native authority receipt path no longer names the held unaliased no-replace file"
                .to_string(),
        );
    }
    Ok(())
}
