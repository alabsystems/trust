//! Trust: keep the build directory out of Time Machine (EW-18, 2026-11-05).
//!
//! A build directory holds hundreds of GiB that the next `x.py` run regenerates:
//! LLVM, the sysroots, the seed and every cargo target tree. Cargo already marks each
//! target directory it creates (`stage1-rustc`, `stage2-tools`, ...) as excluded from
//! backups, through `NSURLIsExcludedFromBackupKey`. Nothing marked the rest. Measured
//! 2026-11-05 on m8: `tmutil isexcluded` reported the main checkout's `build/`, its
//! `llvm/`, `stage0/`, `stage1/`, `stage2/` and `stage1-std/` all `[Included]`.
//!
//! [`exclude_from_backups`] marks the whole directory the way `tmutil addexclusion`
//! does without `-p`: the sticky exclusion, an extended attribute on the directory that
//! needs no privilege and moves with it. Time Machine skips everything under a marked
//! directory. Under the Spotlight layout (`build` is a link to the real `build.noindex`,
//! docs/BUILD_AND_INSTALL.md "Keeping Spotlight out of `build/`") the attribute lands
//! on the real directory, because `setxattr(2)` follows a link unless told not to.
//!
//! Only a volume Time Machine backs up is marked: APFS or HFS+. Elsewhere there is
//! nothing to keep out of a backup, and FAT and exFAT would store the attribute as an
//! AppleDouble `._build` file beside the directory, which `git status` then shows
//! (hostile review of EW-18, 2026-11-05).
//!
//! Bootstrap marks the directory on every run that is not a dry run (`cli_main.rs`), so
//! a tree created before this file existed is marked by its next `x.py` command, and a
//! marked tree costs one `statfs(2)` and one `getxattr(2)`. A failure is reported and the build goes on: the
//! mark keeps backups small, it decides nothing about what is built. Off macOS there is
//! no Time Machine, and nothing here is compiled but a call that does nothing.

#[cfg(target_os = "macos")]
use std::io;
use std::path::Path;

/// The attribute Time Machine reads for a sticky exclusion.
#[cfg(target_os = "macos")]
pub(crate) const BACKUP_EXCLUDE_XATTR: &str = "com.apple.metadata:com_apple_backup_excludeItem";

/// The attribute's value: the binary property list of the string `com.apple.backupd`.
/// `tmutil addexclusion` and Core Foundation's `NSURLIsExcludedFromBackupKey` (which is
/// how cargo marks its target directories) write these same 61 bytes, measured on macOS
/// 27 on 2026-11-05.
#[cfg(any(target_os = "macos", test))]
pub(crate) const BACKUP_EXCLUDE_VALUE: &[u8] = b"bplist00_\x10\x11com.apple.backupd\x08\
\x00\x00\x00\x00\x00\x00\x01\x01\x00\x00\x00\x00\x00\x00\x00\x01\
\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1c";

/// What [`exclude_from_backups`] found or did.
#[cfg(target_os = "macos")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BackupExclusion {
    /// The directory already carried the exclusion.
    AlreadyExcluded,
    /// The directory carries it now.
    Excluded,
    /// The directory is on a volume Time Machine does not back up; nothing was written.
    NotOnABackedUpVolume,
}

/// Whether Time Machine backs up a volume of this file-system type (`f_fstypename`)
/// and the type keeps an extended attribute in the directory itself: APFS and HFS+.
/// `msdos` and `exfat` keep one as an AppleDouble `._<name>` file in the parent, and
/// network volumes are not backed up.
#[cfg(any(target_os = "macos", test))]
pub(crate) fn time_machine_backs_up(fstypename: &[u8]) -> bool {
    matches!(fstypename, b"apfs" | b"hfs")
}

/// Mark `dir` (and so everything under it) as excluded from Time Machine backups.
#[cfg(target_os = "macos")]
pub(crate) fn exclude_from_backups(dir: &Path) -> io::Result<BackupExclusion> {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    if !dir.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::NotADirectory,
            format!("{} is not a directory", dir.display()),
        ));
    }
    let path = CString::new(dir.as_os_str().as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path holds a NUL byte"))?;
    let name = CString::new(BACKUP_EXCLUDE_XATTR).expect("no NUL in a constant");

    // SAFETY: an all-zero `statfs` is a valid value of a plain C struct.
    let mut volume: libc::statfs = unsafe { std::mem::zeroed() };
    // SAFETY: `path` is NUL-terminated and `volume` is valid for writes. `statfs`
    // follows a link, as `getxattr` and `setxattr` below do.
    if unsafe { libc::statfs(path.as_ptr(), &mut volume) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let fstypename: Vec<u8> =
        volume.f_fstypename.iter().take_while(|c| **c != 0).map(|c| *c as u8).collect();
    if !time_machine_backs_up(&fstypename) {
        return Ok(BackupExclusion::NotOnABackedUpVolume);
    }

    let mut current = [0u8; 128];
    // SAFETY: both strings are NUL-terminated and outlive the call; the buffer is valid
    // for `current.len()` bytes. Options 0 follow a symlink, as `setxattr` below does.
    let read = unsafe {
        libc::getxattr(
            path.as_ptr(),
            name.as_ptr(),
            current.as_mut_ptr().cast(),
            current.len(),
            0,
            0,
        )
    };
    if read >= 0 && current.get(..read as usize) == Some(BACKUP_EXCLUDE_VALUE) {
        return Ok(BackupExclusion::AlreadyExcluded);
    }
    // SAFETY: as above; the value is valid for its length.
    let set = unsafe {
        libc::setxattr(
            path.as_ptr(),
            name.as_ptr(),
            BACKUP_EXCLUDE_VALUE.as_ptr().cast(),
            BACKUP_EXCLUDE_VALUE.len(),
            0,
            0,
        )
    };
    if set != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(BackupExclusion::Excluded)
}

/// Bootstrap's call: mark the build directory, and say so when that fails. Off macOS
/// there is no Time Machine, so there is nothing to do.
pub(crate) fn exclude_build_dir_from_backups(out: &Path) {
    #[cfg(target_os = "macos")]
    if let Err(error) = exclude_from_backups(out) {
        eprintln!(
            "WARNING: could not exclude {} from Time Machine backups ({error}); \
             `tmutil addexclusion {}` does the same by hand",
            out.display(),
            out.display(),
        );
    }
    #[cfg(not(target_os = "macos"))]
    let _ = out;
}

#[cfg(test)]
mod tests;
