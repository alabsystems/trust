// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original directory custody before a genuine cache-lock acquisition. The
//! directory, its name and this carrier never construct a cache, Seed or SDK.
use super::*;
use std::{os::unix::ffi::OsStrExt as _, path::Path};

pub const PREPARATION_CACHE_DIRECTORY_RIGHTS_MARKER: u8 = 0x7c;

/// Actual unclassified kernel descriptions, including malformed deliveries.
/// Reuse the same conservative unconsumed-drop custody as early output; only
/// the fixed receiver below creates this distinct carrier role.
#[must_use = "retain actual received descriptions until the native State takes custody"]
pub struct PreparationCacheDirectoryDelivery {
    actual: PreparationOutputDelivery,
}
impl PreparationCacheDirectoryDelivery {
    pub(crate) fn received(descriptions: Vec<OwnedFd>, valid: bool) -> Self {
        Self {
            actual: PreparationOutputDelivery::received(descriptions, valid),
        }
    }

    /// Move the same descriptions directly into State before interpreting
    /// validity. This returns carrier DATA only, never a cache-lock owner.
    pub fn into_parts(self, retained: &mut Vec<OwnedFd>) -> bool {
        self.actual.into_parts(retained)
    }
}

pub fn receive_preparation_cache_directory(
    channel: &mut Channel,
    deadline: Instant,
) -> io::Result<PreparationCacheDirectoryDelivery> {
    channel.receive_preparation_cache_directory(deadline)
}

/// Send the actual context-selected directory while retaining its original
/// description. Native State must independently acquire the maintained cache
/// guard relative to this SAME directory. Equality checks create no owner.
pub fn send_preparation_cache_directory(
    channel: &mut Channel,
    home: &Path,
    original: BorrowedFd<'_>,
    deadline: Instant,
    revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let mut revalidate = revalidate;
    let checked = (|| {
        time(deadline)?;
        check_directory(home, original)?;
        revalidate()?;
        time(deadline)?;
        channel.send_bootstrap_descriptions(
            &[original],
            PREPARATION_CACHE_DIRECTORY_RIGHTS_MARKER,
            deadline,
        )?;
        check_directory(home, original)?;
        revalidate()?;
        time(deadline)
    })();
    if checked.is_err() {
        channel.poison();
    }
    checked
}

fn check_directory(home: &Path, original: BorrowedFd<'_>) -> io::Result<()> {
    let (identity, mode, flags) = inspect(original)?;
    if !home.is_absolute()
        || home.as_os_str().as_bytes().contains(&0)
        || mode & libc::S_IFMT != libc::S_IFDIR
        || flags & libc::O_ACCMODE != libc::O_RDONLY
    {
        return Err(crate::wire::invalid());
    }
    let named = std::fs::symlink_metadata(home)?;
    use std::os::unix::fs::MetadataExt as _;
    if !named.is_dir()
        || home.canonicalize()? != home
        || (named.dev(), named.ino()) != (identity.device, identity.inode)
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}

#[cfg(test)]
#[path = "preparation_cache/tests.rs"]
mod tests;
