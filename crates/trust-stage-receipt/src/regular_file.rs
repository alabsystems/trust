// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::path::Path;

use crate::{Refusal, Result};

/// Read a required regular file under a byte bound, without following its leaf.
///
/// Unix admission uses nonblocking, no-follow handles and compares descriptor
/// and pathname metadata before/after bounded reading. Parent namespaces must
/// be trusted. This sequential observation is not an immutable filesystem
/// snapshot or protection against changes restored between observations.
/// Other platforms explicitly refuse this strict contract. Receipt absence and
/// compatibility-alias semantics are separate and unchanged.
pub fn read_required_regular_file(path: &Path, max_bytes: u64) -> Result<Vec<u8>> {
    #[cfg(unix)]
    return read_with_hook(path, max_bytes, |_| {});
    #[cfg(not(unix))]
    {
        let _ = (path, max_bytes);
        Err(Refusal("strict required-file intake needs Unix no-follow handles".into()))
    }
}

#[cfg(unix)]
#[derive(Clone, Copy, Eq, PartialEq)]
enum ReadPoint {
    BeforeOpen,
    AfterOpen,
    AfterChunk,
    BeforeFinalCheck,
}

#[cfg(unix)]
fn read_with_hook(path: &Path, max_bytes: u64, mut hook: impl FnMut(ReadPoint)) -> Result<Vec<u8>> {
    use std::fs::{self, OpenOptions};
    use std::io::{ErrorKind, Read as _};
    use std::os::unix::fs::OpenOptionsExt as _;

    use crate::files::stamp;

    let refusal = |reason: &str| Refusal(format!("required regular file: {reason}"));
    let lookahead = max_bytes.checked_add(1).ok_or_else(|| refusal("byte bound overflows"))?;
    let before = fs::symlink_metadata(path)?;
    if !before.is_file() {
        return Err(refusal("leaf is not a regular file"));
    }
    if before.len() > max_bytes {
        return Err(refusal("initial length exceeds its byte bound"));
    }
    let expected = usize::try_from(before.len())
        .map_err(|_| refusal("initial length exceeds this platform's address range"))?;
    let read_ceiling = before
        .len()
        .checked_add(1)
        .ok_or_else(|| refusal("initial length lookahead overflows"))?
        .min(lookahead);
    hook(ReadPoint::BeforeOpen);
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)?;
    let opened = file.metadata()?;
    if !opened.is_file() || stamp(&before) != stamp(&opened) {
        return Err(refusal("leaf changed before it could be opened"));
    }
    hook(ReadPoint::AfterOpen);
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(expected)
        .map_err(|_| refusal("initial length cannot be reserved in memory"))?;
    let mut limited = file.by_ref().take(read_ceiling);
    let mut buffer = [0u8; 8192];
    loop {
        let count = match limited.read(&mut buffer) {
            Ok(0) => break,
            Ok(count) => count,
            Err(error) if error.kind() == ErrorKind::Interrupted => continue,
            Err(error) => return Err(error.into()),
        };
        let next =
            bytes.len().checked_add(count).ok_or_else(|| refusal("observed length overflows"))?;
        if next > expected {
            return Err(refusal("file grew while reading"));
        }
        // The admitted capacity was reserved fallibly once, before any reads.
        bytes.extend_from_slice(&buffer[..count]);
        hook(ReadPoint::AfterChunk);
    }
    if bytes.len() != expected {
        return Err(refusal("file shortened while reading"));
    }
    hook(ReadPoint::BeforeFinalCheck);
    if stamp(&before) != stamp(&file.metadata()?)
        || stamp(&before) != stamp(&fs::symlink_metadata(path)?)
    {
        return Err(refusal("file changed while reading"));
    }
    Ok(bytes)
}

#[cfg(all(test, unix))]
mod tests;
