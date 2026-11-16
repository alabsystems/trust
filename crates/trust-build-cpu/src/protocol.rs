// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::ffi::OsStr;
use std::fs::File;
use std::io;
use std::os::fd::FromRawFd;

use crate::invalid;

/// Direct inherited implicit credit. A number alone is never CPU authority;
/// its duplicate must be checked by `Pool::adopt_inherited` before use.
pub const IMPLICIT_FD_ENV: &str = "TRUST_CPU_IMPLICIT_FD";

/// Duplicate, but never take ownership of, an advertised startup descriptor.
pub fn duplicate_descriptor(value: &OsStr) -> io::Result<File> {
    let number = value
        .to_str()
        .and_then(|text| {
            (!text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()))
                .then(|| text.parse::<i32>().ok())
                .flatten()
        })
        .filter(|&number| number >= 3)
        .ok_or_else(|| invalid("invalid resource descriptor"))?;
    // SAFETY: fcntl validates even an arbitrary integer; success returns a new
    // owned CLOEXEC descriptor. The advertised original is never closed here.
    let copy = unsafe { libc::fcntl(number, libc::F_DUPFD_CLOEXEC, 3) };
    if copy < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: the successful duplication returned unique ownership.
    Ok(unsafe { File::from_raw_fd(copy) })
}

/// Duplicate a bounded, nonempty list of inherited fence descriptors.
pub fn duplicate_descriptors(value: &OsStr) -> io::Result<Vec<File>> {
    let text = value.to_str().ok_or_else(|| invalid("resource descriptors are not UTF-8"))?;
    let values: Vec<_> = text.split(',').collect();
    if values.is_empty() || values.len() > 127 {
        return Err(invalid("resource descriptor list is out of bounds"));
    }
    values.into_iter().map(|value| duplicate_descriptor(OsStr::new(value))).collect()
}
