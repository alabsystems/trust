// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Native code-requirement checks against an actual connected peer.
//!
//! A requirement is selected by the caller. Passing it authenticates no Host
//! role, approved resource cohort, SDK, footprint policy or allocation. In
//! particular, a caller-selected `true` requirement is not installation trust.
//! The caller retains its original channel and lifetime checks around exchanges.
//! These calls may wait on Security.framework; an asynchronous owner must keep
//! the pending work and enforce its original deadline without extending it.

use std::fmt;
use std::os::fd::BorrowedFd;
use std::path::Path;

#[cfg(target_os = "macos")]
mod darwin;

/// A definite code refusal is distinct from an operational or unknown result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Refused(String),
    Unchecked(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refused(why) | Self::Unchecked(why) => f.write_str(why),
        }
    }
}
impl std::error::Error for Error {}

#[cfg(not(target_os = "macos"))]
fn unsupported() -> Error {
    Error::Unchecked("native code requirements are supported on macOS only".into())
}

/// A compiled native requirement, not a resource or publisher approval.
#[derive(Debug)]
pub struct Requirement {
    #[cfg(target_os = "macos")]
    native: darwin::Owned,
}

// SAFETY: Only immutable SecRequirement objects escape through Requirement;
// CoreFoundation retain/release and requirement checks are thread-safe.
#[cfg(target_os = "macos")]
unsafe impl Send for Requirement {}
// SAFETY: The requirement is immutable and is only checked after construction.
#[cfg(target_os = "macos")]
unsafe impl Sync for Requirement {}

/// Static validation strength; neither variant authenticates a running peer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StaticValidation {
    Current,
    Strict,
}

impl Requirement {
    /// Compile caller-selected requirement text and return its canonical spelling.
    pub fn compile(text: &str) -> Result<(Self, String), Error> {
        #[cfg(target_os = "macos")]
        {
            let (native, text) = darwin::requirement_from_text(text).map_err(Error::Unchecked)?;
            Ok((Self { native }, text))
        }
        #[cfg(not(target_os = "macos"))]
        {
            let _ = text;
            Err(unsupported())
        }
    }

    /// This image's designated requirement, which is not independent approval.
    pub fn current() -> Result<(Self, String), Error> {
        #[cfg(target_os = "macos")]
        {
            let (native, text) = darwin::own_designated_requirement().map_err(Error::Unchecked)?;
            Ok((Self { native }, text))
        }
        #[cfg(not(target_os = "macos"))]
        Err(unsupported())
    }

    /// The designated requirement of the image at a caller-selected path.
    pub fn at_path(path: &Path) -> Result<(Self, String), Error> {
        #[cfg(target_os = "macos")]
        {
            let (native, text) =
                darwin::designated_requirement_at(path).map_err(Error::Unchecked)?;
            Ok((Self { native }, text))
        }
        #[cfg(not(target_os = "macos"))]
        {
            let _ = path;
            Err(unsupported())
        }
    }

    /// Check a disk image; no path observation is promoted to peer identity.
    pub fn check_static(&self, path: &Path, strength: StaticValidation) -> Result<(), Error> {
        #[cfg(target_os = "macos")]
        {
            let flags = match strength {
                StaticValidation::Current => 0,
                StaticValidation::Strict => darwin::STRICT,
            };
            darwin::check_static_with(path, &self.native, flags)
        }
        #[cfg(not(target_os = "macos"))]
        {
            let _ = (path, strength);
            Err(unsupported())
        }
    }
}

/// Kernel-captured Darwin peer credentials. No raw-token constructor exists.
/// It retains no socket, process owner, resource claim or GC lease.
#[derive(Debug)]
pub struct CapturedPeer {
    token: [u32; 8],
}

impl CapturedPeer {
    /// Capture a connected socket's kernel credentials, never protocol data.
    /// The borrowed descriptor stays live; peer liveness remains unproven.
    pub fn capture(socket: BorrowedFd<'_>) -> Result<Self, Error> {
        #[cfg(target_os = "macos")]
        {
            use std::os::fd::AsRawFd;
            let mut token = [0_u32; 8];
            let mut length = std::mem::size_of_val(&token) as libc::socklen_t;
            // SAFETY: The borrowed descriptor remains live and both output
            // buffers are initialized and writable for the exact stated size.
            let rc = unsafe {
                libc::getsockopt(socket.as_raw_fd(), 0, 6, token.as_mut_ptr().cast(), &mut length)
            };
            if rc != 0 {
                return Err(Error::Unchecked(std::io::Error::last_os_error().to_string()));
            }
            if length as usize != std::mem::size_of_val(&token) || token[5] == 0 {
                return Err(Error::Unchecked("native peer audit token unavailable".into()));
            }
            Ok(Self { token })
        }
        #[cfg(not(target_os = "macos"))]
        {
            let _ = socket;
            Err(unsupported())
        }
    }

    pub fn pid(&self) -> u32 {
        self.token[5]
    }
    pub fn uid(&self) -> u32 {
        self.token[1]
    }
    pub fn exec_version(&self) -> u32 {
        self.token[7]
    }

    /// Compare an earlier observation; it cannot construct a captured peer.
    pub fn matches_native_token(&self, bytes: &[u8; 32]) -> bool {
        self.token
            .iter()
            .zip(bytes.chunks_exact(4))
            .all(|(word, part)| word.to_ne_bytes().as_slice() == part)
    }

    /// Check the actual captured guest, with no PID lookup or helper process.
    pub fn check(&self, requirement: &Requirement) -> Result<(), Error> {
        #[cfg(target_os = "macos")]
        {
            darwin::check_guest(&self.token, &requirement.native)
        }
        #[cfg(not(target_os = "macos"))]
        {
            let _ = requirement;
            Err(unsupported())
        }
    }
}

/// This process's signing team, not a trusted publisher policy.
pub fn own_team() -> Result<Option<String>, Error> {
    #[cfg(target_os = "macos")]
    {
        darwin::own_team().map_err(Error::Unchecked)
    }
    #[cfg(not(target_os = "macos"))]
    {
        Ok(None)
    }
}

/// This process's signing identifier, not an approved resource cohort.
pub fn own_identifier() -> Result<Option<String>, Error> {
    #[cfg(target_os = "macos")]
    {
        darwin::own_identifier().map_err(Error::Unchecked)
    }
    #[cfg(not(target_os = "macos"))]
    {
        Ok(None)
    }
}

#[cfg(all(test, target_os = "macos"))]
#[path = "signing/tests.rs"]
mod tests;
