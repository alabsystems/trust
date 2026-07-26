//! Hardened OS wrappers for Trust.
//!
//! This crate starts with a small dirfd-relative filesystem surface. Callers
//! anchor operations in a [`DirFd`], then pass relative names to avoid ambient
//! current-directory lookups and accidental path traversal.
//!
//! ```
//! # #[cfg(unix)]
//! # {
//! use std::io::{Read, Write};
//! use trust_os::{DirFd, UnixMode};
//!
//! let tmp = tempfile::tempdir()?;
//! let dir = DirFd::open(tmp.path())?;
//! let mut file = dir.create_file("result.txt", UnixMode::OWNER_READ_WRITE)?;
//! file.write_all(b"ok")?;
//!
//! let identity = dir.identity("result.txt")?;
//! assert!(identity.device() > 0);
//!
//! let mut reopened = dir.open_file("result.txt")?;
//! let mut contents = String::new();
//! reopened.read_to_string(&mut contents)?;
//! assert_eq!(contents, "ok");
//! # std::io::Result::Ok(())
//! # }
//! # #[cfg(not(unix))]
//! # std::io::Result::Ok(())
//! ```

#![deny(unsafe_op_in_unsafe_fn)]

mod mode;
// Deadline-bounded child processes: the shared spawn/wait/kill-the-group core
// every solver backend needs, so a timeout is a real bound rather than three
// slightly different approximations of one.
pub mod process;

#[cfg(unix)]
mod unix;
#[cfg(not(any(unix, windows)))]
mod unsupported;
#[cfg(windows)]
mod windows;

pub use mode::UnixMode;
pub use process::{BoundedWait, kill_process_group, spawn_in_own_process_group, wait_bounded};

#[cfg(unix)]
pub use unix::{
    DirFd, FileIdentity, create_file_at, identity_at, metadata_at, open_file_at,
    open_file_read_write_at, read_dir_names_at, remove_file_at, rename_file_at,
};
#[cfg(not(any(unix, windows)))]
pub use unsupported::{
    DirFd, FileIdentity, create_file_at, identity_at, metadata_at, open_file_at,
    open_file_read_write_at, remove_file_at, rename_file_at,
};
#[cfg(windows)]
pub use windows::{
    DirFd, FileIdentity, create_file_at, identity_at, metadata_at, open_file_at,
    open_file_read_write_at, remove_file_at, rename_file_at,
};
