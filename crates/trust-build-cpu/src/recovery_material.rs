// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Private recovery material. This module neither establishes work closure nor
//! settles CPU debt. Reopening a file never recreates a prepared capability.

use std::ffi::CString;
use std::fs::{File, OpenOptions};
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
use std::io::Read;
use std::io::{self, Write};
use std::num::NonZeroU32;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::{FileExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::Owner;

const MAGIC: &[u8; 8] = b"TRRM\0\0\0\x01";
const MAX_WIDTH: u32 = 65_536;
const HEADER: usize = 89; // magic, domain, pid, birth-present, birth, width, context
const MAX_BYTES: usize = HEADER + MAX_WIDTH as usize * 48 + 32;

pub(crate) struct RecoveryUnit {
    pub(crate) nonce: [u8; 16],
    pub(crate) secret: [u8; 32],
}

/// Fresh private material; deliberately neither cloneable nor printable.
pub struct RecoveryMaterial {
    domain: [u8; 32],
    owner: Owner,
    width: NonZeroU32,
    context: [u8; 32],
    units: Vec<RecoveryUnit>,
}

/// A newly persisted issuance capability, tied to the original locked inode.
pub struct PreparedRecovery {
    material: RecoveryMaterial,
    backing: Backing,
    taken: bool,
    nonces: Vec<[u8; 16]>,
}

/// Original material restored for host-side authentication, never issuance.
pub struct RecoveryAuthority {
    material: RecoveryMaterial,
    _backing: Backing,
}

struct Backing {
    parent_path: PathBuf,
    leaf: String,
    parent: File,
    file: File,
    digest: [u8; 32],
}

fn invalid() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "invalid or changed recovery material")
}

impl RecoveryMaterial {
    pub(crate) fn mint(
        domain: [u8; 32],
        owner: Owner,
        width: NonZeroU32,
        context: [u8; 32],
    ) -> io::Result<Self> {
        if width.get() > MAX_WIDTH || owner.pid == 0 {
            return Err(invalid());
        }
        let mut units = Vec::with_capacity(width.get() as usize);
        let mut nonces = std::collections::BTreeSet::new();
        for _ in 0..width.get() {
            let mut bytes = [0; 48];
            entropy(&mut bytes)?;
            let nonce = bytes[..16].try_into().map_err(|_| invalid())?;
            if !nonces.insert(nonce) {
                return Err(invalid());
            }
            units.push(RecoveryUnit {
                nonce,
                secret: bytes[16..].try_into().map_err(|_| invalid())?,
            });
        }
        Ok(Self { domain, owner, width, context, units })
    }

    /// Exclusively create durable material in an existing canonical private
    /// directory. Errors leave conservative artifacts; no repair or overwrite.
    pub fn persist(self, parent: &Path, leaf: &str) -> io::Result<PreparedRecovery> {
        check_leaf(leaf)?;
        let directory = open_parent(parent)?;
        let file = open_at(&directory, leaf, true)?;
        check_private(&file, false)?; // Includes inherited ACL, BEFORE secrets.
        // Write, sync and validation errors leave through the lock's unlock.
        let mut file = Locked::lock(file)?;
        let bytes = self.encode();
        let digest = hash(&bytes);
        file.file().write_all(&bytes)?;
        file.file().sync_all()?;
        directory.sync_all()?;
        let backing = Backing::keep(parent, leaf, directory, file, digest)?;
        let nonces = self.units.iter().map(|unit| unit.nonce).collect();
        Ok(PreparedRecovery { material: self, backing, taken: false, nonces })
    }

    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(HEADER + self.units.len() * 48 + 32);
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(&self.domain);
        bytes.extend_from_slice(&self.owner.pid.to_be_bytes());
        bytes.push(u8::from(self.owner.birth.is_some()));
        bytes.extend_from_slice(&self.owner.birth.unwrap_or(0).to_be_bytes());
        bytes.extend_from_slice(&self.width.get().to_be_bytes());
        bytes.extend_from_slice(&self.context);
        for unit in &self.units {
            bytes.extend_from_slice(&unit.nonce);
            bytes.extend_from_slice(&unit.secret);
        }
        let checksum = hash(&bytes);
        bytes.extend_from_slice(&checksum);
        bytes
    }

    fn parse(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() < HEADER + 32 || bytes.len() > MAX_BYTES || &bytes[..8] != MAGIC {
            return Err(invalid());
        }
        let domain = bytes[8..40].try_into().map_err(|_| invalid())?;
        let pid = u32::from_be_bytes(bytes[40..44].try_into().map_err(|_| invalid())?);
        let birth_value = u64::from_be_bytes(bytes[45..53].try_into().map_err(|_| invalid())?);
        let birth = match bytes[44] {
            0 if birth_value == 0 => None,
            1 => Some(birth_value),
            _ => return Err(invalid()),
        };
        let width =
            NonZeroU32::new(u32::from_be_bytes(bytes[53..57].try_into().map_err(|_| invalid())?))
                .ok_or_else(invalid)?;
        if pid == 0
            || width.get() > MAX_WIDTH
            || bytes.len() != HEADER + width.get() as usize * 48 + 32
        {
            return Err(invalid());
        }
        let end = bytes.len() - 32;
        if hash(&bytes[..end]).as_slice() != &bytes[end..] {
            return Err(invalid());
        }
        let context = bytes[57..89].try_into().map_err(|_| invalid())?;
        let mut units = Vec::with_capacity(width.get() as usize);
        // The length check above makes this exactly `width` records, no remainder.
        for chunk in bytes[HEADER..end].as_chunks::<48>().0 {
            units.push(RecoveryUnit {
                nonce: chunk[..16].try_into().map_err(|_| invalid())?,
                secret: chunk[16..].try_into().map_err(|_| invalid())?,
            });
        }
        if units.iter().map(|unit| unit.nonce).collect::<std::collections::BTreeSet<_>>().len()
            != units.len()
        {
            return Err(invalid());
        }
        Ok(Self { domain, owner: Owner { pid, birth }, width, context, units })
    }
}

macro_rules! observations {
    () => {
        /// Width of the original material.
        pub fn width(&self) -> NonZeroU32 {
            self.material.width
        }
        /// Reported original owner; not evidence of work closure.
        pub fn owner(&self) -> Owner {
            self.material.owner
        }
        /// Host-supplied context bound into this material.
        pub fn context(&self) -> [u8; 32] {
            self.material.context
        }
        /// Independently validated domain digest supplied by the host at mint.
        pub fn domain(&self) -> [u8; 32] {
            self.material.domain
        }
    };
}

impl PreparedRecovery {
    observations!();
    /// Observe original public nonces, including after one-shot consumption.
    pub fn nonces(&self) -> io::Result<Vec<[u8; 16]>> {
        self.validate(self.material.domain)?;
        Ok(self.nonces.clone())
    }
    pub(crate) fn validate_issuance(&self, domain: [u8; 32]) -> io::Result<()> {
        self.validate(domain)?;
        if self.taken || self.material.units.len() != self.material.width.get() as usize {
            return Err(invalid());
        }
        Ok(())
    }
    pub(crate) fn take_units(&mut self) -> io::Result<Vec<RecoveryUnit>> {
        self.validate(self.material.domain)?;
        if self.taken {
            return Err(invalid());
        }
        self.taken = true;
        Ok(std::mem::take(&mut self.material.units))
    }
    pub(crate) fn validate(&self, expected_domain: [u8; 32]) -> io::Result<()> {
        if self.material.domain != expected_domain {
            return Err(invalid());
        }
        self.backing.validate()
    }
}

impl RecoveryAuthority {
    observations!();
    pub(crate) fn open(parent: &Path, leaf: &str) -> io::Result<Self> {
        check_leaf(leaf)?;
        let directory = open_parent(parent)?;
        let file = open_at(&directory, leaf, false)?;
        check_private(&file, false)?;
        // Read, parse and validation errors leave through the lock's unlock.
        let mut file = Locked::lock(file)?;
        let bytes = read_bounded(file.file())?;
        let material = RecoveryMaterial::parse(&bytes)?;
        let backing = Backing::keep(parent, leaf, directory, file, hash(&bytes))?;
        Ok(Self { material, _backing: backing })
    }
    pub(crate) fn units(&self) -> &[RecoveryUnit] {
        &self.material.units
    }
}

/// Authentication only: no child holds this lock on purpose, and one released
/// only by the final close would keep refused or ended material reading as
/// live custody for as long as any concurrent spawn's descriptor copy lives.
impl Drop for RecoveryAuthority {
    fn drop(&mut self) {
        // A failed unlock leaves the release to the final close.
        let _ = self._backing.file.unlock();
    }
}

impl Backing {
    /// Keep newly locked material once it validates. Until then `file` is
    /// still a `Locked`, so a refusal unlocks it.
    fn keep(
        parent_path: &Path,
        leaf: &str,
        parent: File,
        mut file: Locked,
        digest: [u8; 32],
    ) -> io::Result<Self> {
        validate_backing(parent_path, leaf, &parent, file.file(), &digest)?;
        Ok(Self {
            parent_path: parent_path.to_owned(),
            leaf: leaf.to_owned(),
            parent,
            file: file.into_file(),
            digest,
        })
    }

    fn validate(&self) -> io::Result<()> {
        validate_backing(&self.parent_path, &self.leaf, &self.parent, &self.file, &self.digest)
    }
}

fn validate_backing(
    parent_path: &Path,
    leaf: &str,
    parent: &File,
    file: &File,
    digest: &[u8; 32],
) -> io::Result<()> {
    let current_parent = open_parent(parent_path)?;
    check_private(parent, true)?;
    check_private(file, false)?;
    let current = open_at(&current_parent, leaf, false)?;
    check_private(&current, false)?;
    if identity(&current_parent)? != identity(parent)? || identity(&current)? != identity(file)? {
        return Err(invalid());
    }
    if hash(&read_bounded(file)?) != *digest {
        return Err(invalid());
    }
    Ok(())
}

/// Material's file from its lock until a validated capability keeps it.
/// Every error in between unlocks it before close: any concurrent spawn,
/// posix_spawn as well as fork, holds a copy of every descriptor until its
/// exec, and a lock released only by the final close stays held that long,
/// so material that failed to persist or to open would read as live custody.
/// Only `into_file` hands the locked file on: a `PreparedRecovery` releases it
/// by close, and a `RecoveryAuthority` unlocks it on drop.
struct Locked(Option<File>);

impl Locked {
    fn lock(file: File) -> io::Result<Self> {
        file.try_lock().map_err(|e| match e {
            std::fs::TryLockError::WouldBlock => io::Error::from(io::ErrorKind::WouldBlock),
            std::fs::TryLockError::Error(e) => e,
        })?;
        let locked = Self(Some(file));
        // Tests copy the locked file here, as a concurrent spawn can, before
        // anything else can fail: every error after this point must unlock.
        #[cfg(test)]
        if let Some(hook) = AFTER_LOCK.get() {
            hook();
        }
        Ok(locked)
    }

    fn file(&mut self) -> &mut File {
        self.0.as_mut().expect("only into_file takes the locked file, consuming the guard")
    }

    fn into_file(mut self) -> File {
        self.0.take().expect("only into_file takes the locked file, consuming the guard")
    }
}

impl Drop for Locked {
    fn drop(&mut self) {
        if let Some(file) = &self.0 {
            // A failed unlock leaves the release to the final close.
            let _ = file.unlock();
        }
    }
}

#[cfg(test)]
thread_local! {
    /// Called on this thread right after each new lock is taken. The
    /// recovery_material test binary copies the descriptor table here.
    pub(crate) static AFTER_LOCK: std::cell::Cell<Option<fn()>> =
        const { std::cell::Cell::new(None) };
}

/// A commitment is not a grant and does not establish closure or settle debt.
pub(crate) fn commitment(
    domain: &[u8; 32],
    owner: Owner,
    width: NonZeroU32,
    context: &[u8; 32],
    unit: &RecoveryUnit,
    slot: u32,
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"trust-build-cpu/recovery-commitment/v1\0");
    h.update(domain);
    h.update(owner.pid.to_be_bytes());
    h.update([u8::from(owner.birth.is_some())]);
    h.update(owner.birth.unwrap_or(0).to_be_bytes());
    h.update(width.get().to_be_bytes());
    h.update(context);
    h.update(unit.nonce);
    h.update(slot.to_be_bytes());
    h.update(unit.secret);
    h.finalize().into()
}

fn hash(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
fn identity(file: &File) -> io::Result<(u64, u64)> {
    let m = file.metadata()?;
    Ok((m.dev(), m.ino()))
}
fn check_leaf(leaf: &str) -> io::Result<()> {
    if leaf.is_empty() || leaf == "." || leaf == ".." || leaf.contains('/') || leaf.contains('\0') {
        return Err(invalid());
    }
    Ok(())
}
fn open_parent(path: &Path) -> io::Result<File> {
    if !path.is_absolute() || path.canonicalize()? != path {
        return Err(invalid());
    }
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(path)?;
    check_private(&file, true)?;
    Ok(file)
}
fn open_at(parent: &File, leaf: &str, create: bool) -> io::Result<File> {
    check_leaf(leaf)?;
    let name = CString::new(leaf).map_err(|_| invalid())?;
    let flags = libc::O_NOFOLLOW
        | libc::O_CLOEXEC
        | libc::O_NONBLOCK
        | if create { libc::O_RDWR | libc::O_CREAT | libc::O_EXCL } else { libc::O_RDONLY };
    // SAFETY: live directory fd and validated single, NUL-terminated leaf.
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags, 0o600) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: the new descriptor transfers exactly once into File ownership.
    Ok(unsafe { File::from_raw_fd(fd) })
}
fn check_private(file: &File, directory: bool) -> io::Result<()> {
    let m = file.metadata()?;
    // SAFETY: geteuid has no arguments and only observes the current uid.
    if m.uid() != unsafe { libc::geteuid() }
        || m.mode() & 0o7077 != 0
        || if directory { !m.is_dir() } else { !m.is_file() || m.nlink() != 1 }
    {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "recovery material requires private owned storage",
        ));
    }
    no_acl(file)
}
fn read_bounded(file: &File) -> io::Result<Vec<u8>> {
    let len = file.metadata()?.len();
    if len > MAX_BYTES as u64 {
        return Err(invalid());
    }
    let mut bytes = vec![0; len as usize];
    file.read_exact_at(&mut bytes, 0)?;
    let mut extra = [0];
    if file.read_at(&mut extra, len)? != 0 || file.metadata()?.len() != len {
        return Err(invalid());
    }
    Ok(bytes)
}
fn entropy(bytes: &mut [u8; 48]) -> io::Result<()> {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        // SAFETY: writable live 48-byte buffer, below getentropy's 256-byte limit.
        if unsafe { libc::getentropy(bytes.as_mut_ptr().cast(), bytes.len()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        File::open("/dev/urandom")?.read_exact(bytes)
    }
}

// Reject all extended ACL entries, including inherited entries. Conservative
// refusal avoids interpreting platform-specific allow/deny or inheritance rules.
#[cfg(target_os = "macos")]
fn no_acl(file: &File) -> io::Result<()> {
    unsafe extern "C" {
        fn acl_get_fd_np(fd: libc::c_int, kind: libc::c_int) -> *mut libc::c_void;
        fn acl_get_entry(
            acl: *mut libc::c_void,
            entry: libc::c_int,
            out: *mut *mut libc::c_void,
        ) -> libc::c_int;
        fn acl_free(ptr: *mut libc::c_void) -> libc::c_int;
    }
    // SAFETY: ACL_TYPE_EXTENDED from sys/acl.h, live fd. The owned ACL is
    // queried once and freed on every successful allocation path.
    unsafe {
        let acl = acl_get_fd_np(file.as_raw_fd(), 0x100);
        if acl.is_null() {
            let error = io::Error::last_os_error();
            // Darwin returns ENOENT when this live descriptor has no extended
            // ACL. Other failures cannot establish privacy and refuse.
            return if error.raw_os_error() == Some(libc::ENOENT) { Ok(()) } else { Err(error) };
        }
        let mut entry = std::ptr::null_mut();
        let result = acl_get_entry(acl, 0, &mut entry);
        let error = io::Error::last_os_error();
        acl_free(acl);
        if result == -1 && error.raw_os_error() == Some(libc::EINVAL) {
            Ok(())
        } else {
            Err(invalid())
        }
    }
}
#[cfg(target_os = "linux")]
fn no_acl(file: &File) -> io::Result<()> {
    for name in [c"system.posix_acl_access", c"system.posix_acl_default"] {
        // SAFETY: live fd, constant NUL-terminated name; null/zero queries size.
        let size =
            unsafe { libc::fgetxattr(file.as_raw_fd(), name.as_ptr(), std::ptr::null_mut(), 0) };
        if size >= 0 {
            return Err(invalid());
        }
        let e = io::Error::last_os_error();
        if !matches!(e.raw_os_error(), Some(libc::ENODATA) | Some(libc::ENOTSUP)) {
            return Err(e);
        }
    }
    Ok(())
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn no_acl(_: &File) -> io::Result<()> {
    Err(io::Error::new(io::ErrorKind::Unsupported, "recovery ACL validation unavailable"))
}
