//! Held cgroup2 descriptor and bounded control IO; no process lookup.
use std::ffi::CStr;
use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::{FileExt, MetadataExt};

use trust_process_isolation::{Budget, Charge};

use super::{checked, contract, original_endpoint, scalar};
use crate::{Error, system};

#[derive(Clone, Copy)]
pub(in crate::launcher) enum Role {
    Directory,
    Control,
}
#[derive(Clone, Copy)]
pub(in crate::launcher) enum Access {
    Read,
    Write,
}

const CGROUP2: u64 = 0x6367_7270;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::launcher) struct Identity {
    device: u64,
    inode: u64,
    mode: u32,
    owner: u32,
    group: u32,
}
impl Identity {
    pub(in crate::launcher) fn capture(file: &File, role: Role) -> Result<Self, Error> {
        let metadata = file.metadata().map_err(|e| Error::System("tree descriptor", e))?;
        let correct_role = match role {
            Role::Directory => metadata.is_dir(),
            Role::Control => metadata.is_file(),
        };
        if !correct_role {
            return Err(contract("tree descriptor role"));
        }
        let mut fs = std::mem::MaybeUninit::<libc::statfs>::zeroed();
        // SAFETY: the borrowed descriptor is live; fstatfs initializes exactly
        // one native statfs. No pathname or caller-supplied object is reopened.
        if unsafe { libc::fstatfs(file.as_raw_fd(), fs.as_mut_ptr()) } != 0 {
            return Err(system("tree filesystem"));
        }
        // SAFETY: successful fstatfs initialized the complete record.
        // GNU and musl expose signed/unsigned f_type respectively. This
        // positive magic is exact in both; reject negative/unrepresentable IDs.
        if u64::try_from(unsafe { fs.assume_init() }.f_type).ok() != Some(CGROUP2) {
            return Err(contract("tree descriptor is not cgroup2"));
        }
        Ok(Self {
            device: metadata.dev(),
            inode: metadata.ino(),
            mode: metadata.mode(),
            owner: metadata.uid(),
            group: metadata.gid(),
        })
    }
}

#[derive(Debug)]
pub(in crate::launcher) struct Control {
    file: File,
    identity: Identity,
}
impl Control {
    pub(in crate::launcher) fn open(
        directory: &File,
        name: &CStr,
        access: Access,
    ) -> Result<Self, Error> {
        let flags = match access {
            Access::Read => libc::O_RDONLY,
            Access::Write => libc::O_WRONLY,
        };
        // SAFETY: the directory and terminated fixed name are live. NOFOLLOW
        // rejects final aliases; cgroup2 control files are kernel-generated.
        let fd = unsafe {
            libc::openat(
                directory.as_raw_fd(),
                name.as_ptr(),
                flags | libc::O_CLOEXEC | libc::O_NOFOLLOW,
            )
        };
        if fd < 0 {
            return Err(system("tree control open"));
        }
        // SAFETY: successful openat returned a new uniquely owned descriptor.
        let file = unsafe { File::from_raw_fd(fd) };
        let identity = Identity::capture(&file, Role::Control)?;
        if identity.device != Identity::capture(directory, Role::Directory)?.device {
            return Err(contract("tree control filesystem identity"));
        }
        Ok(Self { file, identity })
    }
    fn same(&self) -> Result<(), Error> {
        if Identity::capture(&self.file, Role::Control)? != self.identity {
            return Err(contract("tree control identity changed"));
        }
        Ok(())
    }
    pub(in crate::launcher) fn read<const N: usize>(
        &self,
        buffer: &mut [u8; N],
        budget: &Budget,
    ) -> Result<usize, Error> {
        checked(budget)?;
        budget
            .charge(Charge { work: (N as u64) * 3, ..Charge::default() })
            .map_err(Error::Budget)?;
        self.same()?;
        let count = loop {
            match self.file.read_at(buffer, 0) {
                Ok(n) => break n,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {
                    budget
                        .charge(Charge { work: (N as u64) * 3, ..Default::default() })
                        .map_err(Error::Budget)?;
                }
                Err(e) => return Err(Error::System("tree control read", e)),
            }
        };
        if count == N {
            return Err(contract("tree control text bound"));
        }
        self.same()?;
        checked(budget)?;
        Ok(count)
    }
    pub(in crate::launcher) fn cleanup_read<const N: usize>(
        &self,
        buffer: &mut [u8; N],
        budget: &Budget,
    ) -> Result<usize, Error> {
        original_endpoint(budget)?;
        self.same()?;
        // One bounded attempt uses prepaid work. An interrupted cleanup read
        // refuses instead of hiding an unmetered retry/signal-storm interval.
        let count =
            self.file.read_at(buffer, 0).map_err(|e| Error::System("tree cleanup read", e))?;
        if count == N {
            return Err(contract("tree cleanup text bound"));
        }
        self.same()?;
        original_endpoint(budget)?;
        Ok(count)
    }
    pub(in crate::launcher) fn write(&self, bytes: &[u8]) -> Result<(), Error> {
        self.same()?;
        // SAFETY: only this owner's held control FD is written. The initialized
        // bounded scalar buffer is live; no numerical PID/PGID is signalled.
        let written =
            unsafe { libc::write(self.file.as_raw_fd(), bytes.as_ptr().cast(), bytes.len()) };
        if written < 0 {
            return Err(system("tree control write"));
        }
        if written as usize != bytes.len() {
            return Err(contract("tree control short write"));
        }
        self.same()
    }
    pub(in crate::launcher) fn scalar(&self, budget: &Budget) -> Result<u64, Error> {
        // A canonical u64 cgroup value requires at most twenty digits and LF.
        let mut buffer = [0; 22];
        let count = self.read(&mut buffer, budget)?;
        scalar(&buffer[..count])
    }
}
