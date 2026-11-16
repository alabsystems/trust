//! Transfer existing CPU/GNU descriptions without parsing ambient descriptor
//! numbers or creating a second local token pool.
use std::fs::File;
use std::io;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd, OwnedFd};
use std::os::unix::{ffi::OsStrExt, fs::MetadataExt};

use cargo_util::Jobserver;
use jobserver::TransportWitnesses;
use trust_build_cpu::Lease;
use trust_resource_controller::{Delegations, Descriptor, GnuTransport};

fn source(file: BorrowedFd<'_>) -> io::Result<OwnedFd> {
    // SAFETY: clone this held description into a fresh close-on-exec source
    // slot outside stdio. This never overwrites or changes the original.
    let raw = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 5) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful F_DUPFD_CLOEXEC returned exactly this new owned slot.
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
}

pub(super) fn cpu_only(lease: &Lease) -> io::Result<(Delegations, Vec<OwnedFd>)> {
    cpu_at(lease, 5)
}

fn cpu_at(lease: &Lease, target: u32) -> io::Result<(Delegations, Vec<OwnedFd>)> {
    let cpu = source(lease.as_fd())?;
    Ok((
        Delegations {
            cpu: Some(Descriptor {
                source: cpu.as_raw_fd() as u32,
                target,
            }),
            gnu: GnuTransport::None,
            fences: Vec::new(),
        },
        vec![cpu],
    ))
}

pub(super) fn shared(lease: &Lease, server: &Jobserver) -> io::Result<(Delegations, Vec<OwnedFd>)> {
    let (mut delegation, mut files) = cpu_only(lease)?;
    attach_gnu(&mut delegation, &mut files, server, (6, 7))?;
    Ok((delegation, files))
}

/// Role8 uses the actual native compiler layout: SDK5 and Store7 remain
/// reserved. These are duplicates of the SAME original CPU/GNU descriptions,
/// never a new scheduler or an ambient descriptor-number adoption.
pub(super) fn coordinator(
    lease: &Lease,
    server: Option<&Jobserver>,
) -> io::Result<(Delegations, Vec<OwnedFd>)> {
    let (mut delegation, mut files) = cpu_at(lease, 6)?;
    if let Some(server) = server {
        attach_gnu(&mut delegation, &mut files, server, (8, 9))?;
    }
    Ok((delegation, files))
}

fn attach_gnu(
    delegation: &mut Delegations,
    files: &mut Vec<OwnedFd>,
    server: &Jobserver,
    targets: (u32, u32),
) -> io::Result<()> {
    let (locator, read, write) = match server.client().transport_witnesses()? {
        TransportWitnesses::NumericPipe { read, write } => (None, read, write),
        TransportWitnesses::NamedFifo { path, read, write } => (Some(path), read, write),
    };
    let read = File::from(source(read.as_fd())?);
    let write = source(write.as_fd())?;
    let read_target = Descriptor {
        source: read.as_raw_fd() as u32,
        target: targets.0,
    };
    let write_target = Descriptor {
        source: write.as_raw_fd() as u32,
        target: targets.1,
    };
    delegation.gnu = if let Some(path) = locator {
        let identity = read.metadata()?;
        GnuTransport::NamedFifo {
            locator: path.as_os_str().as_bytes().to_vec(),
            device: identity.dev(),
            inode: identity.ino(),
            read: read_target,
            write: write_target,
        }
    } else {
        GnuTransport::NumericPipe {
            read: read_target,
            write: write_target,
        }
    };
    files.push(read.into());
    files.push(write);
    Ok(())
}
