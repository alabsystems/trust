//! Native description transfer on the SAME original accepted graph channel.
//! Caller owns native peer/Job authentication and original preparation guard.
//! These functions validate descriptions, never mint resource/lock/GO owners.
use std::io;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::MetadataExt as _;
use std::time::Instant;

use super::{Enrollment, GNU_RIGHTS_MARKER, GnuIdentity, OUTPUT_RIGHTS_MARKER, OutputAttachment};
use crate::{Channel, FileIdentity};

/// Unclassified actual kernel-delivered descriptions. No public constructor:
/// flags/status DATA cannot manufacture the native receiver's FD population.
/// The Host must install even malformed delivery in its SAME State before any
/// peer/semantic postchecks. This type is NOT OriginalPreparationOutput.
#[must_use = "retain even malformed delivered descriptions through actual native quarantine"]
pub struct PreparationOutputDelivery {
    descriptions: Option<Vec<OwnedFd>>,
    valid: bool,
}
impl PreparationOutputDelivery {
    pub(crate) fn received(descriptions: Vec<OwnedFd>, valid: bool) -> Self {
        Self {
            descriptions: Some(descriptions),
            valid,
        }
    }

    /// Unique explicit takeover into the actual native State's unclassified
    /// population. Reserve while this SAME guard still owns every FD; even an
    /// allocation unwind cannot close uncertain descriptions. No intermediate
    /// unguarded Vec escapes, and no descriptor is cloned or reconstructed.
    pub fn into_parts(mut self, retained: &mut Vec<OwnedFd>) -> bool {
        retained.reserve(
            self.descriptions
                .as_ref()
                .expect("same unconsumed delivery")
                .len(),
        );
        retained.append(
            self.descriptions
                .as_mut()
                .expect("same uniquely owned delivery"),
        );
        drop(self.descriptions.take()); // empty after the unique append
        self.valid
    }
}
impl Drop for PreparationOutputDelivery {
    fn drop(&mut self) {
        // An actor queue/host/caller unwind is not native retirement. Keep the
        // SAME actual population on every unconsumed path, including foreign
        // process Drop; no saved FD numbers can reconstruct a later owner.
        if let Some(originals) = self.descriptions.take() {
            std::mem::forget(originals);
        }
    }
}

pub fn receive_preparation_output_delivery(
    channel: &mut Channel,
    deadline: Instant,
) -> io::Result<PreparationOutputDelivery> {
    channel.receive_preparation_output_delivery(deadline)
}

/// The sender retains its actual original OutputLock under the same selected
/// SDK contract as ordinary output transfer. DATA/fstat never creates that lock.
pub fn send_preparation_output(
    channel: &mut Channel,
    request: &super::offline_preparation::PreparationOutputAttachment,
    fds: &[BorrowedFd<'_>; 2],
    deadline: Instant,
    revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    request.validate()?;
    let binding = request.physical_binding();
    send(
        channel,
        fds,
        super::offline_preparation::PREPARATION_OUTPUT_RIGHTS_MARKER,
        deadline,
        || check_output(&binding, fds),
        revalidate,
    )
}

mod preparation_cache;
pub use preparation_cache::{
    PREPARATION_CACHE_DIRECTORY_RIGHTS_MARKER, PreparationCacheDirectoryDelivery,
    receive_preparation_cache_directory, send_preparation_cache_directory,
};

mod source;
pub use source::{check_source, receive_source, send_source};
mod configuration;
pub use configuration::{
    check_configuration, receive_configuration_description, send_configuration_description,
};

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
fn inspect(fd: BorrowedFd<'_>) -> io::Result<(FileIdentity, libc::mode_t, libc::c_int)> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: observe this held description only; change no cursor/OFD flags.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let stat = unsafe { stat.assume_init() };
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    if flags < 0 || local < 0 {
        return Err(io::Error::last_os_error());
    }
    if local & libc::FD_CLOEXEC == 0 {
        return Err(crate::wire::invalid());
    }
    Ok((
        FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino },
        stat.st_mode & libc::S_IFMT,
        flags & libc::O_ACCMODE,
    ))
}
fn distinct(fds: &[BorrowedFd<'_>; 2]) -> io::Result<()> {
    if fds[0].as_raw_fd() == fds[1].as_raw_fd() {
        return Err(crate::wire::invalid());
    }
    Ok(())
}

pub fn check_gnu(request: &Enrollment, fds: &[BorrowedFd<'_>; 2]) -> io::Result<()> {
    request.validate()?;
    check_gnu_identity(&request.gnu, fds)
}

/// Observe the same retained GNU descriptions before a query, without
/// synthesizing an enrollment or acquiring, returning or creating any byte.
pub fn check_gnu_identity(gnu: &GnuIdentity, fds: &[BorrowedFd<'_>; 2]) -> io::Result<()> {
    gnu.write(&mut crate::wire::Encoder::new(0))?;
    distinct(fds)?;
    let (read, read_type, read_access) = inspect(fds[0])?;
    let (write, write_type, write_access) = inspect(fds[1])?;
    if read_type != libc::S_IFIFO || write_type != libc::S_IFIFO {
        return Err(crate::wire::invalid());
    }
    match gnu {
        GnuIdentity::NumericPipe { read: expected_read, write: expected_write }
            if read == *expected_read
                && write == *expected_write
                && read_access == libc::O_RDONLY
                && write_access == libc::O_WRONLY => {}
        GnuIdentity::NamedFifo { path, backing }
            if read == *backing
                && write == *backing
                && (read_access == libc::O_RDONLY || read_access == libc::O_RDWR)
                && (write_access == libc::O_WRONLY || write_access == libc::O_RDWR) =>
        {
            // Observe the original advertised namespace entry, never reopen or
            // acquire a lock/token. A link or changed backing refuses.
            let path = std::path::Path::new(std::ffi::OsStr::from_bytes(path));
            let entry = std::fs::symlink_metadata(path)?;
            if entry.mode() & libc::S_IFMT as u32 != libc::S_IFIFO as u32
                || entry.dev() != backing.device
                || entry.ino() != backing.inode
            {
                return Err(crate::wire::invalid());
            }
        }
        _ => return Err(crate::wire::invalid()),
    }
    Ok(())
}

pub fn check_output(request: &OutputAttachment, fds: &[BorrowedFd<'_>; 2]) -> io::Result<()> {
    request.encode()?;
    distinct(fds)?;
    let (root, root_type, root_access) = inspect(fds[0])?;
    let (lock, lock_type, lock_access) = inspect(fds[1])?;
    if root != request.root
        || root_type != libc::S_IFDIR
        || root_access != libc::O_RDONLY
        || lock != request.lock
        || lock_type != libc::S_IFREG
        || lock_access != libc::O_RDWR
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}

fn send(
    channel: &mut Channel,
    fds: &[BorrowedFd<'_>; 2],
    marker: u8,
    deadline: Instant,
    mut check: impl FnMut() -> io::Result<()>,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        time(deadline)?;
        check()?;
        revalidate()?;
        time(deadline)?;
        channel.send_bootstrap_descriptions(fds, marker, deadline)?;
        check()?;
        revalidate()?;
        time(deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
fn receive(
    channel: &mut Channel,
    marker: u8,
    deadline: Instant,
    check: impl FnOnce(&[BorrowedFd<'_>; 2]) -> io::Result<()>,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 2]> {
    let result = (|| {
        time(deadline)?;
        revalidate()?;
        time(deadline)?;
        let fds: [OwnedFd; 2] = channel
            .receive_bootstrap_descriptions(marker, deadline)?
            .try_into()
            .map_err(|_| crate::wire::invalid())?;
        check(&fds.each_ref().map(AsFd::as_fd))?;
        revalidate()?;
        time(deadline)?;
        Ok(fds)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

/// Offer exactly once after the SAME authenticated Prepared reply. This does
/// not close the control connection or change original scheduling flags.
pub fn send_gnu(
    channel: &mut Channel,
    request: &Enrollment,
    fds: &[BorrowedFd<'_>; 2],
    deadline: Instant,
    revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    send(channel, fds, GNU_RIGHTS_MARKER, deadline, || check_gnu(request, fds), revalidate)
}
pub fn receive_gnu(
    channel: &mut Channel,
    request: &Enrollment,
    deadline: Instant,
    revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 2]> {
    receive(channel, GNU_RIGHTS_MARKER, deadline, |fds| check_gnu(request, fds), revalidate)
}

/// The producer must retain its SAME actual close-only OutputLock/physical root
/// through the graph. Host independently requires the trusted original-capsule
/// contract; neither check_output nor SCM reconstructs lock ownership.
pub fn send_output(
    channel: &mut Channel,
    request: &OutputAttachment,
    fds: &[BorrowedFd<'_>; 2],
    deadline: Instant,
    revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    send(channel, fds, OUTPUT_RIGHTS_MARKER, deadline, || check_output(request, fds), revalidate)
}
pub fn receive_output(
    channel: &mut Channel,
    request: &OutputAttachment,
    deadline: Instant,
    revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 2]> {
    receive(channel, OUTPUT_RIGHTS_MARKER, deadline, |fds| check_output(request, fds), revalidate)
}

#[cfg(test)]
mod tests;
