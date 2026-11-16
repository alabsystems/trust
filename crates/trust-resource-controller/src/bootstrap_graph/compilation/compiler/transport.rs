//! Actual GNU2 witnesses only. No CPU FD, token read/write or entitlement.
use std::io;
use std::os::fd::{AsFd, BorrowedFd, OwnedFd};
use std::time::Instant;

use super::{AdoptRequest, GNU_RIGHTS_MARKER};
use crate::Channel;
use crate::bootstrap_graph::transport::check_gnu_identity;
use crate::wire::invalid;
fn check(request: &AdoptRequest, fds: &[BorrowedFd<'_>; 2], at: Instant) -> io::Result<()> {
    if Instant::now() >= at {
        return Err(io::ErrorKind::TimedOut.into());
    }
    request.validate()?;
    check_gnu_identity(&request.gnu, fds)
}
pub fn send_gnu(
    channel: &mut Channel,
    request: &AdoptRequest,
    fds: &[BorrowedFd<'_>; 2],
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        check(request, fds, deadline)?;
        current()?;
        channel.send_named_descriptions(fds, GNU_RIGHTS_MARKER, 2, deadline)?;
        check(request, fds, deadline)?;
        current()?;
        check(request, fds, deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
pub fn receive_gnu(
    channel: &mut Channel,
    request: &AdoptRequest,
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 2]> {
    let result = (|| {
        request.validate()?;
        current()?;
        let fds: [OwnedFd; 2] = channel
            .receive_named_descriptions(2, GNU_RIGHTS_MARKER, 2, deadline)?
            .try_into()
            .map_err(|_| invalid())?;
        check(request, &fds.each_ref().map(AsFd::as_fd), deadline)?;
        current()?;
        check(request, &fds.each_ref().map(AsFd::as_fd), deadline)?;
        Ok(fds)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

/// Actual stdio3 and SAME original GNU2 for the private paired-linker loan.
/// No descriptor is a CPU lease or a primary/parent-loan constructor.
pub fn send_linker_io(
    channel: &mut Channel,
    request: &super::PairedLinkerRequest,
    fds: &[BorrowedFd<'_>; 5],
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        request.validate()?;
        super::super::transport::check_stdio_gnu(&request.adopted.request.gnu, fds, deadline)?;
        current()?;
        channel.send_named_descriptions(fds, super::super::RIGHTS_MARKER, 5, deadline)?;
        current()?;
        super::super::transport::check_stdio_gnu(&request.adopted.request.gnu, fds, deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
pub fn receive_linker_io(
    channel: &mut Channel,
    request: &super::PairedLinkerRequest,
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 5]> {
    let result = (|| {
        request.validate()?;
        current()?;
        let fds: [OwnedFd; 5] = channel
            .receive_named_descriptions(5, super::super::RIGHTS_MARKER, 5, deadline)?
            .try_into()
            .map_err(|_| invalid())?;
        current()?;
        super::super::transport::check_stdio_gnu(
            &request.adopted.request.gnu,
            &fds.each_ref().map(AsFd::as_fd),
            deadline,
        )?;
        Ok(fds)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::os::fd::{AsRawFd as _, FromRawFd as _};
    use std::os::unix::fs::MetadataExt as _;
    use std::os::unix::net::UnixStream;
    use std::time::Duration;

    use super::*;
    use crate::FileIdentity;
    use crate::bootstrap_graph::GnuIdentity;
    #[test]
    fn real_original_gnu_two_descriptions_transfer_without_credit_or_cpu_fd() {
        let mut raw = [-1; 2];
        assert_eq!(unsafe { libc::pipe(raw.as_mut_ptr()) }, 0);
        let fds = raw.map(|fd| unsafe { OwnedFd::from_raw_fd(fd) });
        for fd in &fds {
            assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
        }
        let identity = |fd: &OwnedFd| {
            let meta = File::from(fd.try_clone().unwrap()).metadata().unwrap();
            FileIdentity { device: meta.dev(), inode: meta.ino() }
        };
        let mut request = super::super::tests::adopted().request;
        request.gnu =
            GnuIdentity::NumericPipe { read: identity(&fds[0]), write: identity(&fds[1]) };
        let deadline = Instant::now() + Duration::from_secs(10);
        let (left, right) = UnixStream::pair().unwrap();
        let (mut sender, mut receiver) =
            (Channel::new(left).unwrap(), Channel::new(right).unwrap());
        send_gnu(&mut sender, &request, &fds.each_ref().map(AsFd::as_fd), deadline, || Ok(()))
            .unwrap();
        let received = receive_gnu(&mut receiver, &request, deadline, || Ok(())).unwrap();
        check(&request, &received.each_ref().map(AsFd::as_fd), deadline).unwrap();
        assert!(!sender.poisoned() && !receiver.poisoned());
        let mut reversed = fds.each_ref().map(AsFd::as_fd);
        reversed.swap(0, 1);
        assert!(send_gnu(&mut sender, &request, &reversed, deadline, || Ok(())).is_err());
        assert!(sender.poisoned());
    }
    #[test]
    fn paired_linker_uses_same_exact_five_descriptions_without_a_cpu_descriptor() {
        use std::fs::OpenOptions;
        let mut raw = [-1; 2];
        assert_eq!(unsafe { libc::pipe(raw.as_mut_ptr()) }, 0);
        let gnu = raw.map(|fd| unsafe { OwnedFd::from_raw_fd(fd) });
        for fd in &gnu {
            assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
        }
        let identity = |fd: &OwnedFd| {
            let meta = File::from(fd.try_clone().unwrap()).metadata().unwrap();
            FileIdentity { device: meta.dev(), inode: meta.ino() }
        };
        let mut request = super::super::tests::linker();
        request.adopted.request.gnu =
            GnuIdentity::NumericPipe { read: identity(&gnu[0]), write: identity(&gnu[1]) };
        let fds: [OwnedFd; 5] = [
            File::open("/dev/null").unwrap().into(),
            OpenOptions::new().write(true).open("/dev/null").unwrap().into(),
            OpenOptions::new().write(true).open("/dev/null").unwrap().into(),
            gnu[0].try_clone().unwrap(),
            gnu[1].try_clone().unwrap(),
        ];
        let at = Instant::now() + Duration::from_secs(10);
        let (left, right) = UnixStream::pair().unwrap();
        let (mut sender, mut receiver) =
            (Channel::new(left).unwrap(), Channel::new(right).unwrap());
        send_linker_io(&mut sender, &request, &fds.each_ref().map(AsFd::as_fd), at, || Ok(()))
            .unwrap();
        let received = receive_linker_io(&mut receiver, &request, at, || Ok(())).unwrap();
        assert_eq!(received.len(), 5);
        let mut reversed = fds.each_ref().map(AsFd::as_fd);
        reversed.swap(3, 4);
        assert!(send_linker_io(&mut sender, &request, &reversed, at, || Ok(())).is_err());
        assert!(sender.poisoned());
    }
}
