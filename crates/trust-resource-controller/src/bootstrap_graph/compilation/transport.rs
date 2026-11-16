//! Direct same-channel stdio/GNU description transfer. This performs no local
//! helper spawn, GNU read/write, new CPU claim, member launch or retirement.
use std::io;
use std::os::fd::{AsFd, AsRawFd as _, BorrowedFd, OwnedFd};
use std::time::Instant;

use super::{DESCRIPTION_COUNT, MemberRequest, RIGHTS_MARKER};
use crate::Channel;
use crate::bootstrap_graph::transport::check_gnu_identity;
use crate::wire::invalid;

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
fn stdio(fd: BorrowedFd<'_>, reading: bool) -> io::Result<()> {
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: only observe the actual held description; mutate no flags/cursor.
    if flags < 0 || local < 0 || unsafe { libc::fstat(fd.as_raw_fd(), metadata.as_mut_ptr()) } != 0
    {
        return Err(io::Error::last_os_error());
    }
    let metadata = unsafe { metadata.assume_init() };
    if local & libc::FD_CLOEXEC == 0 || metadata.st_mode & libc::S_IFMT == libc::S_IFDIR {
        return Err(invalid());
    }
    let access = flags & libc::O_ACCMODE;
    if access != libc::O_RDWR && access != if reading { libc::O_RDONLY } else { libc::O_WRONLY } {
        return Err(invalid());
    }
    Ok(())
}
/// Actual held inputs in fixed order: stdin, stdout, stderr, GNU reader/writer.
/// The native Root still compares the SAME original GNU/Full/program owners.
/// These observations cannot establish that a queue credit is held or retired.
pub fn check(
    request: &MemberRequest,
    fds: &[BorrowedFd<'_>; DESCRIPTION_COUNT],
    deadline: Instant,
) -> io::Result<()> {
    request.validate()?;
    check_stdio_gnu(&request.gnu, fds, deadline)
}
pub(super) fn check_stdio_gnu(
    gnu: &crate::bootstrap_graph::GnuIdentity,
    fds: &[BorrowedFd<'_>; DESCRIPTION_COUNT],
    deadline: Instant,
) -> io::Result<()> {
    time(deadline)?;
    stdio(fds[0], true)?;
    stdio(fds[1], false)?;
    stdio(fds[2], false)?;
    check_gnu_identity(gnu, &[fds[3], fds[4]])?;
    time(deadline)
}
pub fn send(
    channel: &mut Channel,
    request: &MemberRequest,
    fds: &[BorrowedFd<'_>; DESCRIPTION_COUNT],
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        check(request, fds, deadline)?;
        current()?;
        time(deadline)?;
        channel.send_named_descriptions(fds, RIGHTS_MARKER, DESCRIPTION_COUNT, deadline)?;
        check(request, fds, deadline)?;
        current()?;
        time(deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
pub fn receive(
    channel: &mut Channel,
    request: &MemberRequest,
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; DESCRIPTION_COUNT]> {
    let result = (|| {
        time(deadline)?;
        current()?;
        let fds: [OwnedFd; DESCRIPTION_COUNT] = channel
            .receive_named_descriptions(
                DESCRIPTION_COUNT,
                RIGHTS_MARKER,
                DESCRIPTION_COUNT,
                deadline,
            )?
            .try_into()
            .map_err(|_| invalid())?;
        check(request, &fds.each_ref().map(AsFd::as_fd), deadline)?;
        current()?;
        time(deadline)?;
        Ok(fds)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

#[cfg(test)]
mod tests {
    use std::fs::{File, OpenOptions};
    use std::os::fd::{FromRawFd as _, OwnedFd};
    use std::os::unix::fs::MetadataExt as _;
    use std::os::unix::net::UnixStream;
    use std::time::Duration;

    use super::*;
    use crate::FileIdentity;
    use crate::bootstrap_graph::GnuIdentity;
    use crate::bootstrap_graph::compilation::tests::member;

    fn fixture() -> (MemberRequest, [OwnedFd; DESCRIPTION_COUNT]) {
        let input = File::open("/dev/null").unwrap();
        let output = OpenOptions::new().write(true).open("/dev/null").unwrap();
        let error = output.try_clone().unwrap();
        let mut pipe = [-1; 2];
        assert_eq!(unsafe { libc::pipe(pipe.as_mut_ptr()) }, 0);
        let reader = unsafe { OwnedFd::from_raw_fd(pipe[0]) };
        let writer = unsafe { OwnedFd::from_raw_fd(pipe[1]) };
        for fd in [&reader, &writer] {
            assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
        }
        let identity = |fd: &OwnedFd| {
            let file = File::from(fd.try_clone().unwrap());
            let metadata = file.metadata().unwrap();
            FileIdentity { device: metadata.dev(), inode: metadata.ino() }
        };
        let mut request = member();
        request.gnu =
            GnuIdentity::NumericPipe { read: identity(&reader), write: identity(&writer) };
        (request, [input.into(), output.into(), error.into(), reader, writer])
    }
    fn deadline() -> Instant {
        Instant::now() + Duration::from_secs(10)
    }
    #[test]
    fn actual_five_descriptions_roundtrip_without_spawning_or_consuming_gnu_bytes() {
        let (request, fds) = fixture();
        let (left, right) = UnixStream::pair().unwrap();
        let (mut sender, mut receiver) =
            (Channel::new(left).unwrap(), Channel::new(right).unwrap());
        send(&mut sender, &request, &fds.each_ref().map(AsFd::as_fd), deadline(), || Ok(()))
            .unwrap();
        let received = receive(&mut receiver, &request, deadline(), || Ok(())).unwrap();
        check(&request, &received.each_ref().map(AsFd::as_fd), deadline()).unwrap();
        assert!(!sender.poisoned() && !receiver.poisoned());
    }
    #[test]
    fn reversed_stdio_or_gnu_and_expired_current_owner_poison_instead_of_transfer() {
        let (request, fds) = fixture();
        let mut wrong = fds.each_ref().map(AsFd::as_fd);
        wrong.swap(0, 1);
        assert!(check(&request, &wrong, deadline()).is_err());
        let mut wrong = fds.each_ref().map(AsFd::as_fd);
        wrong.swap(3, 4);
        assert!(check(&request, &wrong, deadline()).is_err());
        assert!(check(&request, &fds.each_ref().map(AsFd::as_fd), Instant::now()).is_err());
        let (left, _right) = UnixStream::pair().unwrap();
        let mut sender = Channel::new(left).unwrap();
        assert!(
            send(&mut sender, &request, &fds.each_ref().map(AsFd::as_fd), deadline(), || Err(
                invalid()
            ))
            .is_err()
        );
        assert!(sender.poisoned());
    }
    #[test]
    fn foreign_gnu_or_incomplete_rights_never_create_a_member_input_population() {
        let (request, fds) = fixture();
        let mut foreign = request.clone();
        foreign.gnu = GnuIdentity::NumericPipe {
            read: FileIdentity { device: 77, inode: 88 },
            write: FileIdentity { device: 77, inode: 99 },
        };
        assert!(check(&foreign, &fds.each_ref().map(AsFd::as_fd), deadline()).is_err());
        let (left, right) = UnixStream::pair().unwrap();
        let (mut sender, mut receiver) =
            (Channel::new(left).unwrap(), Channel::new(right).unwrap());
        sender
            .send_named_descriptions(
                &fds[..4].iter().map(AsFd::as_fd).collect::<Vec<_>>(),
                RIGHTS_MARKER,
                DESCRIPTION_COUNT,
                deadline(),
            )
            .unwrap();
        assert!(receive(&mut receiver, &request, deadline(), || Ok(())).is_err());
        assert!(receiver.poisoned());
    }
}
