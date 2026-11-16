use super::*;

// Match std::time::Instant's clock domain. On Apple CLOCK_MONOTONIC and
// CLOCK_UPTIME_RAW have different sleep/adjustment semantics; translating a
// long-lived deadline through a different clock could extend its lifetime.
#[cfg(target_vendor = "apple")]
const DEADLINE_CLOCK: libc::clockid_t = libc::CLOCK_UPTIME_RAW;
#[cfg(not(target_vendor = "apple"))]
const DEADLINE_CLOCK: libc::clockid_t = libc::CLOCK_MONOTONIC;

pub(super) struct Channel {
    stream: UnixStream,
    deadline: Instant,
    incoming: Vec<u8>,
    rights: Vec<OwnedFd>,
    failure: Option<(io::ErrorKind, String)>,
}

impl Channel {
    pub(super) fn new(stream: UnixStream, deadline: Instant) -> io::Result<Self> {
        cloexec(stream.as_raw_fd())?;
        validate_stream(stream.as_raw_fd())?;
        stream.set_nonblocking(true)?;
        #[cfg(target_os = "macos")]
        {
            let yes: libc::c_int = 1;
            // SAFETY: this live socket and the option storage are owned here.
            if unsafe {
                libc::setsockopt(
                    stream.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_NOSIGPIPE,
                    (&raw const yes).cast(),
                    std::mem::size_of_val(&yes) as libc::socklen_t,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
        }
        Ok(Self { stream, deadline, incoming: Vec::new(), rights: Vec::new(), failure: None })
    }

    pub(super) fn limit_deadline(&mut self, deadline: Instant) {
        self.deadline = self.deadline.min(deadline);
    }

    pub(super) fn deadline(&self) -> Instant {
        self.deadline
    }

    #[cfg(test)]
    pub(super) fn stream_fd_for_test(&self) -> libc::c_int {
        self.stream.as_raw_fd()
    }

    pub(super) fn adopt_parent_expiry(&mut self, expiry: u64) -> io::Result<()> {
        // Only the startup receiver calls this, once. Sample Instant first so
        // conversion cannot extend the parent's remaining monotonic lifetime.
        let now = Instant::now();
        let remaining =
            expiry.checked_sub(monotonic_nanos()?).filter(|remaining| *remaining != 0).ok_or_else(
                || io::Error::new(io::ErrorKind::TimedOut, "retained parent deadline expired"),
            )?;
        self.deadline = now
            .checked_add(Duration::from_nanos(remaining))
            .ok_or_else(|| invalid("retained parent deadline overflow"))?;
        self.check()
    }

    pub(super) fn failed(&self) -> bool {
        self.failure.is_some()
    }

    pub(super) fn check(&mut self) -> io::Result<()> {
        if let Some((kind, message)) = &self.failure {
            return Err(io::Error::new(*kind, message.clone()));
        }
        if Instant::now() >= self.deadline {
            return self.reject_error(io::Error::new(
                io::ErrorKind::TimedOut,
                "retained session deadline expired",
            ));
        }
        Ok(())
    }

    pub(super) fn reject<T>(&mut self, message: impl Into<String>) -> io::Result<T> {
        self.reject_error(invalid(message))
    }

    pub(super) fn reject_error<T>(&mut self, error: io::Error) -> io::Result<T> {
        self.failure.get_or_insert_with(|| (error.kind(), error.to_string()));
        self.incoming.clear();
        self.rights.clear();
        let _ = self.stream.shutdown(Shutdown::Both);
        Err(error)
    }

    pub(super) fn pause(&mut self) -> io::Result<()> {
        self.check()?;
        std::thread::sleep(
            self.deadline.saturating_duration_since(Instant::now()).min(Duration::from_millis(2)),
        );
        self.check()
    }

    pub(super) fn send(&mut self, message: Message, rights: &[libc::c_int]) -> io::Result<()> {
        self.check()?;
        let bytes = match serde_json::to_vec(&Frame { version: VERSION, message }) {
            Ok(bytes) => bytes,
            Err(error) => return self.reject(error.to_string()),
        };
        if bytes.is_empty() || bytes.len() > MAX_FRAME_BYTES || rights.len() > 2 {
            return self.reject("retained frame or descriptor count exceeds its bound");
        }
        let mut packet = Vec::with_capacity(4 + bytes.len());
        packet.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
        packet.extend_from_slice(&bytes);
        let mut written = 0;
        let mut pending_rights = rights;
        while written < packet.len() {
            self.check()?;
            match send_chunk(&self.stream, &packet[written..], pending_rights) {
                Ok(0) => {
                    return self.reject_error(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "retained channel stopped writing",
                    ));
                }
                Ok(count) => {
                    written += count;
                    // Rights attach only to the first successfully sent byte.
                    pending_rights = &[];
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => self.pause()?,
                Err(error) => return self.reject_error(error),
            }
        }
        Ok(())
    }

    pub(super) fn poll(&mut self, startup: bool) -> io::Result<Option<(Message, Vec<OwnedFd>)>> {
        self.check()?;
        loop {
            if self.incoming.len() >= 4 {
                let length =
                    u32::from_be_bytes(self.incoming[..4].try_into().expect("frame prefix"))
                        as usize;
                if length == 0 || length > MAX_FRAME_BYTES {
                    return self.reject("retained frame length exceeds its bound");
                }
                if self.incoming.len() >= 4 + length {
                    let frame: Frame = match serde_json::from_slice(&self.incoming[4..4 + length]) {
                        Ok(frame) => frame,
                        Err(error) => {
                            return self.reject(format!("invalid retained frame: {error}"));
                        }
                    };
                    if frame.version != VERSION {
                        return self.reject("unsupported retained frame version");
                    }
                    self.incoming.drain(..4 + length);
                    let rights = std::mem::take(&mut self.rights);
                    return Ok(Some((frame.message, rights)));
                }
            }
            let mut bytes = [0u8; 2048];
            match receive_chunk(&self.stream, &mut bytes) {
                Ok((0, _)) => {
                    return self.reject_error(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "retained controller/child closed before completion",
                    ));
                }
                Ok((count, rights)) => {
                    if (!startup && !rights.is_empty()) || self.rights.len() + rights.len() > 2 {
                        return self.reject("unexpected retained descriptor rights");
                    }
                    self.rights.extend(rights);
                    self.incoming.extend_from_slice(&bytes[..count]);
                    if self.incoming.len() > MAX_FRAME_BYTES + 4 {
                        return self.reject("retained frame aggregate exceeds its bound");
                    }
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(None),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return self.reject_error(error),
            }
        }
    }

    pub(super) fn ensure_quiet(&mut self) -> io::Result<()> {
        self.ensure_quiet_with_eof(false)
    }

    // Only a validated one-use drained event permits EOF. This still rejects
    // every extra byte, including incomplete/replayed frames after that event.
    pub(super) fn ensure_finished(&mut self) -> io::Result<()> {
        self.ensure_quiet_with_eof(true)
    }

    fn ensure_quiet_with_eof(&mut self, allow_eof: bool) -> io::Result<()> {
        self.check()?;
        if !self.incoming.is_empty() || !self.rights.is_empty() {
            return self.reject("extra or replayed retained frame");
        }
        loop {
            let mut byte = [0];
            match receive_chunk(&self.stream, &mut byte) {
                Ok((0, rights)) if allow_eof && rights.is_empty() => return Ok(()),
                Ok((0, _)) => {
                    return self.reject_error(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "retained peer closed",
                    ));
                }
                Ok(_) => return self.reject("extra or replayed retained frame"),
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(()),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return self.reject_error(error),
            }
        }
    }

    pub(super) fn peer_closed(&mut self) -> io::Result<bool> {
        loop {
            self.check()?;
            let mut byte = [0u8];
            // SAFETY: MSG_PEEK observes one byte without consuming a queued
            // grant or taking ownership of ancillary descriptors.
            let count = unsafe {
                libc::recv(
                    self.stream.as_raw_fd(),
                    byte.as_mut_ptr().cast(),
                    1,
                    libc::MSG_PEEK | libc::MSG_DONTWAIT,
                )
            };
            if count == 0 {
                self.failure =
                    Some((io::ErrorKind::UnexpectedEof, "retained controller closed".into()));
                return Ok(true);
            }
            if count > 0 {
                return Ok(false);
            }
            let error = io::Error::last_os_error();
            match error.kind() {
                io::ErrorKind::WouldBlock => return Ok(false),
                io::ErrorKind::Interrupted => continue,
                _ => return self.reject_error(error),
            }
        }
    }
}

// Both endpoints execute on the same Unix host. This is only a lifetime bound,
// never a CPU entitlement or a caller-supplied reconstruction of authority.
pub(super) fn monotonic_expiry(deadline: Instant) -> io::Result<u64> {
    let now = monotonic_nanos()?;
    let remaining = deadline.checked_duration_since(Instant::now()).ok_or_else(|| {
        io::Error::new(io::ErrorKind::TimedOut, "retained parent deadline expired")
    })?;
    // Keep both sampling windows conservative, including clock quantization.
    // Reserve one actual clock tick so rounding the later child sample cannot
    // renew the parent's original bound.
    let remaining = u64::try_from(remaining.as_nanos())
        .map_err(|_| invalid("retained deadline overflow"))?
        .checked_sub(monotonic_resolution_nanos()?)
        .filter(|remaining| *remaining != 0)
        .ok_or_else(|| {
            io::Error::new(io::ErrorKind::TimedOut, "retained parent deadline expired")
        })?;
    now.checked_add(remaining).ok_or_else(|| invalid("retained deadline overflow"))
}

fn monotonic_nanos() -> io::Result<u64> {
    let mut time: libc::timespec = unsafe { std::mem::zeroed() };
    // SAFETY: clock_gettime only writes this initialized timespec.
    if unsafe { libc::clock_gettime(DEADLINE_CLOCK, &mut time) } != 0 {
        return Err(io::Error::last_os_error());
    }
    timespec_nanos(time)
}

fn monotonic_resolution_nanos() -> io::Result<u64> {
    let mut resolution: libc::timespec = unsafe { std::mem::zeroed() };
    // SAFETY: clock_getres only writes this initialized timespec.
    if unsafe { libc::clock_getres(DEADLINE_CLOCK, &mut resolution) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let resolution = timespec_nanos(resolution)?;
    if resolution == 0 {
        return Err(invalid("invalid monotonic resolution"));
    }
    Ok(resolution)
}

fn timespec_nanos(time: libc::timespec) -> io::Result<u64> {
    let seconds = u64::try_from(time.tv_sec).map_err(|_| invalid("invalid monotonic seconds"))?;
    let nanos = u64::try_from(time.tv_nsec)
        .ok()
        .filter(|n| *n < 1_000_000_000)
        .ok_or_else(|| invalid("invalid monotonic nanoseconds"))?;
    seconds
        .checked_mul(1_000_000_000)
        .and_then(|s| s.checked_add(nanos))
        .ok_or_else(|| invalid("monotonic time overflow"))
}

pub(super) fn cloexec(fd: libc::c_int) -> io::Result<()> {
    // SAFETY: fcntl validates the descriptor; flags apply to this copy only.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub(super) fn validate_stream(fd: libc::c_int) -> io::Result<()> {
    // SAFETY: all output storage is initialized and writable; the calls only
    // inspect this actual open descriptor without taking ownership of it.
    let mut address: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
    let mut length = std::mem::size_of_val(&address) as libc::socklen_t;
    if unsafe { libc::getsockname(fd, (&raw mut address).cast(), &mut length) } != 0 {
        return Err(io::Error::last_os_error());
    }
    if address.ss_family as libc::c_int != libc::AF_UNIX {
        return Err(invalid("retained endpoint must be a Unix socket"));
    }
    if unsafe { libc::getpeername(fd, (&raw mut address).cast(), &mut length) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let mut kind: libc::c_int = 0;
    let mut length = std::mem::size_of_val(&kind) as libc::socklen_t;
    if unsafe {
        libc::getsockopt(fd, libc::SOL_SOCKET, libc::SO_TYPE, (&raw mut kind).cast(), &mut length)
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    if kind != libc::SOCK_STREAM {
        return Err(invalid("retained endpoint must be a connected stream"));
    }
    Ok(())
}

fn send_chunk(stream: &UnixStream, bytes: &[u8], rights: &[libc::c_int]) -> io::Result<usize> {
    let mut iovec =
        libc::iovec { iov_base: bytes.as_ptr().cast_mut().cast(), iov_len: bytes.len() };
    let mut control = [0usize; 8];
    // SAFETY: zero is valid initialization for msghdr, populated below.
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iovec;
    message.msg_iovlen = 1;
    if !rights.is_empty() {
        // SAFETY: the fixed buffer is aligned and larger than CMSG_SPACE for
        // the at-most-two descriptors accepted by Channel::send.
        unsafe {
            let size = std::mem::size_of_val(rights);
            message.msg_control = control.as_mut_ptr().cast();
            message.msg_controllen = libc::CMSG_SPACE(size as _) as _;
            let header = libc::CMSG_FIRSTHDR(&message);
            (*header).cmsg_level = libc::SOL_SOCKET;
            (*header).cmsg_type = libc::SCM_RIGHTS;
            (*header).cmsg_len = libc::CMSG_LEN(size as _) as _;
            std::ptr::copy_nonoverlapping(
                rights.as_ptr().cast::<u8>(),
                libc::CMSG_DATA(header),
                size,
            );
        }
    }
    #[cfg(target_os = "linux")]
    let flags = libc::MSG_NOSIGNAL;
    #[cfg(not(target_os = "linux"))]
    let flags = 0;
    // SAFETY: all buffers and descriptor numbers remain borrowed and live.
    let count = unsafe { libc::sendmsg(stream.as_raw_fd(), &message, flags) };
    if count < 0 { Err(io::Error::last_os_error()) } else { Ok(count as usize) }
}

fn receive_chunk(stream: &UnixStream, bytes: &mut [u8]) -> io::Result<(usize, Vec<OwnedFd>)> {
    // Darwin installs even the SCM_RIGHTS descriptors omitted by MSG_CTRUNC;
    // their numbers would be unavailable for ownership and cleanup. XNU's
    // sockargs limits a control record to MCLBYTES (2048 bytes), and Linux
    // limits SCM_RIGHTS to 253 descriptors. Accommodate the entire record and
    // receive only one byte, so adjacent control-bearing stream records cannot
    // aggregate past this buffer. This is storage, not the accepted count: the
    // protocol still allows only two runtime writers.
    // https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/uipc_syscalls.c
    // XNU soreceive stops at the next control-bearing record; Linux bounds
    // aggregate SCM_RIGHTS to SCM_MAX_FD and stops after detaching those FDs:
    // https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/uipc_socket.c
    // https://github.com/torvalds/linux/blob/master/include/net/scm.h
    // https://github.com/torvalds/linux/blob/master/net/unix/af_unix.c
    let mut iovec =
        libc::iovec { iov_base: bytes.as_mut_ptr().cast(), iov_len: bytes.len().min(1) };
    let mut control = [0usize; 512];
    // SAFETY: initialized writable buffers outlive this recvmsg call.
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iovec;
    message.msg_iovlen = 1;
    message.msg_control = control.as_mut_ptr().cast();
    message.msg_controllen = std::mem::size_of_val(&control) as _;
    #[cfg(target_os = "linux")]
    let flags = libc::MSG_CMSG_CLOEXEC;
    #[cfg(not(target_os = "linux"))]
    let flags = 0;
    // SAFETY: all storage is writable and owned throughout the call.
    let count = unsafe { libc::recvmsg(stream.as_raw_fd(), &mut message, flags) };
    if count < 0 {
        return Err(io::Error::last_os_error());
    }
    let mut rights = Vec::new();
    let mut unsupported = false;
    // Darwin can preserve the sender's original cmsg_len on MSG_CTRUNC.
    // Neither that length nor a larger reported msg_controllen permits reading
    // beyond our actual receive buffer or adopting its uninitialized tail.
    if message.msg_controllen as usize > std::mem::size_of_val(&control) {
        unsupported = true;
        message.msg_controllen = std::mem::size_of_val(&control) as _;
    }
    // SAFETY: the kernel populated this bounded ancillary buffer. Own every
    // received descriptor before returning any error, including truncation.
    unsafe {
        let mut header = libc::CMSG_FIRSTHDR(&message);
        while !header.is_null() {
            let base = libc::CMSG_LEN(0) as usize;
            let Some(offset) = (header as usize).checked_sub(message.msg_control as usize) else {
                unsupported = true;
                break;
            };
            let Some(remaining) = (message.msg_controllen as usize).checked_sub(offset) else {
                unsupported = true;
                break;
            };
            if remaining < base {
                unsupported = true;
                break;
            }
            let length = (*header).cmsg_len as usize;
            if length < base {
                unsupported = true;
                break;
            }
            if (*header).cmsg_level == libc::SOL_SOCKET && (*header).cmsg_type == libc::SCM_RIGHTS {
                let size = length.min(remaining) - base;
                unsupported |= (length - base) % std::mem::size_of::<libc::c_int>() != 0
                    || size % std::mem::size_of::<libc::c_int>() != 0;
                for index in 0..size / std::mem::size_of::<libc::c_int>() {
                    let number = std::ptr::read_unaligned(
                        libc::CMSG_DATA(header).cast::<libc::c_int>().add(index),
                    );
                    if number < 0 {
                        unsupported = true;
                        continue;
                    }
                    rights.push(OwnedFd::from_raw_fd(number));
                }
            } else {
                unsupported = true
            }
            if length > remaining {
                unsupported = true;
                break;
            }
            header = libc::CMSG_NXTHDR(&message, header);
        }
    }
    if unsupported || message.msg_flags & (libc::MSG_CTRUNC | libc::MSG_TRUNC) != 0 {
        return Err(invalid("unsupported or truncated retained descriptor message"));
    }
    for fd in &rights {
        cloexec(fd.as_raw_fd())?;
    }
    if rights.len() > 2 {
        return Err(invalid("retained descriptor count exceeds its bound"));
    }
    Ok((count as usize, rights))
}

#[cfg(test)]
mod tests {
    use std::io::Read as _;

    use super::*;

    #[test]
    fn received_writers_are_cloexec_and_rejected_extra_rights_are_closed() {
        let (receiver, sender) = UnixStream::pair().unwrap();
        let (reader, writer) = UnixStream::pair().unwrap();
        send_chunk(&sender, b"x", &[writer.as_raw_fd()]).unwrap();
        let (_, rights) = receive_chunk(&receiver, &mut [0]).unwrap();
        assert_eq!(rights.len(), 1);
        // SAFETY: the returned OwnedFd still owns this exact received copy.
        let flags = unsafe { libc::fcntl(rights[0].as_raw_fd(), libc::F_GETFD) };
        assert!(flags >= 0, "the received descriptor must still be live");
        assert_ne!(flags & libc::FD_CLOEXEC, 0);
        drop((reader, writer, rights));

        let (receiver, sender) = UnixStream::pair().unwrap();
        let mut receiver = Channel::new(receiver, Instant::now() + Duration::from_secs(5)).unwrap();
        let (readers, writers): (Vec<_>, Vec<_>) =
            (0..3).map(|_| UnixStream::pair().unwrap()).unzip();
        for reader in &readers {
            reader.set_read_timeout(Some(Duration::from_secs(2))).unwrap();
        }
        let numbers = writers.iter().map(AsRawFd::as_raw_fd).collect::<Vec<_>>();
        send_chunk(&sender, b"x", &numbers).unwrap();
        drop(writers);
        assert!(receiver.poll(true).is_err());
        for mut reader in readers {
            assert_eq!(
                reader.read(&mut [0]).unwrap(),
                0,
                "rejected rights must not leak a runtime writer"
            );
        }
    }

    #[test]
    fn ancillary_truncation_releases_every_received_writer() {
        let (receiver, sender) = UnixStream::pair().unwrap();
        let (readers, writers): (Vec<_>, Vec<_>) =
            (0..40).map(|_| UnixStream::pair().unwrap()).unzip();
        // Darwin refuses SO_RCVTIMEO once its Unix peer is fully closed.
        // Arm the bounded observation while the actual writers are still live.
        for reader in &readers {
            reader.set_read_timeout(Some(Duration::from_secs(2))).unwrap();
        }
        // Build an oversized control buffer only in this adversarial sender.
        let numbers = writers.iter().map(AsRawFd::as_raw_fd).collect::<Vec<_>>();
        let mut control = vec![0usize; 64];
        let mut byte = b'x';
        let mut iovec = libc::iovec { iov_base: (&raw mut byte).cast(), iov_len: 1 };
        let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
        message.msg_iov = &mut iovec;
        message.msg_iovlen = 1;
        unsafe {
            let size = std::mem::size_of_val(numbers.as_slice());
            message.msg_control = control.as_mut_ptr().cast();
            message.msg_controllen = libc::CMSG_SPACE(size as _) as _;
            let header = libc::CMSG_FIRSTHDR(&message);
            (*header).cmsg_level = libc::SOL_SOCKET;
            (*header).cmsg_type = libc::SCM_RIGHTS;
            (*header).cmsg_len = libc::CMSG_LEN(size as _) as _;
            std::ptr::copy_nonoverlapping(
                numbers.as_ptr().cast::<u8>(),
                libc::CMSG_DATA(header),
                size,
            );
            assert_eq!(libc::sendmsg(sender.as_raw_fd(), &message, 0), 1);
        }
        drop(writers);
        let error = receive_chunk(&receiver, &mut [0]).unwrap_err();
        assert_eq!(error.to_string(), "retained descriptor count exceeds its bound");
        for mut reader in readers {
            assert_eq!(reader.read(&mut [0]).unwrap(), 0);
        }
    }
}
