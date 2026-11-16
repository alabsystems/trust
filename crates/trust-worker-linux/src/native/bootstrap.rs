//! Bounded trusted-entry handoff over a private SOCK_SEQPACKET channel. No
//! worker attestation or production launcher is implied by this receiver.
use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd};

use trust_process_isolation::{Budget, Charge};

use super::{charge, check, contract, reserve};
use crate::{Error, system};

#[repr(C)]
struct Ancillary {
    words: [usize; 16],
}

pub(super) fn configure(channel: &File, b: &Budget) -> Result<(), Error> {
    charge(b, Charge { work: 128, ..Charge::default() })?;
    let yes: libc::c_int = 1;
    // SAFETY: SO_PASSCRED reads one live integer and changes only this owned
    // private receiver before child handoff. It never accepts caller credentials.
    if unsafe {
        libc::setsockopt(
            channel.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PASSCRED,
            (&yes as *const libc::c_int).cast(),
            std::mem::size_of_val(&yes) as u32,
        )
    } != 0
    {
        b.refuse(trust_process_isolation::Error::Phase);
        return Err(system("native bootstrap credentials"));
    }
    check(b)
}

pub(super) fn receive(channel: &File, task: u32, b: &Budget) -> Result<File, Error> {
    let result = inner(channel, task, b"LISTENv1", 1, b)
        .and_then(|mut files| files.pop().ok_or_else(|| contract(b, "native listener ownership")));
    if result.is_err() {
        b.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
fn inner(
    channel: &File,
    task: u32,
    tag: &[u8],
    count: usize,
    b: &Budget,
) -> Result<Vec<File>, Error> {
    charge(b, Charge { work: 2048, ..Charge::default() })?;
    if task == 0 || tag.is_empty() || tag.len() > 64 || !(1..=8).contains(&count) {
        return Err(contract(b, "native bootstrap owner"));
    }
    // Reserve before recvmsg transfers ownership; a grant failure must never
    // leave received SCM_RIGHTS descriptors outside owned cleanup.
    let mut files = reserve::<File>(8, b)?;
    let mut bytes = [0; 64];
    let mut ancillary = Ancillary { words: [0; 16] };
    let mut io = libc::iovec { iov_base: bytes.as_mut_ptr().cast(), iov_len: tag.len() };
    // SAFETY: msghdr is a C plain-data structure, completely zero initialized.
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = &mut io;
    msg.msg_iovlen = 1;
    msg.msg_control = ancillary.words.as_mut_ptr().cast();
    // GNU uses size_t, musl socklen_t. Never truncate a supplied buffer length.
    msg.msg_controllen = std::mem::size_of_val(&ancillary)
        .try_into()
        .map_err(|_| contract(b, "native ancillary capacity"))?;
    // SAFETY: every writable region named by msghdr is live and bounded. The
    // private packet receiver is nonblocking, and received FDs are CLOEXEC.
    let n = unsafe {
        libc::recvmsg(channel.as_raw_fd(), &mut msg, libc::MSG_DONTWAIT | libc::MSG_CMSG_CLOEXEC)
    };
    if n < 0 {
        return Err(system("native listener handoff"));
    }
    let mut peer = None;
    let mut malformed = false;
    // SAFETY: successful recvmsg initialized a kernel-provided bounded control
    // sequence in aligned storage. We validate each length before payload reads,
    // own every received FD, and close all of them on any malformed record.
    unsafe {
        let mut item = libc::CMSG_FIRSTHDR(&msg);
        while !item.is_null() {
            let header = &*item;
            let zero = libc::CMSG_LEN(0) as usize;
            // On supported 64-bit Linux targets these ABI lengths are either
            // usize (GNU) or u32 (musl), both losslessly represented by usize.
            let length = header.cmsg_len as usize;
            if length < zero {
                malformed = true;
                break;
            }
            let start = item as usize;
            let begin = msg.msg_control as usize;
            let end = begin + msg.msg_controllen as usize;
            if start < begin || length > end.saturating_sub(start) {
                malformed = true;
                break;
            }
            let payload = length - zero;
            if header.cmsg_level == libc::SOL_SOCKET && header.cmsg_type == libc::SCM_RIGHTS {
                if payload % std::mem::size_of::<i32>() != 0 {
                    malformed = true;
                    break;
                }
                for at in 0..payload / std::mem::size_of::<i32>() {
                    let fd = (libc::CMSG_DATA(item) as *const i32).add(at).read_unaligned();
                    if fd < 0 {
                        malformed = true;
                        continue;
                    }
                    let file = File::from_raw_fd(fd);
                    if files.len() == 8 {
                        malformed = true;
                        drop(file);
                    } else {
                        files.push(file);
                    }
                }
            } else if header.cmsg_level == libc::SOL_SOCKET
                && header.cmsg_type == libc::SCM_CREDENTIALS
                && payload == std::mem::size_of::<libc::ucred>()
                && peer.is_none()
            {
                peer = Some((libc::CMSG_DATA(item) as *const libc::ucred).read_unaligned());
            } else {
                malformed = true;
            }
            item = libc::CMSG_NXTHDR(&msg, item);
        }
    }
    // SAFETY: effective credentials are scalar parent observations only.
    let expected = unsafe { (libc::geteuid(), libc::getegid()) };
    if n != tag.len() as isize
        || &bytes[..tag.len()] != tag
        || msg.msg_flags & (libc::MSG_CTRUNC | libc::MSG_TRUNC) != 0
        || malformed
        || files.len() != count
        || peer.is_none_or(|p| {
            p.pid <= 0 || p.pid as u32 != task || p.uid != expected.0 || p.gid != expected.1
        })
    {
        return Err(contract(b, "native listener ancillary identity"));
    }
    check(b)?;
    Ok(files)
}

pub(super) struct BrokerHandoff {
    pub listener: File,
    pub memory: File,
    pub maps: File,
}
fn broker_tag(worker: u32, capsule: [u8; 32]) -> [u8; 48] {
    let mut tag = [0; 48];
    tag[..8].copy_from_slice(b"BROKERv1");
    tag[8..40].copy_from_slice(&capsule);
    tag[40..44].copy_from_slice(&worker.to_le_bytes());
    tag
}
pub(super) fn receive_broker(
    channel: &File,
    parent: u32,
    worker: u32,
    capsule: [u8; 32],
    b: &Budget,
) -> Result<BrokerHandoff, Error> {
    let result = (|| {
        if worker == 0 || capsule == [0; 32] {
            return Err(contract(b, "native broker handoff context"));
        }
        let files = inner(channel, parent, &broker_tag(worker, capsule), 3, b)?;
        let [listener, memory, maps] = <[File; 3]>::try_from(files)
            .map_err(|_| contract(b, "native broker descriptor roles"))?;
        Ok(BrokerHandoff { listener, memory, maps })
    })();
    if result.is_err() {
        b.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
pub(super) fn send_listener(channel: &File, listener: &File, b: &Budget) -> Result<(), Error> {
    send(channel, b"LISTENv1", &[listener.as_raw_fd()], b)
}
pub(super) fn send_broker(
    channel: &File,
    worker: u32,
    capsule: [u8; 32],
    handoff: &BrokerHandoff,
    b: &Budget,
) -> Result<(), Error> {
    if worker == 0 || capsule == [0; 32] {
        return Err(contract(b, "native broker handoff context"));
    }
    send(
        channel,
        &broker_tag(worker, capsule),
        &[handoff.listener.as_raw_fd(), handoff.memory.as_raw_fd(), handoff.maps.as_raw_fd()],
        b,
    )
}
fn send(channel: &File, tag: &[u8], fds: &[i32], b: &Budget) -> Result<(), Error> {
    let result = (|| {
        if tag.is_empty() || tag.len() > 64 || fds.is_empty() || fds.len() > 8 {
            return Err(contract(b, "native handoff send bound"));
        }
        charge(b, Charge { wire_bytes: tag.len() as u64, work: 2048, ..Charge::default() })?;
        let mut ancillary = Ancillary { words: [0; 16] };
        let mut io = libc::iovec { iov_base: tag.as_ptr() as *mut _, iov_len: tag.len() };
        // SAFETY: plain C message data with every live bounded pointer below.
        let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
        msg.msg_iov = &mut io;
        msg.msg_iovlen = 1;
        msg.msg_control = ancillary.words.as_mut_ptr().cast();
        let size = (4 * fds.len()) as u32;
        // SAFETY: at most8FDs fit in the aligned fixed storage, all descriptors
        // are borrowed live owned capabilities; no ownership is lost on error.
        unsafe {
            msg.msg_controllen = libc::CMSG_SPACE(size)
                .try_into()
                .map_err(|_| contract(b, "native handoff ancillary size"))?;
            let item = libc::CMSG_FIRSTHDR(&msg);
            (*item).cmsg_level = libc::SOL_SOCKET;
            (*item).cmsg_type = libc::SCM_RIGHTS;
            (*item).cmsg_len = libc::CMSG_LEN(size)
                .try_into()
                .map_err(|_| contract(b, "native handoff ancillary length"))?;
            for (at, fd) in fds.iter().enumerate() {
                (libc::CMSG_DATA(item) as *mut i32).add(at).write_unaligned(*fd);
            }
            if libc::sendmsg(channel.as_raw_fd(), &msg, libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL)
                != tag.len() as isize
            {
                return Err(system("native handoff send"));
            }
        }
        check(b)
    })();
    if result.is_err() {
        b.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
