// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io;
use std::os::fd::AsRawFd as _;
use std::time::Instant;

use trust_resource_provenance::process::{self, Identity};

use super::wire::invalid;
use super::{BootstrapChannel, Frame};

/// Informational observations of the authenticated original attempt. This
/// holds the sole endpoint watcher until process exit; Drop cannot disable it.
pub struct Accepted {
    _watch: std::thread::JoinHandle<()>,
    pub attempt: [u8; 16],
    pub units: u32,
    pub footprint_mib: u32,
    pub monotonic_ns: u64,
    pub pid: u32,
    pub birth: u64,
}

/// Enter only from the selected final image, before any payload/input work.
/// The authentication callback must verify the actual parent against the
/// maintained Host, original live claim and selected role. Native peer equality
/// alone proves none of those. It is called before sealing and again before
/// accepting Run, for the same measured native peer and exact Offer. It must
/// revalidate retained authority, never acquire another claim. The seal callback
/// installs the ONE combined
/// final policy; its result never becomes a kernel-policy readback receipt.
///
/// Any error is terminal for this managed invocation: the final policy may
/// already be installed. The caller must refuse payload work and terminate;
/// it must not retry on another endpoint, enter its ordinary unsealed path,
/// or interpret an error as permission to undo or reinstall the seal.
pub fn receive(
    mut channel: BootstrapChannel,
    deadline: Instant,
    mut authenticate: impl FnMut(Identity, &Frame) -> io::Result<()>,
    seal: impl FnOnce(&Frame) -> io::Result<()>,
) -> io::Result<Accepted> {
    alive(deadline)?;
    let peer = channel.channel.native_peer()?;
    let original = process::read_identity(std::process::id())?;
    if original.parent != peer.pid {
        return Err(invalid());
    }
    let offer = channel.receive(deadline)?;
    if offer.kind != 1 || offer.pid != original.pid || offer.birth != original.birth {
        return Err(invalid());
    }
    authenticate(peer, &offer)?;
    alive(deadline)?;
    seal(&offer)?;
    if process::read_identity(original.pid)? != original || channel.channel.native_peer()? != peer {
        return Err(invalid());
    }
    let (send, receive) = std::sync::mpsc::sync_channel(1);
    let (armed, ready) = std::sync::mpsc::sync_channel(1);
    let watch = std::thread::Builder::new().name("resource-host-loss".into()).spawn(move || {
        if armed.send(()).is_ok()
            && let Ok(channel) = receive.recv()
        {
            watch_owner(channel);
        }
    })?;
    ready.recv_timeout(deadline.saturating_duration_since(Instant::now())).map_err(|e| {
        io::Error::from(match e {
            std::sync::mpsc::RecvTimeoutError::Timeout => io::ErrorKind::TimedOut,
            std::sync::mpsc::RecvTimeoutError::Disconnected => io::ErrorKind::UnexpectedEof,
        })
    })?;
    channel.send(offer.response(2, 0), deadline)?;
    let run = channel.receive(deadline)?;
    if run.kind != 3 || run != offer.response(3, run.monotonic_ns) {
        return Err(invalid());
    }
    if process::read_identity(original.pid)? != original || channel.channel.native_peer()? != peer {
        return Err(invalid());
    }
    authenticate(peer, &offer)?;
    if process::read_identity(original.pid)? != original || channel.channel.native_peer()? != peer {
        return Err(invalid());
    }
    alive(deadline)?;
    // No bytes or closure are legal after Run. Refuse already observable
    // loss/trailing input before payload work; the retained watcher handles
    // anything that becomes observable after this final nonconsuming look.
    if channel.channel.ready_to_receive()? {
        return Err(invalid());
    }
    send.try_send(channel).map_err(|_| invalid())?;
    Ok(Accepted {
        _watch: watch,
        attempt: run.attempt,
        units: run.units,
        footprint_mib: run.footprint_mib,
        monotonic_ns: run.monotonic_ns,
        pid: run.pid,
        birth: run.birth,
    })
}

fn alive(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline {
        Err(io::ErrorKind::TimedOut.into())
    } else {
        Ok(())
    }
}
fn watch_owner(channel: BootstrapChannel) {
    loop {
        let mut poll =
            libc::pollfd { fd: channel.as_fd().as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: this initialized entry references the exclusively held
        // endpoint. Poll neither changes its flags nor consumes Run.
        let ready = unsafe { libc::poll(&mut poll, 1, -1) };
        if ready < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
            continue;
        }
        if ready == 0 {
            continue;
        }
        // No traffic is legal after Run. EOF, bytes, poll failure, or invalid
        // descriptor facts terminate THIS process, never an observed target.
        // SAFETY: no unwind may resume work or release borrowed rights.
        unsafe { libc::_exit(75) }
    }
}
