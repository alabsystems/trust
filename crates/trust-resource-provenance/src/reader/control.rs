// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original control backing across a native child exec. No saved Record is an
//! importer: the connected kernel peer, original loaded vnode, actual paths,
//! private backing, immutable content and ancestry are checked independently.
use super::*;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
#[cfg(target_os = "macos")]
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::FileExt;
use std::os::unix::net::UnixListener;

pub const ORIGINAL_CONTROL_DESCRIPTORS: usize = 9;

/// An exporter issued only from a real selected pin. Its anchor is a genuine
/// connected native Host, not an identity label. The caller must admit the
/// anchor and all child copies before creating this owner/duplicating rights.
/// Dropping it neither closes a workload nor returns any CPU original.
pub struct HostControlTransfer {
    source: Arc<PinnedHelper>,
    anchor: UnixStream,
    failed: std::sync::atomic::AtomicBool,
}
impl HostControlTransfer {
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        use std::sync::atomic::Ordering;
        if self.failed.load(Ordering::Acquire) {
            return Err(refused("control transfer is poisoned"));
        }
        let result = self.validate_inner(deadline);
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        if self.failed.load(Ordering::Acquire) {
            return result.and_then(|_| Err(refused("control transfer failed concurrently")));
        }
        result
    }
    fn validate_inner(&self, deadline: Instant) -> io::Result<()> {
        self.source.validate(deadline)?;
        process::check_peer(&self.anchor, self.source.identity)?;
        if self.anchor.peer_addr()?.as_pathname() != Some(self.source.socket_path()) {
            return Err(refused("control anchor endpoint changed"));
        }
        self.source.validate(deadline)
    }
    /// Exactly eight retained backing originals and the same native anchor.
    /// No discovery, path open, replacement owner or resource grant occurs.
    pub fn duplicate_descriptions(
        &self,
        deadline: Instant,
    ) -> io::Result<[OwnedFd; ORIGINAL_CONTROL_DESCRIPTORS]> {
        self.validate(deadline)?;
        let store = &self.source.instance.store.0;
        let files = [
            store.root.as_fd(),
            store.images.as_fd(),
            store.instances.as_fd(),
            store.version.as_fd(),
            store.lock.as_fd(),
            self.source.image.file.as_fd(),
            self.source.image.directory.as_fd(),
            self.source.socket_parent.as_fd(),
            self.anchor.as_fd(),
        ];
        let originals = files
            .into_iter()
            .map(|file| file.try_clone_to_owned())
            .collect::<io::Result<Vec<_>>>()?
            .try_into()
            .map_err(|_| refused("control original population changed"))?;
        self.validate(deadline)?;
        Ok(originals)
    }
}
impl PinnedHelper {
    /// Retained allocation observation for bounded callers, never admission.
    pub fn retained_control_bytes(&self) -> Option<usize> {
        let record = &self.instance.record;
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(std::mem::size_of::<Backing>())?
            .checked_add(std::mem::size_of::<Image>())?
            .checked_add(std::mem::size_of::<File>())?;
        for capacity in [
            self.instance.store.0.path.capacity(),
            self.instance.helper.capacity(),
            self.instance.socket.capacity(),
            record.host.capacity(),
            record.boot.capacity(),
            record.digest.capacity(),
            record.socket_hex.capacity(),
        ] {
            bytes = bytes.checked_add(capacity)?;
        }
        if self.control_anchor.is_some() {
            bytes = bytes.checked_add(std::mem::size_of::<UnixStream>())?;
        }
        Some(bytes)
    }
    /// Equality observation against this pin's actual original store.
    pub fn same_original_store_directory(&self, fd: BorrowedFd<'_>) -> io::Result<bool> {
        self.instance.store.same_original_directory(fd)
    }
    pub fn control_transfer(
        self: &Arc<Self>,
        deadline: Instant,
    ) -> io::Result<HostControlTransfer> {
        let host = self.connect(deadline)?;
        host.revalidate(deadline)?;
        let transfer = HostControlTransfer {
            source: Arc::clone(self),
            anchor: host.stream,
            failed: std::sync::atomic::AtomicBool::new(false),
        };
        transfer.validate(deadline)?;
        Ok(transfer)
    }
    /// Exact original files whose bytes the supported importer reads. Metadata
    /// checks need no recursive control-directory read permission. These paths
    /// are equality DATA derived from this owner, never a generic scope grant.
    pub fn original_control_read_paths(&self, deadline: Instant) -> io::Result<[PathBuf; 2]> {
        self.validate(deadline)?;
        Ok([
            self.instance.store.path().join("version.json"),
            self.instance.helper.clone(),
        ])
    }
    /// Reconstitute only fresh-entry inherited originals. Every native check
    /// below is mandatory; no supplied process/record/digest is accepted.
    ///
    /// # Safety
    /// The native launcher exclusively transferred this ordered, disjoint set
    /// to this fresh child. Snapshot every slot before any allocator/importer;
    /// no intervening code may close/reuse it. The caller owns every FD exactly
    /// once and has set CLOEXEC before callbacks, threads or another exec.
    pub unsafe fn from_inherited_control(
        originals: [OwnedFd; ORIGINAL_CONTROL_DESCRIPTORS],
        deadline: Instant,
    ) -> io::Result<Self> {
        Self::import_control(originals, deadline)
    }
    /// An already authenticated original pin may verify a complete native
    /// transfer against ITSELF. Neither numbers nor a decoded Record can
    /// supply that expected owner; all received FD/content checks still run.
    pub fn receive_original_control(
        &self,
        originals: [OwnedFd; ORIGINAL_CONTROL_DESCRIPTORS],
        deadline: Instant,
    ) -> io::Result<Self> {
        self.validate(deadline)?;
        let received = Self::import_control(originals, deadline)?;
        if received.identity != self.identity
            || received.helper_path() != self.helper_path()
            || received.socket_path() != self.socket_path()
            || identity(&received.image.before) != identity(&self.image.before)
            || !same_file(&received.instance.store.0.root, &self.instance.store.0.root)?
        {
            return Err(refused(
                "received control differs from the actual original pin",
            ));
        }
        self.validate(deadline)?;
        Ok(received)
    }
    fn import_control(
        originals: [OwnedFd; ORIGINAL_CONTROL_DESCRIPTORS],
        deadline: Instant,
    ) -> io::Result<Self> {
        expired(deadline)?;
        let [
            root,
            images,
            instances,
            version,
            lock,
            executable,
            directory,
            socket_parent,
            anchor,
        ] = originals;
        let anchor = UnixStream::from(anchor);
        let native = process::connected_identity(&anchor)?;
        let own = process::read_identity(std::process::id())?;
        if !process::stable_ancestor(native, own, deadline)? {
            return Err(refused("inherited control peer is not an actual ancestor"));
        }
        let [
            root,
            images,
            instances,
            version,
            lock,
            file,
            directory,
            socket_parent,
        ] = [
            root,
            images,
            instances,
            version,
            lock,
            executable,
            directory,
            socket_parent,
        ]
        .map(File::from);
        for original in [
            &root,
            &images,
            &instances,
            &version,
            &lock,
            &file,
            &directory,
            &socket_parent,
        ] {
            let flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) };
            let fdflags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFD) };
            if flags < 0
                || fdflags < 0
                || flags & libc::O_ACCMODE != libc::O_RDONLY
                || fdflags & libc::FD_CLOEXEC == 0
            {
                return Err(refused(
                    "inherited control original is not read-only CLOEXEC",
                ));
            }
        }
        let path = original_path(root.as_fd())?;
        let helper = original_path(file.as_fd())?;
        let image_directory = original_path(directory.as_fd())?;
        let digest = image_directory
            .file_name()
            .and_then(OsStr::to_str)
            .filter(|value| crate::schema::digest_shaped(value))
            .ok_or_else(|| refused("inherited image has no canonical content name"))?
            .to_owned();
        if image_directory != path.join("images").join(&digest)
            || helper != image_directory.join("aterm")
            || original_path(images.as_fd())? != path.join("images")
            || original_path(instances.as_fd())? != path.join("instances")
            || original_path(version.as_fd())? != path.join("version.json")
            || original_path(lock.as_fd())? != path.join("lock")
        {
            return Err(refused(
                "inherited control originals do not share the selected store",
            ));
        }
        let socket = anchor
            .peer_addr()?
            .as_pathname()
            .ok_or_else(|| refused("inherited control anchor has no named peer"))?
            .to_owned();
        if original_path(socket_parent.as_fd())?
            != socket
                .parent()
                .ok_or_else(|| refused("inherited control socket has no parent"))?
        {
            return Err(refused("inherited control socket parent differs"));
        }
        let store = Store(Arc::new(Backing {
            path,
            root,
            images,
            instances,
            version,
            lock,
        }));
        store.check()?;
        private::owned(&file, false)?;
        private::owned(&directory, true)?;
        let before = file.metadata()?;
        let directory_before = directory.metadata()?;
        if before.mode() & 0o7777 != 0o500
            || directory_before.mode() & 0o7777 != 0o500
            || before.len() == 0
            || before.len() > image_pin::MAX_IMAGE
        {
            return Err(refused("invalid inherited immutable image"));
        }
        // Preserve the initial content check on the SAME held file. Positioned
        // reads never change the exporter/another child's shared file offset.
        let mut hash = sha2::Sha256::new();
        let mut offset = 0u64;
        let mut bytes = [0; 65536];
        use sha2::Digest as _;
        loop {
            expired(deadline)?;
            let count = file.read_at(&mut bytes, offset)?;
            if count == 0 {
                break;
            }
            offset = offset
                .checked_add(count as u64)
                .filter(|value| *value <= image_pin::MAX_IMAGE)
                .ok_or_else(|| refused("inherited image size exceeds bound"))?;
            hash.update(&bytes[..count]);
        }
        if offset != before.len()
            || hex(&hash.finalize()) != digest
            || private::stamp(&before) != private::stamp(&file.metadata()?)
        {
            return Err(refused("inherited immutable image content changed"));
        }
        let (host, boot) = process::host_boot()?;
        let record = Record {
            pid: native.pid,
            birth: native.birth,
            host,
            boot,
            digest,
            image: identity(&before),
            directory: identity(&directory_before),
            socket_hex: hex(socket.as_os_str().as_bytes()),
            socket: identity(&fs::symlink_metadata(&socket)?),
        };
        process::check_peer(&anchor, native)?;
        let pin = Self {
            instance: Instance {
                store,
                record,
                helper,
                socket,
            },
            identity: native,
            image: Arc::new(Image {
                file,
                before,
                directory,
                directory_before,
            }),
            socket_parent: Arc::new(socket_parent),
            control_anchor: Some(Arc::new(anchor)),
        };
        pin.validate(deadline)?;
        expired(deadline)?;
        Ok(pin)
    }
}
impl Store {
    /// The Host may retain its own published listener pin before spawning any
    /// target. An actual listening socket and current native image are needed;
    /// a path, book row or self-PID is insufficient.
    pub fn pin_current_listener(
        &self,
        listener: BorrowedFd<'_>,
        deadline: Instant,
    ) -> io::Result<PinnedHelper> {
        let before = listener_stamp(listener)?;
        let listener = UnixListener::from(listener.try_clone_to_owned()?);
        let address = listener.local_addr()?;
        let path = address
            .as_pathname()
            .ok_or_else(|| refused("control listener is unnamed"))?;
        let native = process::read_identity(std::process::id())?;
        let mut selected = None;
        for instance in self.instances()? {
            if instance.pid() == native.pid
                && instance.birth() == native.birth
                && instance.socket_path() == path
            {
                if selected.is_some() {
                    return Err(refused("ambiguous current control listener"));
                }
                selected = Some(
                    instance
                        .connect_ancestor(deadline)?
                        .ok_or_else(|| refused("current control listener is not native"))?
                        .into_helper(deadline)?,
                );
            }
        }
        if before != listener_stamp(listener.as_fd())? {
            return Err(refused("control original listener changed during pinning"));
        }
        selected.ok_or_else(|| refused("current control listener is not published"))
    }
}

#[cfg(target_os = "macos")]
fn listener_stamp(fd: BorrowedFd<'_>) -> io::Result<(u64, u64)> {
    // Darwin declares SO_ACCEPTCONN but does NOT implement that getsockopt
    // (XNU sogetoptlock). Observe actual SAME-FD socket options instead. Layout
    // is the maintained aterm-sysprobe jobs::darwin socket_fdinfo (792 bytes),
    // sys/proc_info.h: soi_type176/family184/options188/kind256. Full reads only.
    let mut bytes = [0u8; 792];
    let count = unsafe {
        libc::proc_pidfdinfo(
            std::process::id() as i32,
            fd.as_raw_fd(),
            3,
            bytes.as_mut_ptr().cast(),
            bytes.len() as i32,
        )
    };
    if count != bytes.len() as i32 {
        return Err(refused(
            "complete native control listener observation unavailable",
        ));
    }
    let int = |at| i32::from_ne_bytes(bytes[at..at + 4].try_into().unwrap());
    let options = u16::from_ne_bytes(bytes[188..190].try_into().unwrap());
    let socket = u64::from_ne_bytes(bytes[160..168].try_into().unwrap());
    let pcb = u64::from_ne_bytes(bytes[168..176].try_into().unwrap());
    if int(176) != libc::SOCK_STREAM
        || int(184) != libc::AF_UNIX
        || int(256) != 3
        || options & 0x2 == 0
        || socket == 0
        || pcb == 0
    {
        return Err(refused(
            "control original is not an actual listening Unix stream",
        ));
    }
    Ok((socket, pcb))
}
#[cfg(target_os = "linux")]
fn listener_stamp(fd: BorrowedFd<'_>) -> io::Result<(u64, u64)> {
    let mut accepts = 0i32;
    let mut length = std::mem::size_of::<i32>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            fd.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_ACCEPTCONN,
            (&raw mut accepts).cast(),
            &mut length,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    if accepts != 1 || length as usize != std::mem::size_of::<i32>() {
        return Err(refused("control original is not an actual listener"));
    }
    let mut stat: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstat(fd.as_raw_fd(), &mut stat) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok((stat.st_dev, stat.st_ino))
}
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn listener_stamp(_: BorrowedFd<'_>) -> io::Result<(u64, u64)> {
    Err(io::ErrorKind::Unsupported.into())
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn original_path(fd: BorrowedFd<'_>) -> io::Result<PathBuf> {
    #[cfg(target_os = "macos")]
    let path = {
        let mut bytes = [0u8; 4096];
        if unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETPATH, bytes.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let end = bytes
            .iter()
            .position(|byte| *byte == 0)
            .ok_or_else(|| refused("unbounded original control path"))?;
        PathBuf::from(std::ffi::OsString::from_vec(bytes[..end].to_vec()))
    };
    #[cfg(target_os = "linux")]
    let path = fs::read_link(format!("/proc/self/fd/{}", fd.as_raw_fd()))?;
    if !path.is_absolute() || path.as_os_str().as_bytes().len() > 4096 {
        return Err(refused("invalid original control path"));
    }
    Ok(path)
}
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn original_path(_: BorrowedFd<'_>) -> io::Result<PathBuf> {
    Err(io::ErrorKind::Unsupported.into())
}
