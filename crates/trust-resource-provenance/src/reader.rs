// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::ffi::OsStr;
use std::fs::{self, File, Metadata};
use std::io::{self, Read};
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

#[cfg(test)]
use sha2::{Digest, Sha256};

use crate::private::{self, identity};
use crate::process::{self, Identity, Presence};
use crate::schema::{Book, MAX_JSON, Record, hex, refused};

mod image_pin;
pub use image_pin::PinnedProgram;
mod control;
pub use control::{HostControlTransfer, ORIGINAL_CONTROL_DESCRIPTORS};

#[derive(Debug)]
struct Backing {
    path: PathBuf,
    root: File,
    images: File,
    instances: File,
    version: File,
    lock: File,
}

/// Existing private account state, pinned by original open directory/file handles.
#[derive(Clone, Debug)]
pub struct Store(Arc<Backing>);

/// A book row; validation is mandatory before using its helper or endpoint.
#[derive(Clone, Debug)]
pub struct Instance {
    store: Store,
    record: Record,
    helper: PathBuf,
    socket: PathBuf,
}

#[derive(Debug)]
struct Image {
    file: File,
    before: Metadata,
    directory: File,
    directory_before: Metadata,
}

/// A connected native ancestor with pinned image and socket identities.
///
/// The connection must remain open through post-response validation and the
/// protocol's ACK. Dropping this value confers no release or closure authority.
#[derive(Debug)]
pub struct Host {
    instance: Instance,
    identity: Identity,
    image: Arc<Image>,
    socket_parent: Arc<File>,
    stream: UnixStream,
    control_anchor: Option<Arc<UnixStream>>,
}

/// An immutable helper selected through an actual native ancestor connection.
/// The discovery stream has been closed; every spawn still validates original
/// backing and actual loaded child identity before private data is delivered.
#[derive(Debug)]
pub struct PinnedHelper {
    instance: Instance,
    identity: Identity,
    image: Arc<Image>,
    socket_parent: Arc<File>,
    // Imported control originals retain their SAME native socket too. Ordinary
    // discovered pins have only the existing eight-backing profile.
    control_anchor: Option<Arc<UnixStream>>,
}

fn same_file(actual: &File, original: &File) -> io::Result<bool> {
    Ok(identity(&actual.metadata()?) == identity(&original.metadata()?))
}
fn expired(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
impl Store {
    /// Resolve the native account database home; environment paths grant no authority.
    pub fn account_path() -> io::Result<PathBuf> {
        #[cfg(target_os = "macos")]
        let suffix = "Library/Caches/aterm/resource-host-v3.noindex";
        #[cfg(not(target_os = "macos"))]
        let suffix = ".cache/aterm/resource-host-v3.noindex";
        Ok(process::account_home()?.join(suffix))
    }
    pub fn open_account() -> io::Result<Self> {
        Self::open_at(&Self::account_path()?)
    }
    /// Open existing state only. Nothing creates, repairs or retires a namespace.
    pub fn open_at(path: &Path) -> io::Result<Self> {
        let root = private::directory(path)?;
        let images = private::directory(&path.join("images"))?;
        let instances = private::directory(&path.join("instances"))?;
        let version = private::open_private(&root, OsStr::new("version.json"))?;
        let lock = private::open_private(&root, OsStr::new("lock"))?;
        let store = Self(Arc::new(Backing {
            path: path.to_owned(),
            root,
            images,
            instances,
            version,
            lock,
        }));
        store.check()?;
        store.book()?;
        Ok(store)
    }
    /// The pinned canonical location; this pathname alone grants no authority.
    pub fn path(&self) -> &Path {
        &self.0.path
    }
    /// Compare this reader's OWN original directory to an independently held
    /// descriptor. This is an identity observation, not path validation,
    /// discovery or a resource grant. No descriptor escapes the reader.
    pub fn same_original_directory(
        &self,
        original: std::os::fd::BorrowedFd<'_>,
    ) -> io::Result<bool> {
        let file = File::from(original.try_clone_to_owned()?);
        if !file.metadata()?.is_dir() {
            return Ok(false);
        }
        same_file(&self.0.root, &file)
    }
    /// Validate the original structural backing without creating or repairing it.
    pub fn validate(&self) -> io::Result<()> {
        self.check()
    }
    fn check(&self) -> io::Result<()> {
        let backing = &self.0;
        for (path, held) in [
            (&backing.path, &backing.root),
            (&backing.path.join("images"), &backing.images),
            (&backing.path.join("instances"), &backing.instances),
        ] {
            private::named_directory(path, held)?;
        }
        private::named_file(&backing.path.join("version.json"), &backing.version)?;
        let version = private::read_original(&backing.version, 64)?;
        if version != b"{\"version\":1}" {
            return Err(refused("provenance version changed"));
        }
        private::named_file(&backing.path.join("lock"), &backing.lock)?;
        if backing.lock.metadata()?.len() != 0 {
            return Err(refused("provenance lock changed"));
        }
        Ok(())
    }
    pub fn book(&self) -> io::Result<Book> {
        self.check()?;
        let (bytes, _) =
            private::read_private(&self.0.instances, OsStr::new("book.json"), MAX_JSON)?;
        let book = Book::decode(&bytes)?;
        self.check()?;
        Ok(book)
    }
    pub fn instances(&self) -> io::Result<Vec<Instance>> {
        self.book()?
            .instances
            .into_iter()
            .map(|record| {
                let socket = record.socket_path()?;
                let helper = self.0.path.join("images").join(&record.digest).join("aterm");
                Ok(Instance { store: self.clone(), record, helper, socket })
            })
            .collect()
    }
    /// Find exactly one actual connected ancestor. Unknown/partial backing is a
    /// refusal, never an absent row or zero resource reservation.
    pub fn connect_ancestor(&self, deadline: Instant) -> io::Result<Host> {
        let mut selected = None;
        for instance in self.instances()? {
            expired(deadline)?;
            if instance.proven_stale() {
                continue;
            }
            if let Some(host) = instance.connect_ancestor(deadline)?
                && selected.replace(host).is_some()
            {
                return Err(refused("ambiguous native custodian ancestors"));
            }
        }
        selected.ok_or_else(|| refused("native custodian ancestor unavailable"))
    }
}
impl Instance {
    pub fn pid(&self) -> u32 {
        self.record.pid
    }
    pub fn birth(&self) -> u64 {
        self.record.birth
    }
    pub fn helper_path(&self) -> &Path {
        &self.helper
    }
    pub fn socket_path(&self) -> &Path {
        &self.socket
    }
    fn proven_stale(&self) -> bool {
        if process::presence(self.pid()) == Presence::Absent {
            return true;
        }
        let before = process::read_identity(self.pid()).ok();
        before.is_some_and(|old| old.birth != self.birth())
            && process::read_identity(self.pid()).ok() == before
    }
    fn image_ref(&self) -> image_pin::ImageRef<'_> {
        image_pin::ImageRef {
            store: &self.store,
            path: &self.helper,
            digest: &self.record.digest,
            image: self.record.image,
            directory: self.record.directory,
        }
    }
    fn open_image(&self, deadline: Instant) -> io::Result<Image> {
        self.image_ref().open(deadline)
    }
    fn check_image(&self, image: &Image) -> io::Result<()> {
        self.image_ref().check(image)
    }
    /// Connect as the actual caller; the live kernel peer proves endpoint ownership.
    pub fn connect_ancestor(&self, deadline: Instant) -> io::Result<Option<Host>> {
        expired(deadline)?;
        let image = self.open_image(deadline)?;
        if process::host_boot()? != (self.record.host.clone(), self.record.boot.clone()) {
            return Err(refused("custodian host or boot changed"));
        }
        let native = process::read_identity(self.pid())?;
        if native.birth != self.birth()
            || !process::image_matches(native, &image.file, &self.helper)?
        {
            return Err(refused("custodian no longer executes cached helper"));
        }
        let socket_parent = private::directory(
            self.socket.parent().ok_or_else(|| refused("socket parent missing"))?,
        )?;
        self.check_socket(&socket_parent)?;
        let stream = crate::connection::connect(&self.socket, deadline)?;
        process::check_peer(&stream, native)?;
        let host = Host {
            instance: self.clone(),
            identity: native,
            image: Arc::new(image),
            socket_parent: Arc::new(socket_parent),
            stream,
            control_anchor: None,
        };
        host.instance.check_socket(&host.socket_parent)?;
        let own = process::read_identity(std::process::id())?;
        if !process::stable_ancestor(native, own, deadline)? {
            return Ok(None);
        }
        host.revalidate(deadline)?;
        Ok(Some(host))
    }
    fn check_socket(&self, original_parent: &File) -> io::Result<()> {
        private::named_directory(
            self.socket.parent().ok_or_else(|| refused("socket parent missing"))?,
            original_parent,
        )?;
        let meta = fs::symlink_metadata(&self.socket)?;
        // SAFETY: geteuid reads only the current effective account identity.
        if !meta.file_type().is_socket()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.nlink() != 1
            || meta.mode() & 0o7077 != 0
            || identity(&meta) != self.record.socket
        {
            return Err(refused("native socket backing changed"));
        }
        Ok(())
    }
}
impl Host {
    /// Keep original image/host backing while dropping the unused pre-HELLO
    /// connection. The helper reconnects independently for its actual operation.
    pub fn into_helper(self, deadline: Instant) -> io::Result<PinnedHelper> {
        self.into_helper_preserving(deadline).map_err(|original| {
            let (_original, error) = *original;
            error
        })
    }
    /// Consume this actual connection into its SAME opaque original pin after
    /// native validation. Failure returns the original owner, never a pin made
    /// from a saved process identity, descriptor number or decoded observation.
    /// Closing the connection confers no execution or resource-return authority.
    pub fn into_helper_preserving(
        self,
        deadline: Instant,
    ) -> Result<PinnedHelper, Box<(Self, io::Error)>> {
        if let Err(error) = self.revalidate(deadline) {
            return Err(Box::new((self, error)));
        }
        Ok(PinnedHelper {
            instance: self.instance,
            identity: self.identity,
            image: self.image,
            socket_parent: self.socket_parent,
            control_anchor: self.control_anchor,
        })
    }
    pub fn pid(&self) -> u32 {
        self.identity.pid
    }
    pub fn birth(&self) -> u64 {
        self.identity.birth
    }
    pub fn helper_path(&self) -> &Path {
        self.instance.helper_path()
    }
    pub fn socket_path(&self) -> &Path {
        self.instance.socket_path()
    }
    pub fn stream(&self) -> &UnixStream {
        &self.stream
    }
    /// Recheck before/after a bounded reply, then send the host protocol ACK
    /// while this original connection remains alive. This grants no launch.
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        validate_native_host(
            &self.instance,
            self.identity,
            &self.image,
            &self.socket_parent,
            deadline,
        )?;
        check_control_anchor(self.control_anchor.as_deref(), &self.instance, self.identity)?;
        process::check_peer(&self.stream, self.identity)?;
        let own = process::read_identity(std::process::id())?;
        if !process::stable_ancestor(self.identity, own, deadline)? {
            return Err(refused("custodian is not actual ancestor"));
        }
        expired(deadline)
    }
}

fn validate_native_host(
    instance: &Instance,
    identity: Identity,
    image: &Image,
    socket_parent: &File,
    deadline: Instant,
) -> io::Result<()> {
    expired(deadline)?;
    instance.check_image(image)?;
    instance.check_socket(socket_parent)?;
    if process::host_boot()? != (instance.record.host.clone(), instance.record.boot.clone())
        || process::read_identity(identity.pid)? != identity
        || !process::image_matches(identity, &image.file, instance.helper_path())?
    {
        return Err(refused("native custodian changed"));
    }
    let own = process::read_identity(std::process::id())?;
    if !process::stable_ancestor(identity, own, deadline)? {
        return Err(refused("custodian is not actual ancestor"));
    }
    expired(deadline)
}
fn check_control_anchor(
    anchor: Option<&UnixStream>,
    instance: &Instance,
    native: Identity,
) -> io::Result<()> {
    if let Some(anchor) = anchor {
        process::check_peer(anchor, native)?;
        if anchor.peer_addr()?.as_pathname() != Some(instance.socket_path()) {
            return Err(refused("retained original control anchor endpoint changed"));
        }
    }
    Ok(())
}
impl PinnedHelper {
    /// Duplicate the SAME retained read-only store directory for this helper's
    /// child-only handoff. This neither selects another store nor grants any
    /// resource or execution authority. Every original pin check remains live.
    pub fn duplicate_original_store(&self, deadline: Instant) -> io::Result<std::os::fd::OwnedFd> {
        use std::os::fd::{AsRawFd as _, FromRawFd as _};
        self.validate(deadline)?;
        // SAFETY: duplicate our original held directory to a fresh slot;
        // stdio and the fixed SDK slot are never replaced or exposed.
        let raw = unsafe {
            libc::fcntl(self.instance.store.0.root.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 6)
        };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful F_DUPFD_CLOEXEC transferred this fresh descriptor.
        let owned = unsafe { std::os::fd::OwnedFd::from_raw_fd(raw) };
        self.validate(deadline)?;
        Ok(owned)
    }
    /// Original independently selected location retained by this helper pin.
    /// Equality/diagnostic data only; this does not revalidate backing or
    /// authorize discovery, a different controller, resources or execution.
    pub fn original_store_path(&self) -> &Path {
        self.instance.store.path()
    }
    pub fn helper_path(&self) -> &Path {
        self.instance.helper_path()
    }
    pub fn socket_path(&self) -> &Path {
        self.instance.socket_path()
    }
    pub fn host_pid(&self) -> u32 {
        self.identity.pid
    }
    pub fn host_birth(&self) -> u64 {
        self.identity.birth
    }
    /// Fresh native process/image/boot/ancestry and original backing checks.
    /// This does not inspect claims or confer admission authority.
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        validate_native_host(
            &self.instance,
            self.identity,
            &self.image,
            &self.socket_parent,
            deadline,
        )?;
        check_control_anchor(self.control_anchor.as_deref(), &self.instance, self.identity)?;
        expired(deadline)
    }
    /// Reconnect as the actual native caller using the ORIGINAL verified image
    /// handles. This never rehashes or reselects a different book row. Retain
    /// the Host through post-response revalidation and the protocol ACK.
    pub fn connect(&self, deadline: Instant) -> io::Result<Host> {
        self.validate(deadline)?;
        let stream = crate::connection::connect(self.socket_path(), deadline)?;
        let host = Host {
            instance: self.instance.clone(),
            identity: self.identity,
            // Share the SAME original held descriptions, not one duplicate
            // image/directory set per accepted operation. Validation below
            // still checks every actual connection and original backing.
            image: Arc::clone(&self.image),
            socket_parent: Arc::clone(&self.socket_parent),
            stream,
            control_anchor: self.control_anchor.clone(),
        };
        host.revalidate(deadline)?;
        Ok(host)
    }
    /// Check an actual held, unreaped helper child against the ORIGINAL cached
    /// image before sending any capability-bearing request. The caller must
    /// retain this Child for helper health; a target is never represented by it.
    pub fn validate_child(
        &self,
        child: &std::process::Child,
        deadline: Instant,
    ) -> io::Result<Identity> {
        self.validate(deadline)?;
        let own = process::read_identity(std::process::id())?;
        let native = process::read_identity(child.id())?;
        if native.parent != own.pid
            || (cfg!(target_os = "macos") && native.parent_unique_id != own.unique_id)
            || !process::image_matches(native, &self.image.file, self.helper_path())?
            || process::read_identity(std::process::id())? != own
            || process::read_identity(child.id())? != native
        {
            return Err(refused("helper is not the original image and direct owned child"));
        }
        self.validate(deadline)?;
        Ok(native)
    }
}

#[cfg(test)]
#[path = "reader/tests.rs"]
mod tests;
