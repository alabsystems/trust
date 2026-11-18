// Trust: recover the same scheduling pipe after an unaware build-script spawn.
// The pathname and environment are inert advertisements. A live ancestral
// owner, a per-pool capability and a fresh connected-socket exchange bind the
// transfer. This grants scheduling access only, never compiler/proof authority.

#[path = "handoff_process.rs"]
mod process;

#[cfg(test)]
#[path = "tests/handoff.rs"]
pub(crate) mod tests;

#[cfg(test)]
#[path = "tests/scoped_handoff.rs"]
mod scoped_tests;

#[cfg(test)]
#[path = "tests/fixed_handoff.rs"]
mod fixed_tests;

use std::ffi::{OsStr, OsString};
use std::io::{self, Read, Write};
use std::mem::{size_of, size_of_val};
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex, MutexGuard, Once, PoisonError, TryLockError};

#[path = "handoff_scoped.rs"]
mod scoped;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use process::{Process, ancestry, ensure_chain};
pub use scoped::ScopedHandoff;

pub(super) const ENV: &str = super::DESCENDANT_HANDOFF_ENV;
const MAGIC: &[u8; 8] = b"TJSCHED1";
const NAMED_FIFO_MAGIC: &[u8; 8] = b"TGNUNAM1";
const CPU_MAGIC: &[u8; 8] = b"TCPULEA1";
const CPU_BUNDLE_MAGIC: &[u8; 8] = b"TCPUBND2";
const MAX_CPU_FILES: usize = 128;
const FIXED_CLAIM_MAGIC: &[u8; 8] = b"TFIXCLM1";
const FIXED_OUTPUT_MAGIC: &[u8; 8] = b"TFIXOUT2";
// Complete original fixed claim: 65536 slots, worktree, admission and packet.
// Each actual SCM message stays within the existing 128-rights transport bound.
const MAX_FIXED_FILES: usize = 65_539;
const FIXED_FILES_PER_MESSAGE: usize = 128;

#[derive(Clone, Copy)]
enum Role {
    Jobserver,
    NamedFifo,
    CpuLease,
    CpuBundle,
    FixedClaim,
    FixedOutput,
}

impl Role {
    fn version(self) -> &'static str {
        match self {
            Self::CpuBundle => "cpu2",
            Self::NamedFifo => "fifo1",
            Self::FixedClaim => "fixed1",
            Self::FixedOutput => "fixed2",
            _ => "v1",
        }
    }
    fn magic(self) -> &'static [u8; 8] {
        match self {
            Self::Jobserver => MAGIC,
            Self::NamedFifo => NAMED_FIFO_MAGIC,
            Self::CpuLease => CPU_MAGIC,
            Self::CpuBundle => CPU_BUNDLE_MAGIC,
            Self::FixedClaim => FIXED_CLAIM_MAGIC,
            Self::FixedOutput => FIXED_OUTPUT_MAGIC,
        }
    }
    fn environment(self) -> &'static str {
        match self {
            Self::Jobserver | Self::NamedFifo => ENV,
            Self::CpuLease | Self::CpuBundle => super::CPU_HANDOFF_ENV,
            Self::FixedClaim | Self::FixedOutput => super::FIXED_CLAIM_HANDOFF_ENV,
        }
    }
}

const TIMEOUT: Duration = Duration::from_secs(2);
// XNU installs all rights before truncating ancillary copyout, so a small
// receive buffer can leak undisclosed descriptors despite closing its prefix.
// Its UIPC_MAX_CMSG_FD storage bound is 512 and sockargs further caps the
// control mbuf. This aligned capacity exceeds that complete rights message;
// it is receive storage only, never an increase to the exact-two protocol.
// https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/uipc_usrreq.c
// https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/uipc_syscalls.c
const ANCILLARY_BYTES: usize = 4096;

fn refused(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message)
}

// Trust (RL-64): a refused system call says what was being done and to which
// path. A bare `Permission denied (os error 13)` was Targo's whole error when
// its job-server folder could not be made. The kind is kept for callers.
fn naming<'a>(
    action: &'a str,
    path: &'a std::path::Path,
) -> impl FnOnce(io::Error) -> io::Error + 'a {
    move |error| {
        io::Error::new(error.kind(), format!("could not {action} {}: {error}", path.display()))
    }
}

fn timed_out() -> io::Error {
    io::Error::new(io::ErrorKind::TimedOut, "jobserver handoff deadline expired")
}

fn check_deadline(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(timed_out()) } else { Ok(()) }
}

fn ready(stream: &UnixStream, events: libc::c_short, deadline: Instant) -> io::Result<()> {
    loop {
        check_deadline(deadline)?;
        let remaining = deadline.saturating_duration_since(Instant::now());
        let timeout = remaining.as_millis().clamp(1, libc::c_int::MAX as u128) as libc::c_int;
        let mut fd = libc::pollfd { fd: stream.as_raw_fd(), events, revents: 0 };
        // SAFETY: one initialized pollfd is writable for this call.
        match unsafe { libc::poll(&mut fd, 1, timeout) } {
            0 => return Err(timed_out()),
            -1 if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted => continue,
            -1 => return Err(io::Error::last_os_error()),
            _ => return check_deadline(deadline),
        }
    }
}

fn read_frame(stream: &mut UnixStream, mut bytes: &mut [u8], deadline: Instant) -> io::Result<()> {
    while !bytes.is_empty() {
        check_deadline(deadline)?;
        match stream.read(bytes) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "incomplete jobserver handoff",
                ));
            }
            Ok(count) => bytes = &mut bytes[count..],
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                ready(stream, libc::POLLIN, deadline)?
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    check_deadline(deadline)
}

fn write_frame(stream: &mut UnixStream, mut bytes: &[u8], deadline: Instant) -> io::Result<()> {
    while !bytes.is_empty() {
        check_deadline(deadline)?;
        match stream.write(bytes) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "incomplete jobserver handoff",
                ));
            }
            Ok(count) => bytes = &bytes[count..],
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                ready(stream, libc::POLLOUT, deadline)?
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    check_deadline(deadline)
}

fn expect_end(stream: &mut UnixStream, deadline: Instant) -> io::Result<()> {
    loop {
        check_deadline(deadline)?;
        match stream.read(&mut [0]) {
            Ok(0) => return Ok(()),
            Ok(_) => return Err(refused("trailing jobserver handoff frame")),
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                ready(stream, libc::POLLIN, deadline)?
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
}

fn socket_address(path: &std::path::Path) -> io::Result<(libc::sockaddr_un, libc::socklen_t)> {
    let path = path.as_os_str().as_bytes();
    // SAFETY: zero initializes the sockaddr optional fields and path terminator.
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if path.is_empty() || path.len() >= address.sun_path.len() || path.contains(&0) {
        return Err(refused(&format!(
            "invalid jobserver endpoint pathname {}",
            std::path::Path::new(OsStr::from_bytes(path)).display()
        )));
    }
    address.sun_family = libc::AF_UNIX as _;
    for (output, byte) in address.sun_path.iter_mut().zip(path) {
        *output = *byte as _;
    }
    let length = std::mem::offset_of!(libc::sockaddr_un, sun_path) + path.len() + 1;
    #[cfg(target_os = "macos")]
    {
        address.sun_len = length as _;
    }
    Ok((address, length as _))
}

fn connect(path: &std::path::Path, deadline: Instant) -> io::Result<UnixStream> {
    let (address, length) = socket_address(path)?;
    // SAFETY: socket returns a newly owned fd or -1. No pathname open occurs.
    let fd = unsafe { libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: the successful socket call returned this new owned descriptor.
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    // SAFETY: set CLOEXEC on this newly owned descriptor before any spawn.
    if unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
        return Err(io::Error::last_os_error());
    }
    let stream = UnixStream::from(fd);
    stream.set_nonblocking(true)?;
    // SAFETY: address is initialized, fits the native ABI and remains alive.
    let result = unsafe {
        libc::connect(
            stream.as_raw_fd(),
            (&address as *const libc::sockaddr_un).cast(),
            length as _,
        )
    };
    if result != 0 {
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::EINPROGRESS) {
            // In particular, refuse a full AF_UNIX backlog (EAGAIN) promptly;
            // do not enter a blocking or unbounded connection retry loop.
            return Err(error);
        }
        ready(&stream, libc::POLLOUT, deadline)?;
        if let Some(error) = stream.take_error()? {
            return Err(error);
        }
    }
    check_deadline(deadline)?;
    Ok(stream)
}

fn random() -> io::Result<[u8; 32]> {
    let mut bytes = [0; 32];
    #[cfg(target_os = "macos")]
    // SAFETY: this writable buffer is below getentropy's 256-byte limit.
    if unsafe { libc::getentropy(bytes.as_mut_ptr().cast(), bytes.len()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    #[cfg(target_os = "linux")]
    {
        // Use the kernel interface without adding a newer glibc symbol. If
        // entropy or this optional interface is unavailable, the chosen pool
        // remains usable through its existing explicit descriptor transport.
        let mut filled = 0;
        while filled < bytes.len() {
            // SAFETY: the remaining writable buffer is valid for this syscall.
            let count = unsafe {
                libc::syscall(
                    libc::SYS_getrandom,
                    bytes[filled..].as_mut_ptr(),
                    bytes.len() - filled,
                    libc::GRND_NONBLOCK,
                )
            };
            if count > 0 {
                filled += count as usize;
            } else if count == 0 {
                return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "empty entropy response"));
            } else {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
    Ok(bytes)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(text: &str) -> io::Result<[u8; 32]> {
    let mut output = [0; 32];
    if text.len() != 64 || !text.is_ascii() {
        return Err(refused("invalid jobserver pool capability"));
    }
    for (index, byte) in output.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[index * 2..index * 2 + 2], 16)
            .map_err(|_| refused("invalid jobserver pool capability"))?;
    }
    Ok(output)
}

#[cfg(any(feature = "client", test))]
fn flags(pair: [libc::c_int; 2]) -> String {
    let [read, write] = pair;
    format!("-j --jobserver-fds={read},{write} --jobserver-auth={read},{write}")
}

struct Advertisement {
    owner: u32,
    birth: u64,
    pair: [libc::c_int; 2],
    capability: [u8; 32],
    path: PathBuf,
}

impl Advertisement {
    #[cfg(test)]
    fn encode(&self) -> OsString {
        self.encode_role(Role::Jobserver)
    }

    fn encode_role(&self, role: Role) -> OsString {
        let [read, write] = self.pair;
        let version = role.version();
        let mut bytes = format!(
            "{version}:{}:{}:{read},{write}:{}:",
            self.owner,
            self.birth,
            hex(&self.capability),
        )
        .into_bytes();
        bytes.extend_from_slice(self.path.as_os_str().as_bytes());
        OsString::from_vec(bytes)
    }

    fn parse(value: &OsStr) -> io::Result<Self> {
        Self::parse_role(value, Role::Jobserver)
    }

    fn parse_role(value: &OsStr, role: Role) -> io::Result<Self> {
        if value.len() > 4096 {
            return Err(refused("oversized jobserver handoff advertisement"));
        }
        let mut fields = value.as_bytes().splitn(6, |b| *b == b':');
        let mut field = || {
            std::str::from_utf8(fields.next().unwrap_or_default())
                .map_err(|_| refused("invalid jobserver handoff advertisement"))
        };
        let version = role.version();
        if field()? != version {
            return Err(refused("unsupported jobserver handoff advertisement"));
        }
        let owner = field()?.parse().map_err(|_| refused("invalid jobserver owner"))?;
        let birth = field()?.parse().map_err(|_| refused("invalid jobserver owner identity"))?;
        let (read, write) = field()?.split_once(',').ok_or_else(|| refused("invalid pool pair"))?;
        let pair = [
            read.parse().map_err(|_| refused("invalid pool read descriptor"))?,
            write.parse().map_err(|_| refused("invalid pool write descriptor"))?,
        ];
        let capability = unhex(field()?)?;
        let path = PathBuf::from(OsString::from_vec(fields.next().unwrap_or_default().to_vec()));
        if owner <= 1
            || birth == 0
            || if matches!(role, Role::NamedFifo) {
                pair != [2, 0]
            } else if matches!(role, Role::CpuBundle) {
                pair[0] < 1 || pair[0] as usize > MAX_CPU_FILES || pair[1] != 0
            } else if matches!(role, Role::FixedClaim) {
                pair[0] < 2 || pair[0] as usize > MAX_FIXED_FILES || pair[1] != 0
            } else if matches!(role, Role::FixedOutput) {
                pair[0] < 4 || pair[0] as usize > MAX_FIXED_FILES + 2 || pair[1] != 0
            } else {
                pair[0] <= 2 || pair[1] <= 2 || pair[0] == pair[1]
            }
            || !path.is_absolute()
        {
            return Err(refused("invalid jobserver handoff binding"));
        }
        Ok(Self { owner, birth, pair, capability, path })
    }
}

#[derive(Debug)]
struct Directory {
    path: PathBuf,
    file: std::fs::File,
    /// The marker, held open and locked while the folder lives.
    marker: Option<std::fs::File>,
}

// Trust (RL-64): removing an endpoint's folder cannot depend on a destructor.
// Targo parks its compiler-query scheduler in a static, rustc and targo-trust
// park theirs the same way, and a static is never dropped; `process::exit`
// drops nothing either. Each such process left one `tjs-<hex>` folder behind.
// Every live folder of this process is therefore also listed here, and one
// exit(3) handler removes what is still listed when the process ends.
struct LiveDirectory {
    /// The process that made the folder. A forked child inherits this list,
    /// and its own exit(3) must not remove its parent's folders.
    owner: libc::pid_t,
    /// Borrowed from the owning [`Directory`], which takes this entry out of
    /// the list, under the list's lock, before it closes the descriptor.
    descriptor: RawFd,
    path: PathBuf,
}

static LIVE_DIRECTORIES: Mutex<Vec<LiveDirectory>> = Mutex::new(Vec::new());
static EXIT_HANDLER: Once = Once::new();
/// One-millisecond attempts the exit path makes for the list's lock.
const EXIT_LOCK_ATTEMPTS: usize = 50;

// Trust (RL-65): a process ended by a signal runs no exit handler, so its
// folder stayed for good. The owner of a folder therefore proves through the
// kernel that it is alive, and every process that makes a folder first removes
// the dead ones beside it.
//
// The owner holds an exclusive flock on the folder's own descriptor. flock
// belongs to the open file description: the kernel releases it when the last
// descriptor of that description closes, which the death of the process by any
// signal does, and an exec too (the descriptor is close-on-exec). A forked
// child that keeps a copy keeps the folder alive, which errs on the safe side.
// The marker inside says the lock was taken, and was shown to exclude a second
// description of the folder, before the marker appeared. A folder without it
// is never swept: one from a pack before this change, one whose owner died
// before the marker, one on a filesystem that does not enforce flock.
//
// The lock proves an owner alive only to a sweeper that asks the kernel
// holding it, about the file it was taken on. Linux keeps flock on a folder of
// NFS, FUSE, 9p and overlayfs in the calling kernel alone (their directory
// operations have no `flock`, so `flock(2)` takes the local path): a second
// host, or a guest and its host, that share a temporary folder each see the
// other's live folders as unlocked, and so does one kernel that reaches a
// folder through a second file system laid over the first. The marker
// therefore holds where its lock lives (`liveness_record`): the kernel's
// identity for this boot and the folder's device and inode numbers as the
// owner's kernel reports them. A sweep removes a folder only when the marker
// holds the sweeper's own three values. A process that cannot read its
// kernel's identity makes no marker and sweeps nothing.
//
// Two kernels can report one identity (virtual machines resumed from one
// snapshot) and an NFS client gives every client of an export the same device
// and inode numbers, so the record alone can take another client's live owner
// for this kernel's. The owner therefore also holds an exclusive flock on the
// marker, a regular file, for as long as the folder lives, and a sweep leaves a
// folder whose marker refuses it a shared lock. Linux's NFS client takes flock
// on a regular file as a lock of the server's (unless mounted
// `local_lock=flock` or `all`), which every client sees. A file system that
// refuses the request itself leaves the folder's lock and the record to
// decide, as before.
//
// Processes built at different times meet over this lock, so it names its
// system call: std's `File::try_lock` is flock today by a choice std may change.
const LIVE_MARKER: &std::ffi::CStr = c"l";
/// The longest kernel identity a marker holds.
const KERNEL_IDENTITY_BYTES: usize = 64;
/// The most a marker holds: the identity, two 64-bit numbers in decimal, the
/// two spaces between them and the newline.
const MARKER_BYTES: usize = KERNEL_IDENTITY_BYTES + 1 + 20 + 1 + 20 + 1;
/// Entries of the parent one sweep reads, so that a temporary folder of any
/// size costs an endpoint a bounded listing. In a folder that holds more, the
/// names listed after these are not seen.
const SWEEP_ENTRIES: usize = 16_384;
/// Job-server folders one sweep opens, and so the most it removes. A killed
/// targo leaves one or two. This many removals cost about what the full
/// listing above does (docs/STATUS.md, "Job-server folder removal").
const SWEEP_FOLDERS: usize = 64;

fn live_directories() -> MutexGuard<'static, Vec<LiveDirectory>> {
    // No code panics while it holds this lock; a poisoned list is still exact.
    LIVE_DIRECTORIES.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The list for a process that is ending, which must not wait without bound.
fn live_directories_at_exit() -> Option<MutexGuard<'static, Vec<LiveDirectory>>> {
    for _ in 0..EXIT_LOCK_ATTEMPTS {
        match LIVE_DIRECTORIES.try_lock() {
            Ok(live) => return Some(live),
            Err(TryLockError::Poisoned(poisoned)) => return Some(poisoned.into_inner()),
            // Another thread adds or removes one entry, or runs this removal.
            // A forked child of a threaded process can instead inherit the
            // lock held by a thread it does not have, and would wait forever.
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(1)),
        }
    }
    None
}

/// Remove every job-server folder this process made and still holds.
///
/// exit(3) does this by itself. Call it before an end that runs no exit
/// handler: `_exit`, a signal raised to end the process the way its child
/// ended, or an exec that replaces this image. The endpoints stay valid
/// owners afterwards but can no longer be reached, so this is for a process
/// that is about to end or be replaced. A forked child's call removes nothing
/// its parent made. It never blocks for long and never panics: when the
/// list's lock cannot be had, the folders are left where they are.
pub fn remove_endpoint_directories() {
    let Some(mut live) = live_directories_at_exit() else { return };
    // SAFETY: getpid has no preconditions.
    let process = unsafe { libc::getpid() };
    // The lock is held across the removals: a `Directory` dropped on another
    // thread waits here before it closes a descriptor this loop may be using.
    for entry in live.drain(..) {
        if entry.owner == process {
            // SAFETY: an entry is listed only while its `Directory` holds this
            // descriptor open (see `LiveDirectory::descriptor`), and a
            // `Directory` that was leaked or parked never closes it.
            remove_owned(unsafe { BorrowedFd::borrow_raw(entry.descriptor) }, &entry.path, None);
        }
    }
}

extern "C" fn remove_endpoint_directories_at_exit() {
    // A panic must not cross into exit(3) or stop the handlers after this one.
    let _ = std::panic::catch_unwind(remove_endpoint_directories);
}

/// Remove the socket, the marker and then the folder, the first two named
/// through the folder's own descriptor. `marker`, the owner's open marker, is
/// closed straight before the marker's unlink: an NFS client would rename a
/// marker still open instead of removing it. Running it again for a folder
/// that is already gone does nothing.
fn remove_owned(directory: BorrowedFd<'_>, path: &std::path::Path, marker: Option<std::fs::File>) {
    // SAFETY: remove only the socket entry in the directory we own, even
    // when its advertised pathname was replaced or redirected by a peer.
    unsafe {
        libc::unlinkat(directory.as_raw_fd(), c"s".as_ptr(), 0);
    }
    // SAFETY: the descriptor stays open for this borrow, and `ManuallyDrop`
    // keeps this view of it from closing it.
    let file =
        std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(directory.as_raw_fd()) });
    let named_here = matches!(
        (file.metadata(), std::fs::symlink_metadata(path)),
        (Ok(owned), Ok(named))
            if named.is_dir() && owned.dev() == named.dev() && owned.ino() == named.ino()
    );
    // Trust (RL-65): the marker goes last, straight before the rmdir. A
    // process killed after the socket's unlink and before this one leaves a
    // folder a later sweep still recognises; one killed after this call leaves
    // an empty folder nothing recognises, a window of one system call.
    drop(marker);
    // SAFETY: as for the socket: only the entry in the directory we own.
    unsafe {
        libc::unlinkat(directory.as_raw_fd(), LIVE_MARKER.as_ptr(), 0);
    }
    if named_here {
        // rmdir does not follow a final symlink and cannot delete a
        // nonempty substituted directory. The removals above never
        // traverse this mutable pathname.
        if let Err(error) = std::fs::remove_dir(path)
            && error.raw_os_error() == Some(libc::ENOTEMPTY)
        {
            // Trust (RL-65): an entry this remover did not make keeps the
            // folder. On an NFS client the socket's unlink is such an entry
            // while the socket is still bound, as it is when an owner's exit
            // handler runs: the client renames it to `.nfs…` and removes that
            // only once the socket is closed. The lock is still held through
            // `directory`, so the marker made again here names it, and a
            // later sweep removes the folder once that entry has gone, where
            // without the marker nothing would ever recognise it.
            // Made for a later sweep, so not held: its lock goes here.
            drop(mark_live(&file));
        }
    }
}

fn open_folder(path: &std::path::Path) -> io::Result<std::fs::File> {
    std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
}

/// Try the lock that says a folder's owner is alive. `Ok(false)`: another open
/// file description holds it.
fn try_liveness_lock(directory: BorrowedFd<'_>) -> io::Result<bool> {
    // SAFETY: flock uses only the number of this borrowed, open descriptor.
    if unsafe { libc::flock(directory.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
        return Ok(true);
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::EWOULDBLOCK) { Ok(false) } else { Err(error) }
}

/// The running kernel's name for itself, new at each boot: Darwin's
/// `kern.bootsessionuuid`, Linux's `boot_id`. `None` when it cannot be read
/// or is not a name (empty, too long, other bytes than letters, digits and
/// `-`, or nothing but zeros).
fn kernel_identity() -> Option<Vec<u8>> {
    let identity = read_kernel_identity()?;
    is_kernel_identity(&identity).then_some(identity)
}

fn is_kernel_identity(identity: &[u8]) -> bool {
    (1..=KERNEL_IDENTITY_BYTES).contains(&identity.len())
        && identity.iter().all(|byte| byte.is_ascii_alphanumeric() || *byte == b'-')
        && identity.iter().any(|byte| !matches!(byte, b'0' | b'-'))
}

#[cfg(target_os = "macos")]
fn read_kernel_identity() -> Option<Vec<u8>> {
    let mut bytes = [0_u8; KERNEL_IDENTITY_BYTES + 1];
    let mut length = bytes.len();
    // SAFETY: the name is NUL-terminated, the buffer is writable for the
    // `length` bytes passed with it, and no new value is given.
    let read = unsafe {
        libc::sysctlbyname(
            c"kern.bootsessionuuid".as_ptr(),
            bytes.as_mut_ptr().cast(),
            &mut length,
            std::ptr::null_mut(),
            0,
        )
    };
    if read != 0 {
        return None;
    }
    // A string: the length the kernel reports counts its terminating NUL.
    let text = bytes.get(..length)?;
    Some(text.strip_suffix(&[0]).unwrap_or(text).to_vec())
}

#[cfg(target_os = "linux")]
fn read_kernel_identity() -> Option<Vec<u8>> {
    let mut bytes = Vec::new();
    std::fs::File::open("/proc/sys/kernel/random/boot_id")
        .ok()?
        .take(KERNEL_IDENTITY_BYTES as u64 + 2)
        .read_to_end(&mut bytes)
        .ok()?;
    Some(bytes.strip_suffix(b"\n").unwrap_or(&bytes).to_vec())
}

/// What a marker holds: where the owner's lock lives. `kernel` keeps the
/// lock, and `device` and `inode` are the locked folder as that kernel reports
/// it. Within one kernel a device number names one mounted file system and an
/// inode number one file of it, so equal records mean one lock table and one
/// entry in it.
fn liveness_record(kernel: &[u8], device: u64, inode: u64) -> Vec<u8> {
    let mut record = kernel.to_vec();
    record.extend_from_slice(format!(" {device} {inode}\n").as_bytes());
    record
}

/// Take the liveness lock on a new folder and, once this filesystem is shown
/// to enforce it, make the marker that says where the lock lives, and lock the
/// marker too. The marker's descriptor is returned: its lock lasts while it is
/// open. When any step fails, or this kernel's identity cannot be read, there
/// is no marker: the endpoint works as it did before and its folder is never
/// swept.
fn mark_live(directory: &std::fs::File) -> Option<std::fs::File> {
    let kernel = kernel_identity()?;
    if !matches!(try_liveness_lock(directory.as_fd()), Ok(true)) {
        return None;
    }
    // The proof: a second description of the same folder must be refused, as
    // a sweeper's will be. A filesystem that has no flock, or grants it twice,
    // gets no marker.
    // SAFETY: the folder's descriptor is open and `.` is NUL-terminated; a
    // successful openat returns a new descriptor owned here alone.
    let second = unsafe {
        libc::openat(
            directory.as_raw_fd(),
            c".".as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if second < 0 {
        return None;
    }
    // SAFETY: the successful openat above returned this descriptor's one owner.
    let second = unsafe { OwnedFd::from_raw_fd(second) };
    if !matches!(try_liveness_lock(second.as_fd()), Ok(false)) {
        return None;
    }
    drop(second);
    let folder = directory.metadata().ok()?;
    let record = liveness_record(&kernel, folder.dev(), folder.ino());
    // SAFETY: the marker is made in the directory we own, by a NUL-terminated
    // name.
    // Read and write: an NFS client refuses an exclusive flock through a
    // descriptor that cannot write.
    let marker = unsafe {
        libc::openat(
            directory.as_raw_fd(),
            LIVE_MARKER.as_ptr(),
            libc::O_RDWR | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        )
    };
    if marker < 0 {
        return None;
    }
    // SAFETY: the successful openat above returned this descriptor's one owner.
    let mut marker = unsafe { std::fs::File::from_raw_fd(marker) };
    // Before the record: a sweeper that finds the record finds the lock. A
    // file system that refuses it leaves the folder's lock and the record to
    // decide.
    let _ = try_liveness_lock(marker.as_fd());
    // A marker that does not hold the whole record equals no sweeper's, so
    // one seen before this write, or left by an owner killed before it, only
    // keeps its folder.
    if marker.write_all(&record).is_err() {
        // SAFETY: as for the socket: only the entry in the directory we own.
        unsafe {
            libc::unlinkat(directory.as_raw_fd(), LIVE_MARKER.as_ptr(), 0);
        }
        return None;
    }
    Some(marker)
}

/// `tjs-` and sixteen lowercase hexadecimal digits, as `new_scoped_resources`
/// names a folder.
fn is_folder_name(name: &[u8]) -> bool {
    name.len() == 20
        && name.starts_with(b"tjs-")
        && name[4..].iter().all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
}

/// The folder's marker, opened to read, when it is this user's regular file
/// and holds exactly `record`.
fn marker_holding(
    directory: BorrowedFd<'_>,
    user: libc::uid_t,
    record: &[u8],
) -> Option<std::fs::File> {
    // SAFETY: the descriptor is open and the name is NUL-terminated. A final
    // symlink is not followed, and a FIFO put there is not waited on.
    let marker = unsafe {
        libc::openat(
            directory.as_raw_fd(),
            LIVE_MARKER.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    };
    if marker < 0 {
        return None;
    }
    // SAFETY: the successful openat above returned this descriptor's one owner.
    let mut marker = unsafe { std::fs::File::from_raw_fd(marker) };
    let metadata = marker.metadata().ok()?;
    if !metadata.is_file() || metadata.uid() != user {
        return None;
    }
    // One read, with room for one byte more than any record: a marker that is
    // shorter, longer or still being written is not this record.
    let mut bytes = [0_u8; MARKER_BYTES + 1];
    matches!(marker.read(&mut bytes), Ok(count) if bytes[..count] == *record).then_some(marker)
}

/// A shared flock on `file`, without waiting: `Ok(false)` when an exclusive
/// lock of another description refuses it.
fn try_shared_lock(file: BorrowedFd<'_>) -> io::Result<bool> {
    // SAFETY: flock uses only the number of this borrowed, open descriptor.
    if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_SH | libc::LOCK_NB) } == 0 {
        return Ok(true);
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::EWOULDBLOCK) { Ok(false) } else { Err(error) }
}

/// The folder at `path`, opened and locked, when it is one this user's
/// process made and marked under the kernel `kernel` and no live owner holds
/// it.
fn stale_folder(path: &std::path::Path, user: libc::uid_t, kernel: &[u8]) -> Option<std::fs::File> {
    let directory = open_folder(path).ok()?;
    let metadata = directory.metadata().ok()?;
    if !metadata.is_dir() || metadata.uid() != user || metadata.mode() & 0o777 != 0o700 {
        return None;
    }
    // The marker must say that this kernel keeps the lock on this very
    // folder: only then does the lock below ask the owner's lock table.
    let record = liveness_record(kernel, metadata.dev(), metadata.ino());
    let marker = marker_holding(directory.as_fd(), user, &record)?;
    // Last, and only for a marked folder: a folder still being made has no
    // marker yet, so this lock never meets its owner's first attempt.
    if !matches!(try_liveness_lock(directory.as_fd()), Ok(true)) {
        return None;
    }
    // Then the marker's own lock, which an owner under another kernel holds
    // where the folder's lock is that kernel's alone. Shared, through the
    // descriptor the record was read from: an NFS client grants a shared lock
    // through a descriptor that only reads, and a read open, unlike a write
    // one, does not break the read delegation the server may have given
    // another client for the marker. A file system that refuses the request
    // itself leaves the decision to the locks and the record above. A lock
    // granted here goes when `marker` closes, before any removal.
    if matches!(try_shared_lock(marker.as_fd()), Ok(false)) {
        return None;
    }
    Some(directory)
}

/// Remove the marked folders in `parent` whose owners are gone. Every failure
/// skips its folder: the sweep returns no error and its lock attempts never
/// wait. No process table is read and no socket is connected to: the lock
/// alone says an owner is alive. Its other calls are a listing and, for a
/// matching name, the opens, fstats and one read of `stale_folder`. The open
/// of a name can wait where another user serves a file system mounted under
/// it (docs/OPEN_ISSUES.md TARGO-JOBSERVER-SWEEP-SHARED-1).
fn sweep_stale_folders(parent: &std::path::Path, rotation: usize) {
    let Ok(listing) = std::fs::read_dir(parent) else { return };
    let names: Vec<OsString> = listing
        .take(SWEEP_ENTRIES)
        .map_while(Result::ok)
        .map(|entry| entry.file_name())
        .filter(|name| is_folder_name(name.as_bytes()))
        .collect();
    if names.is_empty() {
        return;
    }
    // A sweeper that cannot name its kernel cannot tell whose lock a marker
    // speaks of, and removes nothing.
    let Some(kernel) = kernel_identity() else { return };
    // SAFETY: geteuid has no preconditions.
    let user = unsafe { libc::geteuid() };
    // The listing's order is the filesystem's and does not change between
    // calls. Starting somewhere else each time, more folders than one call
    // opens (those of earlier packs are never removed) cannot hide a stale one.
    let first = rotation % names.len();
    for name in names.iter().cycle().skip(first).take(names.len().min(SWEEP_FOLDERS)) {
        let path = parent.join(name);
        if let Some(directory) = stale_folder(&path, user, &kernel) {
            remove_owned(directory.as_fd(), &path, None);
        }
    }
}

impl Directory {
    /// Make the private folder, open it, lock and mark it as live, and list it
    /// for removal at exit.
    fn create(path: PathBuf) -> io::Result<Self> {
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&path)
            .map_err(naming("create the job-server folder", &path))?;
        let file = open_folder(&path).map_err(|error| {
            // Nothing was put in the folder made above, and no `Directory`
            // exists yet to remove it. rmdir removes only an empty
            // directory and does not follow a final symlink.
            let _ = std::fs::remove_dir(&path);
            naming("open the job-server folder", &path)(error)
        })?;
        let marker = mark_live(&file);
        EXIT_HANDLER.call_once(|| {
            // SAFETY: the handler is a function of this image, which exit(3)
            // may call once. Without it, removal is left to `Drop` alone.
            unsafe {
                libc::atexit(remove_endpoint_directories_at_exit);
            }
        });
        // SAFETY: getpid has no preconditions.
        let owner = unsafe { libc::getpid() };
        live_directories().push(LiveDirectory {
            owner,
            descriptor: file.as_raw_fd(),
            path: path.clone(),
        });
        Ok(Self { path, file, marker })
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        // First, so that the list never holds a descriptor that was closed.
        // This waits for the lock: giving up would leave the number of a
        // closed descriptor listed for the exit handler to use.
        let descriptor = self.file.as_raw_fd();
        live_directories().retain(|live| live.descriptor != descriptor);
        remove_owned(self.file.as_fd(), &self.path, self.marker.take());
    }
}

#[derive(PartialEq, Eq)]
struct FileIdentity(libc::dev_t, libc::ino_t);

impl FileIdentity {
    fn read(fd: &OwnedFd) -> io::Result<Self> {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: fd is owned and stat has room for the complete kernel result.
        if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: fstat initialized the whole value on success.
        let stat = unsafe { stat.assume_init() };
        Ok(Self(stat.st_dev, stat.st_ino))
    }
}

fn validate_cpu_file(fd: &OwnedFd) -> io::Result<()> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: owned descriptor and writable complete stat storage.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: the successful fstat initialized this value.
    let stat = unsafe { stat.assume_init() };
    // SAFETY: geteuid has no arguments; F_GETFL only observes the owned descriptor.
    let (uid, flags) = unsafe { (libc::geteuid(), libc::fcntl(fd.as_raw_fd(), libc::F_GETFL)) };
    if stat.st_mode & libc::S_IFMT != libc::S_IFREG
        || stat.st_uid != uid
        || stat.st_nlink != 1
        || stat.st_mode & 0o077 != 0
        || flags < 0
        || flags & libc::O_ACCMODE != libc::O_RDWR
        || stat.st_size <= 0
        || stat.st_size > 256
    {
        return Err(refused("CPU handoff requires one private readable writable lease file"));
    }
    let mut bytes = [0; 257];
    // SAFETY: the buffer is writable and pread observes offset zero without
    // changing the executing owner's shared file-description offset.
    let count = unsafe { libc::pread(fd.as_raw_fd(), bytes.as_mut_ptr().cast(), bytes.len(), 0) };
    if count < 0 {
        return Err(io::Error::last_os_error());
    }
    if count == 0 || count > 256 {
        return Err(refused("CPU lease record exceeds its size bound"));
    }
    let text = std::str::from_utf8(&bytes[..count as usize])
        .map_err(|_| refused("CPU lease record is not UTF-8"))?;
    let fields: Vec<_> = text.split_whitespace().collect();
    let decimal = |value: &str| {
        !value.is_empty()
            && value.bytes().all(|b| b.is_ascii_digit())
            && value.parse::<u64>().is_ok()
    };
    if fields.len() != 5
        || fields[0] != "trust-build-cpu-v1"
        || fields[4] != "held=1"
        || !fields[1].strip_prefix("slot=").is_some_and(decimal)
        || !fields[2].strip_prefix("pid=").is_some_and(|pid| decimal(pid) && pid != "0")
        || !fields[3].strip_prefix("birth=").is_some_and(|birth| birth == "-" || decimal(birth))
        || text != format!("{}\n", fields.join(" "))
    {
        return Err(refused("CPU lease record is malformed"));
    }
    Ok(())
}

fn validate_fence_file(fd: &OwnedFd) -> io::Result<()> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: fd is owned; stat is writable for the complete kernel result.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: fstat initialized every field on success; geteuid only reads.
    let (stat, uid) = unsafe { (stat.assume_init(), libc::geteuid()) };
    if stat.st_mode & libc::S_IFMT != libc::S_IFREG
        || stat.st_uid != uid
        || stat.st_nlink != 1
        || stat.st_mode & 0o022 != 0
    {
        return Err(refused("CPU fence must be an owned non-writable-to-others regular file"));
    }
    Ok(())
}

/// Authenticated ancestor transport for an already-owned CPU lease.
///
/// The caller retains this endpoint through child completion. This helper
/// never creates a CPU grant: the recipient must validate the returned file
/// against its actual global pool before borrowing the implicit credit.
#[derive(Debug)]
pub struct CpuLeaseHandoff(Arc<Endpoint>);

impl CpuLeaseHandoff {
    /// Retain a private CPU-like regular file and serve duplicates to descendants.
    pub fn new(owned: OwnedFd) -> io::Result<Self> {
        validate_cpu_file(&owned)?;
        let other = owned.try_clone()?;
        let endpoint =
            Endpoint::new_role(Arc::new([owned, other]), &std::env::temp_dir(), Role::CpuLease)?;
        Ok(Self(Arc::new(endpoint)))
    }

    /// Retain an actual CPU lease and the shared fence descriptions it owns.
    ///
    /// CPU-v2 carries one to 128 descriptors. Fences are transferred as the
    /// same open descriptions, never reacquired through mutable pathnames.
    /// The caller must supply genuinely held fences; file shape is not proof
    /// of pool membership, lock state, or permission to mint a new grant.
    pub fn new_bundle(primary: OwnedFd, fences: Vec<OwnedFd>) -> io::Result<Self> {
        if fences.len() >= MAX_CPU_FILES {
            return Err(refused("CPU handoff bundle exceeds its descriptor bound"));
        }
        validate_cpu_file(&primary)?;
        for fence in &fences {
            validate_fence_file(fence)?;
        }
        let mut handles = Vec::with_capacity(fences.len() + 1);
        handles.push(primary);
        handles.extend(fences);
        let count = handles.len() as libc::c_int;
        let endpoint = Endpoint::new_resources(
            Arc::new(handles),
            [count, 0],
            &std::env::temp_dir(),
            Role::CpuBundle,
        )?;
        Ok(Self(Arc::new(endpoint)))
    }

    /// Publish the CPU-role advertisement and retain its endpoint through spawn.
    pub fn configure(self: &Arc<Self>, command: &mut std::process::Command) {
        self.0.configure(command);
    }

    /// Inert routing information; possession alone grants no lease or authority.
    pub fn advertisement(&self) -> &OsStr {
        &self.0.advertisement
    }
}

/// Recover a fresh descriptor from a live authenticated ancestor.
///
/// Advertised original descriptor numbers are neither used nor closed: they
/// may already name unrelated files. The caller must still validate the fresh
/// returned descriptor against the actual global CPU pool.
pub fn recover_cpu_lease(advertisement: &OsStr) -> io::Result<OwnedFd> {
    let handles = recover_role(Advertisement::parse(advertisement)?, Role::CpuLease)?;
    handles[0].try_clone()
}

/// Recover the actual CPU-v2 lease and all of its inherited fence descriptions.
/// No advertised descriptor number or pathname is opened as authority. The
/// caller validates membership against its actual CPU/fence pools before use.
pub fn recover_cpu_resources(advertisement: &OsStr) -> io::Result<(OwnedFd, Vec<OwnedFd>)> {
    let advertisement = Advertisement::parse_role(advertisement, Role::CpuBundle)?;
    let mut handles = recover_handles(advertisement, Role::CpuBundle)?.into_iter();
    let primary = handles.next().ok_or_else(|| refused("CPU handoff has no primary lease"))?;
    Ok((primary, handles.collect()))
}

/// Live ancestor courier for an already retained original fixed claim. The
/// packet and files are transferred as the same open descriptions; no token,
/// CPU reservation, SDK custody or fixed-claim authority is created here.
#[derive(Debug)]
pub struct FixedClaimHandoff(Arc<Endpoint>);

impl FixedClaimHandoff {
    pub fn new(packet: OwnedFd, originals: Vec<OwnedFd>) -> io::Result<Self> {
        let mut handles = Vec::with_capacity(originals.len() + 1);
        handles.push(packet);
        handles.extend(originals);
        validate_fixed_files(&handles)?;
        let count = handles.len() as libc::c_int;
        Ok(Self(Arc::new(Endpoint::new_resources(
            Arc::new(handles),
            [count, 0],
            &std::env::temp_dir(),
            Role::FixedClaim,
        )?)))
    }

    /// Distinct output-member generation. V1 still accepts regular fence
    /// files only; the domain receiver must authenticate this directory/lock
    /// pair against its Root-issued record before accepting membership.
    pub fn new_with_output_member(packet: OwnedFd, originals: Vec<OwnedFd>) -> io::Result<Self> {
        let mut handles = Vec::with_capacity(originals.len() + 1);
        handles.push(packet);
        handles.extend(originals);
        validate_fixed_output_files(&handles)?;
        let count = handles.len() as libc::c_int;
        Ok(Self(Arc::new(Endpoint::new_resources(
            Arc::new(handles),
            [count, 0],
            &std::env::temp_dir(),
            Role::FixedOutput,
        )?)))
    }

    /// Routing data only. Keep this actual endpoint through descendant waits.
    pub fn advertisement(&self) -> &OsStr {
        &self.0.advertisement
    }
}

/// Recover only fresh SCM rights from the actual live ancestor, never an
/// advertised local FD number. The domain reader must check the complete
/// packet/file identities, original locks, fingerprint, budget and pool.
pub fn recover_fixed_claim(advertisement: &OsStr) -> io::Result<(OwnedFd, Vec<OwnedFd>)> {
    let role = if advertisement.as_bytes().split(|byte| *byte == b':').next()
        == Some(b"fixed2".as_slice())
    {
        Role::FixedOutput
    } else {
        Role::FixedClaim
    };
    let ad = Advertisement::parse_role(advertisement, role)?;
    let mut handles = recover_handles(ad, role)?.into_iter();
    let packet = handles.next().ok_or_else(|| refused("fixed handoff has no packet"))?;
    Ok((packet, handles.collect()))
}

fn validate_fixed_output_files(handles: &[OwnedFd]) -> io::Result<()> {
    if !(4..=MAX_FIXED_FILES + 2).contains(&handles.len()) {
        return Err(refused("fixed output-member population is invalid"));
    }
    validate_fixed_files(&handles[..handles.len() - 2])?;
    validate_fence_file(&handles[handles.len() - 1])?;
    let directory = &handles[handles.len() - 2];
    let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: actual owned descriptor and complete writable native stat.
    if unsafe { libc::fstat(directory.as_raw_fd(), metadata.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful fstat initialized the metadata; geteuid observes only.
    let (metadata, uid) = unsafe { (metadata.assume_init(), libc::geteuid()) };
    if metadata.st_mode & libc::S_IFMT != libc::S_IFDIR
        || metadata.st_uid != uid
        || metadata.st_mode & 0o077 != 0
    {
        return Err(refused("fixed output member is not an owned private directory"));
    }
    Ok(())
}

fn validate_fixed_files(handles: &[OwnedFd]) -> io::Result<()> {
    if !(2..=MAX_FIXED_FILES).contains(&handles.len()) {
        return Err(refused("fixed handoff file population is invalid"));
    }
    let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: an owned descriptor and complete writable native stat storage.
    if unsafe { libc::fstat(handles[0].as_raw_fd(), metadata.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful fstat initialized the complete result.
    let metadata = unsafe { metadata.assume_init() };
    let flags = unsafe { libc::fcntl(handles[0].as_raw_fd(), libc::F_GETFL) };
    if metadata.st_mode & libc::S_IFMT != libc::S_IFREG
        || metadata.st_uid != unsafe { libc::geteuid() }
        || metadata.st_mode & 0o077 != 0
        || metadata.st_size <= 0
        || metadata.st_size > 8 * 1024 * 1024
        || flags < 0
        || flags & libc::O_ACCMODE == libc::O_WRONLY
    {
        return Err(refused("fixed handoff packet is not a private readable bounded file"));
    }
    for fd in &handles[1..] {
        validate_fence_file(fd)?;
    }
    Ok(())
}

/// Recover the original named FIFO witness descriptions from the authenticated
/// scoped owner. Advertised count fields are NEVER interpreted as FD numbers;
/// inherited/reused descriptors are neither read nor closed. Callers freshly
/// open the locator and compare it with these witnesses before scheduling.
pub fn recover_named_fifo_resources(advertisement: &OsStr) -> io::Result<[OwnedFd; 2]> {
    let advertisement = Advertisement::parse_role(advertisement, Role::NamedFifo)?;
    let handles = recover_handles(advertisement, Role::NamedFifo)?;
    handles.try_into().map_err(|_| refused("named FIFO handoff did not return two witnesses"))
}

fn validate_named_pair(handles: &[OwnedFd]) -> io::Result<()> {
    if handles.len() != 2 || FileIdentity::read(&handles[0])? != FileIdentity::read(&handles[1])? {
        return Err(refused("named FIFO witnesses differ"));
    }
    for (index, fd) in handles.iter().enumerate() {
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: held descriptor, correctly sized writable native stat storage.
        let result = unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) };
        if result != 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful fstat initialized the complete native value.
        let stat = unsafe { stat.assume_init() };
        // SAFETY: read-only access-mode query on the held witness descriptor.
        let mode = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
        let access = mode & libc::O_ACCMODE;
        if stat.st_mode & libc::S_IFMT != libc::S_IFIFO
            || mode < 0
            || if index == 0 { access == libc::O_WRONLY } else { access == libc::O_RDONLY }
        {
            return Err(refused(
                "named FIFO witnesses are not ordered readable/writable descriptions",
            ));
        }
    }
    Ok(())
}

/// Owned by the chosen scheduler, never a replacement scheduler or token proxy.
pub(super) struct Endpoint {
    role: Role,
    advertisement: OsString,
    stop: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
    _directory: Directory,
    scope: Option<Arc<Mutex<scoped::Scope>>>,
}

impl std::fmt::Debug for Endpoint {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Endpoint").finish_non_exhaustive()
    }
}

impl Endpoint {
    #[cfg(any(feature = "client", test))]
    pub(super) fn new(pipe: Arc<[OwnedFd; 2]>, base: &std::path::Path) -> io::Result<Self> {
        Self::new_role(pipe, base, Role::Jobserver)
    }

    fn new_role(pipe: Arc<[OwnedFd; 2]>, base: &std::path::Path, role: Role) -> io::Result<Self> {
        let pair = [pipe[0].as_raw_fd(), pipe[1].as_raw_fd()];
        let handles = pipe.iter().map(OwnedFd::try_clone).collect::<io::Result<Vec<_>>>()?;
        Self::new_resources(Arc::new(handles), pair, base, role)
    }

    fn new_resources(
        pipe: Arc<Vec<OwnedFd>>,
        pair: [libc::c_int; 2],
        base: &std::path::Path,
        role: Role,
    ) -> io::Result<Self> {
        Self::new_scoped_resources(pipe, pair, base, role, None)
    }

    fn new_scoped_resources(
        pipe: Arc<Vec<OwnedFd>>,
        pair: [libc::c_int; 2],
        base: &std::path::Path,
        role: Role,
        scope: Option<Arc<Mutex<scoped::Scope>>>,
    ) -> io::Result<Self> {
        let root = Process::current().map_err(|error| {
            io::Error::new(
                error.kind(),
                format!(
                    "could not read this process's identity for the job-server endpoint: {error}"
                ),
            )
        })?;
        let capability = random()?;
        // A valid TMPDIR can exceed sockaddr_un's pathname limit (104 bytes
        // on Darwin). Choose a short location before creating anything; do not
        // turn arbitrary bind/I/O failures into retries or a replacement pool.
        if !base.is_absolute() || base.as_os_str().as_bytes().contains(&0) {
            return Err(refused(&format!(
                "invalid jobserver endpoint directory {}",
                base.display()
            )));
        }
        let unique = random()?;
        let name = format!("tjs-{}", hex(&unique[..8]));
        let preferred = base.join(&name);
        let directory = if socket_address(&preferred.join("s")).is_ok() {
            preferred
        } else {
            // The absolute, NUL-free path above can fail only on length. Keep
            // invalid TMPDIRs refused; /tmp is only a pathname-length fallback.
            if !std::fs::metadata(base)
                .map_err(naming("read the job-server temporary directory", base))?
                .is_dir()
            {
                return Err(io::Error::new(
                    io::ErrorKind::NotADirectory,
                    format!(
                        "the job-server temporary directory {} is not a directory",
                        base.display()
                    ),
                ));
            }
            // A fresh random 0700 directory retains the same custody and
            // descriptor-based cleanup in this shared system temporary root.
            std::path::Path::new("/tmp").join(name)
        };
        // Trust (RL-65): before this folder is made, remove the ones beside it
        // whose owners were killed. The bytes of the draw the name did not use
        // say where in the listing this sweep starts.
        if let Some(parent) = directory.parent() {
            let rotation =
                unique[8..16].iter().fold(0, |sum, byte| (sum << 8) | usize::from(*byte));
            sweep_stale_folders(parent, rotation);
        }
        let directory = Directory::create(directory)?;
        let path = directory.path.join("s");
        let listener = bind_endpoint(&path)?;
        listener.set_nonblocking(true)?;
        let advertisement =
            Advertisement { owner: root.pid(), birth: root.birth(), pair, capability, path }
                .encode_role(role);
        let stop = Arc::new(AtomicBool::new(false));
        let stopping = Arc::clone(&stop);
        let serving_scope = scope.clone();
        let thread =
            std::thread::Builder::new().name("trust-jobserver".into()).spawn(move || {
                while !stopping.load(Ordering::Acquire) {
                    match listener.accept() {
                        Ok((stream, _)) => {
                            // Failed authentication grants nothing and cannot stop
                            // later legitimate probes. Every connection is bounded.
                            let _ = serve_scoped_role(
                                stream,
                                &root,
                                &pipe,
                                &capability,
                                pair,
                                role,
                                serving_scope.as_deref(),
                            );
                        }
                        Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                            std::thread::park_timeout(Duration::from_millis(100));
                        }
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                        Err(_) => break,
                    }
                }
            })?;
        Ok(Self { role, advertisement, stop, thread: Some(thread), _directory: directory, scope })
    }

    pub(super) fn configure(self: &Arc<Self>, command: &mut std::process::Command) {
        use std::os::unix::process::CommandExt;

        command.env(self.role.environment(), &self.advertisement);
        let endpoint = Arc::clone(self);
        // SAFETY: retaining the owner runs no operation in the child hook.
        // This keeps a configured Command's endpoint live through spawn even
        // when its originating wrapper is dropped. Targo retains the owner
        // itself through every child wait, as required by this API.
        unsafe {
            command.pre_exec(move || {
                let _ = &endpoint;
                Ok(())
            });
        }
    }
}

// Trust (RL-64): its own function so that a test can refuse a bind by a path
// whose folder is absent, with no sandbox.
fn bind_endpoint(path: &std::path::Path) -> io::Result<UnixListener> {
    UnixListener::bind(path).map_err(naming("bind the job-server socket", path))
}

impl Drop for Endpoint {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        if let Some(thread) = self.thread.take() {
            thread.thread().unpark();
            let _ = thread.join();
        }
    }
}

#[cfg(test)]
fn serve(
    stream: UnixStream,
    root: &Process,
    pipe: &[OwnedFd; 2],
    capability: &[u8; 32],
    pair: [libc::c_int; 2],
) -> io::Result<()> {
    serve_role(stream, root, pipe, capability, pair, Role::Jobserver)
}

#[cfg(test)]
fn serve_role(
    stream: UnixStream,
    root: &Process,
    pipe: &[OwnedFd],
    capability: &[u8; 32],
    pair: [libc::c_int; 2],
    role: Role,
) -> io::Result<()> {
    serve_scoped_role(stream, root, pipe, capability, pair, role, None)
}

fn serve_scoped_role(
    mut stream: UnixStream,
    root: &Process,
    pipe: &[OwnedFd],
    capability: &[u8; 32],
    pair: [libc::c_int; 2],
    role: Role,
    scope: Option<&Mutex<scoped::Scope>>,
) -> io::Result<()> {
    let deadline = Instant::now() + TIMEOUT;
    stream.set_nonblocking(true)?;
    let requester = Process::peer(&stream)?;
    let mut request = [0_u8; 80];
    read_frame(&mut stream, &mut request, deadline)?;
    expect_end(&mut stream, deadline)?;
    let capability_difference =
        request[8..40].iter().zip(capability).fold(0, |a, (x, y)| a | (x ^ y));
    if &request[..8] != role.magic()
        || capability_difference != 0
        || request[72..76] != pair[0].to_be_bytes()
        || request[76..80] != pair[1].to_be_bytes()
    {
        return Err(refused("jobserver handoff session or pool mismatch"));
    }
    let chain = ancestry(root, &requester)?;
    let member_chain = scoped::authorize(scope, &requester)?;
    ensure_chain(&chain)?;
    root.ensure_unchanged()?;
    ensure_chain(&member_chain)?;
    if matches!(role, Role::FixedClaim | Role::FixedOutput) {
        for chunk in pipe.chunks(FIXED_FILES_PER_MESSAGE) {
            send_handles(&stream, chunk, deadline)?;
        }
    } else {
        send_handles(&stream, pipe, deadline)?;
    }
    write_frame(&mut stream, &request[40..72], deadline)?;
    ensure_chain(&chain)?;
    ensure_chain(&member_chain)?;
    root.ensure_unchanged()
}

/// Only the early-startup shim importer calls this. All advertised numbers
/// must be closed before opening a socket or process file can reuse them.
#[cfg(any(feature = "client", test))]
pub(super) fn recover(advertisement: &OsStr, cargo_flags: &OsStr) -> io::Result<Arc<[OwnedFd; 2]>> {
    let advertisement = Advertisement::parse(advertisement)?;
    if cargo_flags != OsStr::new(&flags(advertisement.pair)) {
        return Err(refused("jobserver handoff does not bind the advertised pool"));
    }
    for fd in advertisement.pair {
        // SAFETY: F_GETFD inspects but never takes ownership of this number.
        let result = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        if result != -1 || io::Error::last_os_error().raw_os_error() != Some(libc::EBADF) {
            return Err(refused("jobserver recovery requires two closed advertised descriptors"));
        }
    }
    // No sockets, sidecars, proc files or other fd opens occur above this line.
    recover_role(advertisement, Role::Jobserver)
}

/// Obtain original scheduler descriptions solely from the authenticated ancestor.
/// Unlike startup recovery, this never imports, reads or closes ambient slots.
/// The returned rights come from the same checked owner/ancestry handshake.
#[cfg(any(feature = "client", test))]
pub(super) fn retain_originals(
    advertisement: &OsStr,
    cargo_flags: &OsStr,
) -> io::Result<Arc<[OwnedFd; 2]>> {
    let advertisement = Advertisement::parse(advertisement)?;
    if cargo_flags != OsStr::new(&flags(advertisement.pair)) {
        return Err(refused("jobserver handoff does not bind the advertised pool"));
    }
    recover_role(advertisement, Role::Jobserver)
}

fn recover_role(advertisement: Advertisement, role: Role) -> io::Result<Arc<[OwnedFd; 2]>> {
    let handles = recover_handles(advertisement, role)?;
    Ok(Arc::new(handles.try_into().map_err(|_| refused("handoff did not return a pair"))?))
}

fn recover_handles(advertisement: Advertisement, role: Role) -> io::Result<Vec<OwnedFd>> {
    let count = if matches!(role, Role::CpuBundle | Role::FixedClaim | Role::FixedOutput) {
        advertisement.pair[0] as usize
    } else {
        2
    };
    let deadline = Instant::now() + TIMEOUT;
    let mut stream = connect(&advertisement.path, deadline)?;
    let owner = Process::peer(&stream)?;
    if owner.pid() != advertisement.owner || owner.birth() != advertisement.birth {
        return Err(refused("jobserver endpoint has a substituted owner"));
    }
    let chain = ancestry(&owner, &Process::current()?)?;
    let challenge = random()?;
    let mut request = [0; 80];
    request[..8].copy_from_slice(role.magic());
    request[8..40].copy_from_slice(&advertisement.capability);
    request[40..72].copy_from_slice(&challenge);
    request[72..76].copy_from_slice(&advertisement.pair[0].to_be_bytes());
    request[76..80].copy_from_slice(&advertisement.pair[1].to_be_bytes());
    write_frame(&mut stream, &request, deadline)?;
    stream.shutdown(std::net::Shutdown::Write)?;
    let pipe = receive_role_response(&mut stream, deadline, role, count, &challenge)?;
    owner.ensure_unchanged()?;
    ensure_chain(&chain)?;
    Ok(pipe)
}

fn receive_role_response(
    stream: &mut UnixStream,
    deadline: Instant,
    role: Role,
    count: usize,
    challenge: &[u8; 32],
) -> io::Result<Vec<OwnedFd>> {
    let pipe = if matches!(role, Role::FixedClaim | Role::FixedOutput) {
        let mut all = Vec::with_capacity(count);
        while all.len() < count {
            let expected = (count - all.len()).min(FIXED_FILES_PER_MESSAGE);
            all.extend(receive_handles(stream, deadline, role, expected)?);
        }
        match role {
            Role::FixedOutput => validate_fixed_output_files(&all)?,
            _ => validate_fixed_files(&all)?,
        }
        all
    } else {
        receive_handles(stream, deadline, role, count)?
    };
    let mut response = [0; 32];
    read_frame(stream, &mut response, deadline)?;
    if &response != challenge {
        return Err(refused("jobserver handoff challenge mismatch"));
    }
    expect_end(stream, deadline)?;
    Ok(pipe)
}

#[cfg(test)]
fn send_pipe(stream: &UnixStream, pipe: &[OwnedFd; 2], deadline: Instant) -> io::Result<()> {
    send_handles(stream, pipe, deadline)
}

fn send_handles(stream: &UnixStream, pipe: &[OwnedFd], deadline: Instant) -> io::Result<()> {
    let descriptors = pipe.iter().map(std::os::fd::AsFd::as_fd).collect::<Vec<_>>();
    super::descriptor_transfer::send(stream, &descriptors, 1, deadline)
}

#[cfg(test)]
fn receive_pipe(stream: &UnixStream, deadline: Instant) -> io::Result<[OwnedFd; 2]> {
    receive_role(stream, deadline, Role::Jobserver)
}

#[cfg(test)]
fn receive_role(stream: &UnixStream, deadline: Instant, role: Role) -> io::Result<[OwnedFd; 2]> {
    receive_handles(stream, deadline, role, 2)?
        .try_into()
        .map_err(|_| refused("handoff is not a pair"))
}

fn receive_handles(
    stream: &UnixStream,
    deadline: Instant,
    role: Role,
    count: usize,
) -> io::Result<Vec<OwnedFd>> {
    let mut byte = [0_u8];
    let mut control = [0_usize; ANCILLARY_BYTES / size_of::<usize>()];
    let mut iovec = libc::iovec { iov_base: byte.as_mut_ptr().cast(), iov_len: 1 };
    // SAFETY: zero is valid for the optional msghdr pointers/counts.
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iovec;
    message.msg_iovlen = 1;
    message.msg_control = control.as_mut_ptr().cast();
    message.msg_controllen = size_of_val(&control) as _;
    #[cfg(target_os = "linux")]
    let flags = libc::MSG_CMSG_CLOEXEC;
    #[cfg(target_os = "macos")]
    let flags = 0;
    // SAFETY: all message buffers are valid writable memory for their lengths.
    let received = loop {
        check_deadline(deadline)?;
        // SAFETY: buffers remain valid and no descriptors arrive on an error.
        let received = unsafe { libc::recvmsg(stream.as_raw_fd(), &mut message, flags) };
        if received >= 0 {
            break received;
        }
        let error = io::Error::last_os_error();
        match error.kind() {
            io::ErrorKind::WouldBlock => ready(stream, libc::POLLIN, deadline)?,
            io::ErrorKind::Interrupted => {}
            _ => return Err(error),
        }
        // recvmsg may rewrite these fields even on an interrupted attempt.
        message.msg_controllen = size_of_val(&control) as _;
        message.msg_flags = 0;
    };
    let mut descriptors = Vec::new();
    let mut malformed_header = None;
    let mut valid = received == 1
        && byte == [1]
        && message.msg_flags & (libc::MSG_CTRUNC | libc::MSG_TRUNC) == 0;
    let reported_control_bytes = message.msg_controllen as usize;
    if reported_control_bytes > size_of_val(&control) {
        valid = false;
        message.msg_controllen = size_of_val(&control) as _;
    }
    // SAFETY: the kernel initialized this control buffer. Visit every complete
    // rights header, owning every delivered fd even when the frame is invalid,
    // so every rejection below closes all received descriptors.
    unsafe {
        let mut header = libc::CMSG_FIRSTHDR(&message);
        while !header.is_null() {
            let base = libc::CMSG_LEN(0) as usize;
            let remaining =
                message.msg_controllen as usize - (header as usize - message.msg_control as usize);
            if remaining < base {
                valid = false;
                malformed_header = Some((0, remaining));
                break;
            }
            let length = (*header).cmsg_len as usize;
            if length < base {
                valid = false;
                malformed_header = Some((length, remaining));
                break;
            }
            if (*header).cmsg_level == libc::SOL_SOCKET && (*header).cmsg_type == libc::SCM_RIGHTS {
                // Darwin preserves the original cmsg_len on MSG_CTRUNC.
                // Own every complete delivered prefix fd before rejecting it;
                // never inspect bytes outside the actual supplied buffer.
                let payload = length.min(remaining) - base;
                valid &= (length - base).is_multiple_of(size_of::<libc::c_int>())
                    && payload.is_multiple_of(size_of::<libc::c_int>());
                let data = libc::CMSG_DATA(header).cast::<libc::c_int>();
                for index in 0..payload / size_of::<libc::c_int>() {
                    descriptors.push(OwnedFd::from_raw_fd(data.add(index).read_unaligned()));
                }
            } else {
                valid = false;
            }
            if length > remaining {
                valid = false;
                malformed_header = Some((length, remaining));
                break;
            }
            header = libc::CMSG_NXTHDR(&message, header);
        }
    }
    if !valid || descriptors.len() != count {
        let expected = if count == 2 { "two".to_owned() } else { count.to_string() };
        return Err(refused(&format!(
            "jobserver handoff requires exactly {expected} untruncated descriptors (rights={}, control_bytes={}, flags={:#x}, malformed_header={malformed_header:?})",
            descriptors.len(),
            reported_control_bytes,
            message.msg_flags,
        )));
    }
    for (index, fd) in descriptors.iter().enumerate() {
        // SAFETY: inspect only the newly owned descriptors. On macOS mark them
        // CLOEXEC before any other opens/spawn; the shim is single-threaded.
        unsafe {
            let flags = libc::fcntl(fd.as_raw_fd(), libc::F_GETFD);
            if flags < 0 || libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC) < 0
            {
                return Err(io::Error::last_os_error());
            }
            let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
            if libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) != 0 {
                return Err(io::Error::last_os_error());
            }
            let mode = libc::fcntl(fd.as_raw_fd(), libc::F_GETFL);
            let access = mode & libc::O_ACCMODE;
            if matches!(role, Role::Jobserver | Role::NamedFifo)
                && (stat.assume_init().st_mode & libc::S_IFMT != libc::S_IFIFO
                    || mode < 0
                    || if index == 0 { access == libc::O_WRONLY } else { access == libc::O_RDONLY })
            {
                return Err(refused("jobserver handoff descriptors are not an ordered pipe pair"));
            }
        }
    }
    if matches!(role, Role::NamedFifo) {
        validate_named_pair(&descriptors)?;
    }
    if matches!(role, Role::CpuBundle) {
        validate_cpu_file(&descriptors[0])?;
        for fd in &descriptors[1..] {
            validate_fence_file(fd)?;
        }
    }
    if matches!(role, Role::CpuLease) {
        for fd in &descriptors {
            validate_cpu_file(fd)?;
        }
        let first = FileIdentity::read(&descriptors[0])?;
        if first != FileIdentity::read(&descriptors[1])? {
            return Err(refused("CPU handoff must duplicate one file description"));
        }
    }
    Ok(descriptors)
}
