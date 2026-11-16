// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Read-only native identity observations extracted from aterm's process readers.
//! Birth units are BSD wall microseconds on macOS and start ticks on Linux.

use std::fs::File;
use std::io;
use std::os::fd::AsRawFd;
#[cfg(target_os = "linux")]
use std::os::fd::FromRawFd;
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Identity {
    pub pid: u32,
    pub parent: u32,
    pub birth: u64,
    pub unique_id: u64,
    pub parent_unique_id: u64,
    pub exec_version: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Presence {
    Absent,
    Present,
    Unknown,
}

fn refused(why: &str) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, why)
}

/// Absence is reported only when the kernel proves ESRCH, never on a failed read.
pub fn presence(pid: u32) -> Presence {
    let Ok(pid) = i32::try_from(pid) else {
        return Presence::Unknown;
    };
    if pid <= 1 {
        return Presence::Unknown;
    }
    // SAFETY: signal zero only probes the existence of this positive PID.
    if unsafe { libc::kill(pid, 0) } == 0 {
        return Presence::Present;
    }
    match io::Error::last_os_error().raw_os_error() {
        Some(libc::ESRCH) => Presence::Absent,
        _ => Presence::Unknown,
    }
}

/// Resolve the real account's database home, refusing changed-UID contexts.
pub fn account_home() -> io::Result<PathBuf> {
    use std::ffi::CStr;
    use std::os::unix::ffi::OsStrExt;
    // SAFETY: getuid and geteuid read only this process's account identities.
    let (uid, effective) = unsafe { (libc::getuid(), libc::geteuid()) };
    if uid != effective {
        return Err(refused("changed-UID resource provenance is unsupported"));
    }
    let mut bytes = vec![0_u8; 1024];
    loop {
        let mut record = std::mem::MaybeUninit::<libc::passwd>::zeroed();
        let mut result = std::ptr::null_mut();
        // SAFETY: record, bytes and result are writable for their stated sizes.
        let rc = unsafe {
            libc::getpwuid_r(
                uid,
                record.as_mut_ptr(),
                bytes.as_mut_ptr().cast(),
                bytes.len(),
                &mut result,
            )
        };
        if rc == libc::ERANGE && bytes.len() < 1024 * 1024 {
            bytes.resize(bytes.len() * 2, 0);
            continue;
        }
        if rc != 0 {
            return Err(io::Error::from_raw_os_error(rc));
        }
        if result.is_null() {
            return Err(refused("account database has no home"));
        }
        // SAFETY: getpwuid_r returned the initialized record and pointers into bytes.
        let record = unsafe { record.assume_init() };
        if record.pw_dir.is_null() {
            return Err(refused("account home is null"));
        }
        // SAFETY: successful getpwuid_r supplies a NUL-terminated pw_dir.
        let path = PathBuf::from(std::ffi::OsStr::from_bytes(
            unsafe { CStr::from_ptr(record.pw_dir) }.to_bytes(),
        ));
        return if path.is_absolute() {
            Ok(path)
        } else {
            Err(refused("account home is not absolute"))
        };
    }
}

/// A bounded, reread ancestry observation; it creates no child-control authority.
pub fn stable_ancestor(
    ancestor: Identity,
    descendant: Identity,
    deadline: Instant,
) -> io::Result<bool> {
    let mut current = descendant;
    let mut chain = Vec::new();
    for _ in 0..256 {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        if read_identity(current.pid)? != current {
            return Err(refused("ancestry changed"));
        }
        chain.push(current);
        if current == ancestor {
            for member in chain.iter().rev() {
                if Instant::now() >= deadline {
                    return Err(io::ErrorKind::TimedOut.into());
                }
                if read_identity(member.pid)? != *member {
                    return Err(refused("ancestry changed during reread"));
                }
            }
            return Ok(true);
        }
        if current.parent <= 1 {
            return Ok(false);
        }
        if chain.iter().any(|member| member.pid == current.parent) {
            return Err(refused("cyclic process ancestry"));
        }
        let parent = read_identity(current.parent)?;
        #[cfg(target_os = "macos")]
        if parent.unique_id != current.parent_unique_id {
            return Err(refused("parent lifetime changed"));
        }
        if read_identity(current.pid)? != current {
            return Err(refused("child changed while reading parent"));
        }
        current = parent;
    }
    Err(refused("ancestry exceeds observation bound"))
}

/// Match a held regular executable to the actual kernel-loaded image.
/// The exact immutable kernel path must match too. macOS additionally preserves
/// aterm's vnode-inode comparison (the native reader has no device).
pub fn image_matches(expected: Identity, held: &File, expected_path: &Path) -> io::Result<bool> {
    if read_identity(expected.pid)? != expected {
        return Err(refused("image process changed"));
    }
    let before = held.metadata()?;
    if !before.is_file() {
        return Ok(false);
    }
    let first_path = image_path(expected.pid)?;
    let first = image_identity(expected.pid)?;
    let last = image_identity(expected.pid)?;
    if first != last
        || image_path(expected.pid)? != first_path
        || read_identity(expected.pid)? != expected
    {
        return Err(refused("image changed during observation"));
    }
    let after = held.metadata()?;
    if (before.dev(), before.ino()) != (after.dev(), after.ino()) {
        return Err(refused("held image identity changed"));
    }
    Ok(first_path == expected_path
        && first.1 == before.ino()
        && first.0.is_none_or(|dev| dev == before.dev()))
}

/// Authenticate an actual connected peer before and after each protocol exchange.
pub fn check_peer(stream: &UnixStream, expected: Identity) -> io::Result<()> {
    if read_identity(expected.pid)? != expected {
        return Err(refused("peer identity changed"));
    }
    let (pid, uid, version) = peer(stream)?;
    // SAFETY: geteuid reads this process's effective identity.
    if pid != expected.pid
        || uid != unsafe { libc::geteuid() }
        || version.is_some_and(|v| v != expected.exec_version)
    {
        return Err(refused("connected peer does not match native owner"));
    }
    if read_identity(expected.pid)? != expected {
        return Err(refused("peer changed during credential read"));
    }
    Ok(())
}

/// Observe a connected native peer, then bind its complete current lifetime.
/// This authenticates no resource, SDK, caller role or release authority.
pub fn connected_identity(stream: &UnixStream) -> io::Result<Identity> {
    let (pid, uid, _) = peer(stream)?;
    // SAFETY: geteuid observes the current account only.
    if uid != unsafe { libc::geteuid() } {
        return Err(refused("connected peer belongs to another account"));
    }
    let identity = read_identity(pid)?;
    check_peer(stream, identity)?;
    Ok(identity)
}

#[cfg(target_os = "macos")]
#[repr(C)]
struct BsdInfoWithUniqId {
    bsd: libc::proc_bsdinfo,
    uuid: [u8; 16],
    unique: u64,
    parent_unique: u64,
    version: i32,
    original_parent_version: i32,
    reserved2: u64,
    reserved3: u64,
}

#[cfg(target_os = "macos")]
const _: () = assert!(
    std::mem::size_of::<BsdInfoWithUniqId>() == std::mem::size_of::<libc::proc_bsdinfo>() + 56
);

#[cfg(target_os = "macos")]
pub fn read_identity(pid: u32) -> io::Result<Identity> {
    let pid = i32::try_from(pid).map_err(|_| refused("invalid process PID"))?;
    if pid <= 1 {
        return Err(refused("invalid process PID"));
    }
    let mut info = std::mem::MaybeUninit::<BsdInfoWithUniqId>::zeroed();
    let size = std::mem::size_of::<BsdInfoWithUniqId>() as i32;
    // SAFETY: this is aterm's maintained flavor-18 ABI; info is size writable bytes.
    let n = unsafe { libc::proc_pidinfo(pid, 18, 0, info.as_mut_ptr().cast(), size) };
    if n != size {
        return Err(refused("complete native process identity unavailable"));
    }
    // SAFETY: the kernel filled the complete plain-data record.
    let info = unsafe { info.assume_init() };
    // SAFETY: geteuid reads only the current process's effective identity.
    if info.bsd.pbi_pid != pid as u32
        || info.bsd.pbi_uid != unsafe { libc::geteuid() }
        || info.bsd.pbi_status == 5
    {
        return Err(refused("live same-user process unavailable"));
    }
    let birth = info
        .bsd
        .pbi_start_tvsec
        .checked_mul(1_000_000)
        .and_then(|s| s.checked_add(info.bsd.pbi_start_tvusec))
        .filter(|b| *b != 0)
        .ok_or_else(|| refused("invalid BSD process birth"))?;
    Ok(Identity {
        pid: pid as u32,
        parent: info.bsd.pbi_ppid,
        birth,
        unique_id: info.unique,
        parent_unique_id: info.parent_unique,
        exec_version: info.version as u32,
    })
}

#[cfg(target_os = "macos")]
fn image_identity(pid: u32) -> io::Result<(Option<u64>, u64)> {
    // Exact maintained PROC_PIDREGIONPATHINFO ABI from aterm-sysprobe::kproc.
    let mut at = 0_u64;
    for _ in 0..64 {
        let mut bytes = [0_u8; 1272];
        // SAFETY: bytes is the full maintained flavor-8 record buffer.
        let n = unsafe {
            libc::proc_pidinfo(pid as i32, 8, at, bytes.as_mut_ptr().cast(), bytes.len() as i32)
        };
        if n != bytes.len() as i32 {
            return Err(refused("loaded vnode identity unavailable"));
        }
        let word = |offset| -> io::Result<u64> {
            Ok(u64::from_ne_bytes(
                bytes[offset..offset + 8]
                    .try_into()
                    .map_err(|_| refused("invalid native image field"))?,
            ))
        };
        let inode = word(104)?;
        if inode != 0 {
            return Ok((None, inode));
        }
        let next = word(80)?
            .checked_add(word(88)?)
            .ok_or_else(|| refused("native image address overflow"))?;
        if next <= at {
            return Err(refused("native image observation did not advance"));
        }
        at = next;
    }
    Err(refused("native image observation exceeds region bound"))
}

#[cfg(target_os = "macos")]
fn image_path(pid: u32) -> io::Result<PathBuf> {
    use std::os::unix::ffi::OsStrExt;
    let mut bytes = [0_u8; 4096];
    // SAFETY: bytes is writable for its stated size; proc_pidpath retains no pointer.
    let n =
        unsafe { libc::proc_pidpath(pid as i32, bytes.as_mut_ptr().cast(), bytes.len() as u32) };
    let n = usize::try_from(n)
        .ok()
        .filter(|n| *n > 0 && *n < bytes.len())
        .ok_or_else(|| refused("kernel executable path unavailable"))?;
    let end = bytes[..n].iter().position(|b| *b == 0).unwrap_or(n);
    let path = PathBuf::from(std::ffi::OsStr::from_bytes(&bytes[..end]));
    if path.is_absolute() { Ok(path) } else { Err(refused("kernel image path is not absolute")) }
}
#[cfg(target_os = "linux")]
fn image_path(pid: u32) -> io::Result<PathBuf> {
    std::fs::read_link(format!("/proc/{pid}/exe"))
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn image_path(_: u32) -> io::Result<PathBuf> {
    Err(refused("native image path unsupported"))
}

#[cfg(target_os = "macos")]
fn peer(stream: &UnixStream) -> io::Result<(u32, u32, Option<u32>)> {
    let mut token = [0_u32; 8];
    let mut length = std::mem::size_of_val(&token) as libc::socklen_t;
    // SAFETY: token and length are writable, and the exact audit-token size is supplied.
    let rc = unsafe {
        libc::getsockopt(stream.as_raw_fd(), 0, 6, token.as_mut_ptr().cast(), &mut length)
    };
    if rc != 0 || length as usize != std::mem::size_of_val(&token) {
        return Err(refused("native peer audit token unavailable"));
    }
    Ok((token[5], token[1], Some(token[7])))
}

#[cfg(target_os = "linux")]
struct ProcDir(File);
#[cfg(target_os = "linux")]
impl ProcDir {
    fn open(pid: u32) -> io::Result<Self> {
        use std::os::unix::fs::OpenOptionsExt;
        let file = std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(format!("/proc/{pid}"))?;
        // SAFETY: geteuid reads only the current process identity.
        if file.metadata()?.uid() != unsafe { libc::geteuid() } {
            return Err(refused("foreign or unreadable proc directory"));
        }
        Ok(Self(file))
    }
    fn file(&self, name: &std::ffi::CStr, follow: bool) -> io::Result<File> {
        let flags = libc::O_RDONLY
            | libc::O_CLOEXEC
            | libc::O_NONBLOCK
            | if follow { 0 } else { libc::O_NOFOLLOW };
        // SAFETY: this held proc directory and NUL-terminated relative name are valid.
        let fd = unsafe { libc::openat(self.0.as_raw_fd(), name.as_ptr(), flags) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: openat returned one newly owned descriptor.
        Ok(unsafe { File::from_raw_fd(fd) })
    }
    fn read(&self, name: &std::ffi::CStr) -> io::Result<Vec<u8>> {
        use std::io::Read;
        let mut bytes = Vec::new();
        self.file(name, false)?.take(1024 * 1024 + 1).read_to_end(&mut bytes)?;
        if bytes.len() > 1024 * 1024 {
            return Err(refused("proc observation exceeds bound"));
        }
        Ok(bytes)
    }
}

#[cfg(target_os = "linux")]
fn stat(bytes: &[u8], pid: u32) -> io::Result<Identity> {
    let text = std::str::from_utf8(bytes).map_err(|_| refused("invalid proc stat"))?;
    let (number, _) = text.split_once('(').ok_or_else(|| refused("missing proc comm"))?;
    let fields = text
        .rsplit_once(')')
        .ok_or_else(|| refused("unterminated proc comm"))?
        .1
        .split_whitespace()
        .collect::<Vec<_>>();
    if number.trim().parse::<u32>().ok() != Some(pid)
        || fields.first().is_none_or(|s| matches!(*s, "Z" | "X" | "x"))
    {
        return Err(refused("proc process unavailable"));
    }
    let parent =
        fields.get(1).and_then(|s| s.parse().ok()).ok_or_else(|| refused("invalid proc parent"))?;
    let birth = fields
        .get(19)
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|n| *n != 0)
        .ok_or_else(|| refused("invalid proc birth"))?;
    Ok(Identity { pid, parent, birth, unique_id: birth, parent_unique_id: 0, exec_version: 0 })
}

#[cfg(target_os = "linux")]
pub fn read_identity(pid: u32) -> io::Result<Identity> {
    if pid <= 1 || pid > i32::MAX as u32 {
        return Err(refused("invalid process PID"));
    }
    let dir = ProcDir::open(pid)?;
    let before = stat(&dir.read(c"stat")?, pid)?;
    let status = dir.read(c"status")?;
    let text = std::str::from_utf8(&status).map_err(|_| refused("invalid proc status"))?;
    let uid = text
        .lines()
        .find_map(|line| line.strip_prefix("Uid:"))
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|s| s.parse::<u32>().ok());
    // SAFETY: geteuid reads only the current process identity.
    if uid != Some(unsafe { libc::geteuid() }) || stat(&dir.read(c"stat")?, pid)? != before {
        return Err(refused("proc identity changed or foreign"));
    }
    Ok(before)
}

#[cfg(target_os = "linux")]
fn image_identity(pid: u32) -> io::Result<(Option<u64>, u64)> {
    let dir = ProcDir::open(pid)?;
    let auxv = dir.read(c"auxv")?;
    let word = std::mem::size_of::<usize>();
    if !auxv.len().is_multiple_of(2 * word) {
        return Err(refused("invalid native auxv"));
    }
    let mut ended = false;
    for pair in auxv.chunks_exact(2 * word) {
        let key = usize::from_ne_bytes(
            pair[..word].try_into().map_err(|_| refused("invalid auxv word"))?,
        );
        if key == 2 {
            return Err(refused("translated executable observation unsupported"));
        }
        if key == 0 {
            ended = true;
            break;
        }
    }
    if !ended {
        return Err(refused("incomplete native auxv"));
    }
    let first = dir.file(c"exe", true)?.metadata()?;
    let last = dir.file(c"exe", true)?.metadata()?;
    if !first.is_file()
        || !last.is_file()
        || (first.dev(), first.ino()) != (last.dev(), last.ino())
        || dir.read(c"auxv")? != auxv
    {
        return Err(refused("loaded executable changed"));
    }
    Ok((Some(first.dev()), first.ino()))
}

#[cfg(target_os = "linux")]
fn peer(stream: &UnixStream) -> io::Result<(u32, u32, Option<u32>)> {
    let mut credentials = std::mem::MaybeUninit::<libc::ucred>::zeroed();
    let mut size = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    // SAFETY: credentials and size are writable for the exact SO_PEERCRED record.
    let rc = unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            credentials.as_mut_ptr().cast(),
            &mut size,
        )
    };
    if rc != 0 || size as usize != std::mem::size_of::<libc::ucred>() {
        return Err(refused("native peer credentials unavailable"));
    }
    // SAFETY: the exact complete credential structure was returned.
    let credentials = unsafe { credentials.assume_init() };
    Ok((
        u32::try_from(credentials.pid).map_err(|_| refused("invalid peer PID"))?,
        credentials.uid,
        None,
    ))
}

fn hex_id(raw: &[u8]) -> io::Result<String> {
    let text = std::str::from_utf8(raw)
        .map_err(|_| refused("invalid native UUID"))?
        .trim_matches(char::from(0))
        .trim();
    let hex = text.chars().filter(|c| *c != '-').collect::<String>();
    if hex.len() != 32
        || !hex.bytes().all(|b| b.is_ascii_hexdigit())
        || hex.bytes().all(|b| b == b'0')
    {
        return Err(refused("invalid native UUID"));
    }
    Ok(hex.to_ascii_lowercase())
}

#[cfg(target_os = "macos")]
pub fn host_boot() -> io::Result<(String, String)> {
    unsafe extern "C" {
        fn gethostuuid(id: *mut u8, wait: *const libc::timespec) -> libc::c_int;
    }
    let mut host = [0_u8; 16];
    let wait = libc::timespec { tv_sec: 1, tv_nsec: 0 };
    // SAFETY: host is uuid_t's16 writable bytes; wait is a valid live timespec.
    if unsafe { gethostuuid(host.as_mut_ptr(), &wait) } != 0 || host == [0; 16] {
        return Err(refused("native host UUID unavailable"));
    }
    let mut boot = [0_u8; 64];
    let mut size = boot.len();
    // SAFETY: boot and size are writable and the literal name is NUL-terminated.
    if unsafe {
        libc::sysctlbyname(
            c"kern.bootsessionuuid".as_ptr(),
            boot.as_mut_ptr().cast(),
            &mut size,
            std::ptr::null_mut(),
            0,
        )
    } != 0
        || size > boot.len()
    {
        return Err(refused("native boot UUID unavailable"));
    }
    let host = host.iter().map(|b| format!("{b:02x}")).collect::<String>();
    Ok((format!("darwin:{host}"), hex_id(&boot[..size])?))
}

#[cfg(target_os = "linux")]
pub fn host_boot() -> io::Result<(String, String)> {
    use std::io::Read;
    use std::os::unix::fs::OpenOptionsExt;
    let file = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open("/etc/machine-id")?;
    let meta = file.metadata()?;
    if !meta.is_file() || meta.uid() != 0 || meta.mode() & 0o022 != 0 || meta.len() > 64 {
        return Err(refused("invalid machine identity file"));
    }
    let mut host = Vec::new();
    file.take(65).read_to_end(&mut host)?;
    let mut boot = Vec::new();
    File::open("/proc/sys/kernel/random/boot_id")?.take(65).read_to_end(&mut boot)?;
    Ok((format!("linux:{}", hex_id(&host)?), hex_id(&boot)?))
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn read_identity(_: u32) -> io::Result<Identity> {
    Err(refused("native process identity unsupported"))
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn image_identity(_: u32) -> io::Result<(Option<u64>, u64)> {
    Err(refused("native image identity unsupported"))
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn peer(_: &UnixStream) -> io::Result<(u32, u32, Option<u32>)> {
    Err(refused("native peer identity unsupported"))
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn host_boot() -> io::Result<(String, String)> {
    Err(refused("native host identity unsupported"))
}

#[cfg(test)]
#[path = "process/tests.rs"]
mod tests;

// Trust: one WNOWAIT/group-stop owner shared by Cargo and native harnesses.
#[path = "process/owned_group.rs"]
mod owned_group;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use owned_group::{OwnedGroupExit, observe_owned_group_exit};
pub use owned_group::{stop_owned_group, unreaped_child_exit};

#[path = "process/signal_lease.rs"]
mod signal_lease;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use signal_lease::OWNED_GROUP_SIGNALS;
pub use signal_lease::{ChildSignalLease, pending_child_signal};
