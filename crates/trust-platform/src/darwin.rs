//! Darwin (aarch64-apple-darwin / x86_64-apple-darwin) ABI numbers the model
//! speaks, and the name tables that let a refusal say *which* command or
//! request it declined.
//!
//! Every number here was read from the macOS SDK headers
//! (`sys/errno.h`, `sys/fcntl.h`, `sys/filio.h`, `sys/ttycom.h`,
//! `sys/socket.h`, `sys/resource.h`, `sys/spawn.h`) on 2026-09-30, and the
//! ones the conformance suite exercises are re-measured on every run.

/// An `errno` value, with Darwin's numbering.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Errno(pub i32);

macro_rules! errnos {
    ($($name:ident = $val:expr),* $(,)?) => {
        impl Errno {
            $(pub const $name: Errno = Errno($val);)*
            /// The symbolic name, if this is one the model knows.
            #[must_use]
            pub fn name(self) -> Option<&'static str> {
                match self.0 {
                    $($val => Some(stringify!($name)),)*
                    _ => None,
                }
            }
        }
    };
}

errnos! {
    EPERM = 1, ENOENT = 2, ESRCH = 3, EINTR = 4, EIO = 5, ENXIO = 6, E2BIG = 7,
    ENOEXEC = 8, EBADF = 9, ECHILD = 10, ENOMEM = 12, EACCES = 13, EFAULT = 14,
    EBUSY = 16, EEXIST = 17, ENOTDIR = 20, EISDIR = 21, EINVAL = 22, ENFILE = 23, EMFILE = 24,
    ENOTTY = 25, ETXTBSY = 26, ENOSPC = 28, EROFS = 30, EPIPE = 32, EAGAIN = 35, ENOTSOCK = 38,
    EPROTOTYPE = 41, EPROTONOSUPPORT = 43, ENOTSUP = 45, EAFNOSUPPORT = 47,
    ECONNABORTED = 53, ENOBUFS = 55, ELOOP = 62, ENAMETOOLONG = 63,
    EBADEXEC = 85, EBADARCH = 86, EBADMACHO = 88, EOPNOTSUPP = 102, ENOTCAPABLE = 107,
}

impl std::fmt::Display for Errno {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.name() {
            Some(name) => write!(f, "{name}"),
            None => write!(f, "errno {}", self.0),
        }
    }
}

// ---- fcntl(2) -------------------------------------------------------------

pub const F_DUPFD: i32 = 0;
pub const F_GETFD: i32 = 1;
pub const F_SETFD: i32 = 2;
pub const F_GETFL: i32 = 3;
pub const F_SETFL: i32 = 4;
pub const F_DUPFD_CLOEXEC: i32 = 67;
pub const FD_CLOEXEC: i64 = 1;
/// Close-on-fork. MEASURED (Darwin 27.0, macOS 27.0.1): a descriptor flag
/// beside `FD_CLOEXEC` — `F_SETFD` keeps it, `F_GETFD` reads it, `O_CLOFORK`
/// and `F_DUPFD_CLOFORK` set it, `dup`/`F_DUPFD` clear it, and `fork` and
/// `posix_spawn` drop the descriptor. On Darwin 25.6 `F_SETFD` ignored this
/// bit. The model has no such flag: every call that would set it is refused.
pub const FD_CLOFORK: i64 = 2;

/// Every `fcntl` command `sys/fcntl.h` names. The model executes six of them
/// (see [`crate::clauses`]); the rest are refused *by this name*.
pub const FCNTL_COMMANDS: &[(i32, &str)] = &[
    (0, "F_DUPFD"),
    (1, "F_GETFD"),
    (2, "F_SETFD"),
    (3, "F_GETFL"),
    (4, "F_SETFL"),
    (5, "F_GETOWN"),
    (6, "F_SETOWN"),
    (7, "F_GETLK"),
    (8, "F_SETLK"),
    (9, "F_SETLKW"),
    (10, "F_SETLKWTIMEOUT"),
    (40, "F_FLUSH_DATA"),
    (41, "F_CHKCLEAN"),
    (42, "F_PREALLOCATE"),
    (43, "F_SETSIZE"),
    (44, "F_RDADVISE"),
    (45, "F_RDAHEAD"),
    (48, "F_NOCACHE"),
    (49, "F_LOG2PHYS"),
    (50, "F_GETPATH"),
    (51, "F_FULLFSYNC"),
    (52, "F_PATHPKG_CHECK"),
    (53, "F_FREEZE_FS"),
    (54, "F_THAW_FS"),
    (55, "F_GLOBAL_NOCACHE"),
    (59, "F_ADDSIGS"),
    (61, "F_ADDFILESIGS"),
    (62, "F_NODIRECT"),
    (63, "F_GETPROTECTIONCLASS"),
    (64, "F_SETPROTECTIONCLASS"),
    (65, "F_LOG2PHYS_EXT"),
    (66, "F_GETLKPID"),
    (67, "F_DUPFD_CLOEXEC"),
    (70, "F_SETBACKINGSTORE"),
    (71, "F_GETPATH_MTMINFO"),
    (72, "F_GETCODEDIR"),
    (73, "F_SETNOSIGPIPE"),
    (74, "F_GETNOSIGPIPE"),
    (75, "F_TRANSCODEKEY"),
    (76, "F_SINGLE_WRITER"),
    (77, "F_GETPROTECTIONLEVEL"),
    (78, "F_FINDSIGS"),
    (83, "F_ADDFILESIGS_FOR_DYLD_SIM"),
    (85, "F_BARRIERFSYNC"),
    (90, "F_OFD_SETLK"),
    (91, "F_OFD_SETLKW"),
    (92, "F_OFD_GETLK"),
    (93, "F_OFD_SETLKWTIMEOUT"),
    (97, "F_ADDFILESIGS_RETURN"),
    (98, "F_CHECK_LV"),
    (99, "F_PUNCHHOLE"),
    (100, "F_TRIM_ACTIVE_FILE"),
    (101, "F_SPECULATIVE_READ"),
    (102, "F_GETPATH_NOFIRMLINK"),
    (103, "F_ADDFILESIGS_INFO"),
    (104, "F_ADDFILESUPPL"),
    (105, "F_GETSIGSINFO"),
    (106, "F_SETLEASE"),
    (107, "F_GETLEASE"),
    (110, "F_TRANSFEREXTENTS"),
    (111, "F_ATTRIBUTION_TAG"),
    (112, "F_NOCACHE_EXT"),
    (113, "F_ADDSIGS_MAIN_BINARY"),
    (115, "F_DUPFD_CLOFORK"),
    (116, "F_RDADVISEV"),
];

/// The SDK name of an `fcntl` command number.
#[must_use]
pub fn fcntl_name(cmd: i32) -> Option<&'static str> {
    FCNTL_COMMANDS.iter().find(|(n, _)| *n == cmd).map(|(_, name)| *name)
}

// ---- open(2) flags --------------------------------------------------------

pub const O_RDONLY: i32 = 0x0000;
pub const O_WRONLY: i32 = 0x0001;
pub const O_RDWR: i32 = 0x0002;
pub const O_ACCMODE: i32 = 0x0003;
pub const O_NONBLOCK: i32 = 0x0004;
pub const O_APPEND: i32 = 0x0008;
pub const O_ASYNC: i32 = 0x0040;
pub const O_FSYNC: i32 = 0x0080;
pub const O_NOFOLLOW: i32 = 0x0100;
pub const O_CREAT: i32 = 0x0200;
pub const O_TRUNC: i32 = 0x0400;
pub const O_EXCL: i32 = 0x0800;
pub const O_NOCTTY: i32 = 0x20000;
pub const O_DIRECTORY: i32 = 0x100000;
pub const O_DSYNC: i32 = 0x400000;
pub const O_CLOEXEC: i32 = 0x0100_0000;
pub const O_SHLOCK: i32 = 0x0010;
pub const O_EXLOCK: i32 = 0x0020;
pub const O_RESOLVE_BENEATH: i32 = 0x1000;
pub const O_UNIQUE: i32 = 0x2000;
pub const O_EVTONLY: i32 = 0x8000;
pub const O_SYMLINK: i32 = 0x0020_0000;
pub const O_NOFOLLOW_ANY: i32 = 0x2000_0000;
pub const O_EXEC: i32 = 0x4000_0000;
/// XNU's close-on-FORK open flag. MEASURED (Darwin 25.6, where it was private
/// and not in the SDK): `open(path, O_RDONLY | 0x0800_0000)` succeeds,
/// `F_GETFD` reads 0, and neither `fork` nor `posix_spawn` copies the
/// descriptor; no `fcntl` could read, set or clear it. Darwin 27 names it
/// `O_CLOFORK` in the SDK and `F_GETFD` reads [`FD_CLOFORK`] after it. The
/// model has no such per-descriptor bit, so an `open` carrying it is refused.
pub const O_CLOFORK_PRIVATE: i32 = 0x0800_0000;

/// The `open(2)` bits the model executes: the access mode, the status bits
/// it tracks (`O_NONBLOCK`, `O_APPEND`, `O_FSYNC`, `O_DSYNC`), the
/// path-resolution bits whose only effect is on whether the path resolves
/// (`O_NOFOLLOW`, `O_CREAT`, `O_TRUNC`, `O_EXCL`, `O_DIRECTORY` — the
/// oracle's choice), `O_NOCTTY` (a no-op on Darwin: a tty is acquired only
/// by `TIOCSCTTY`) and `O_CLOEXEC`. Every other bit is refused BY NAME:
/// `O_SHLOCK`/`O_EXLOCK` take a `flock` lock (MEASURED: `F_GETFL` then reads
/// 0x4000, a second `O_EXLOCK|O_NONBLOCK` open fails `EAGAIN`; flock is M2),
/// `O_EVTONLY` changes `F_GETFL` (MEASURED 0x8000), the private close-on-fork
/// bit hides the descriptor from `fork`, `O_RESOLVE_BENEATH` fails
/// `ENOTCAPABLE`, and an unknown bit has an unknown effect.
pub const OPEN_MODELED_MASK: i32 = O_ACCMODE
    | O_NONBLOCK
    | O_APPEND
    | O_FSYNC
    | O_NOFOLLOW
    | O_CREAT
    | O_TRUNC
    | O_EXCL
    | O_NOCTTY
    | O_DIRECTORY
    | O_DSYNC
    | O_CLOEXEC;

/// The `open(2)` bits a NAMED open ([`crate::Call::OpenPath`], whose node the
/// model's namespace knows) executes: [`OPEN_MODELED_MASK`] plus the lock bits.
/// MEASURED (Darwin 25.6): `O_EXLOCK` / `O_SHLOCK` take the `flock` lock on the
/// new description as part of the open — the description then reads
/// [`FHASLOCK`] in `F_GETFL`, and neither lock bit does; both bits together take
/// `LOCK_EX`; a conflicting lock fails `EAGAIN` under `O_NONBLOCK` with no
/// descriptor allocated; on a FIFO they fail `ENOTSUP`. An anonymous
/// [`crate::Call::Open`] keeps refusing them: the model does not know which node
/// that open named, and locks conflict per node.
pub const OPEN_NAMED_MODELED_MASK: i32 = OPEN_MODELED_MASK | O_SHLOCK | O_EXLOCK;

/// Names of the `open(2)` bits the model refuses (for legible refusals).
pub const OPEN_REFUSED_NAMES: &[(i32, &str)] = &[
    (O_SHLOCK, "O_SHLOCK"),
    (O_EXLOCK, "O_EXLOCK"),
    (O_ASYNC, "O_ASYNC"),
    (O_RESOLVE_BENEATH, "O_RESOLVE_BENEATH"),
    (O_UNIQUE, "O_UNIQUE"),
    (O_EVTONLY, "O_EVTONLY"),
    (O_SYMLINK, "O_SYMLINK"),
    (O_CLOFORK_PRIVATE, "O_CLOFORK (private)"),
    (O_NOFOLLOW_ANY, "O_NOFOLLOW_ANY"),
    (O_EXEC, "O_EXEC"),
];

/// The names of the bits of `flags` outside [`OPEN_MODELED_MASK`], or `None`
/// when every bit is modeled.
#[must_use]
pub fn unmodeled_open_bits(flags: i32) -> Option<String> {
    unmodeled_open_bits_in(flags, OPEN_MODELED_MASK)
}

/// The names of the bits of `flags` outside `mask`, or `None` when every bit
/// is in it.
#[must_use]
pub fn unmodeled_open_bits_in(flags: i32, mask: i32) -> Option<String> {
    let extra = flags & !mask;
    if extra == 0 {
        return None;
    }
    let mut names = Vec::new();
    let mut rest = extra;
    for (bit, name) in OPEN_REFUSED_NAMES {
        if rest & bit != 0 {
            names.push((*name).to_string());
            rest &= !bit;
        }
    }
    if rest != 0 {
        names.push(format!("unknown bits {rest:#x}"));
    }
    Some(names.join("|"))
}

/// `OPEN_MAX` (`sys/syslimits.h`). MEASURED (Darwin 25.6): libc's
/// `posix_spawn_file_actions_add{close,dup2,open,inherit_np,fchdir_np}`
/// reject any descriptor `< 0` or `>= OPEN_MAX` with `EBADF` at ADD time,
/// although the kernel allocates descriptors up to `kern.maxfilesperproc`
/// (92160 here).
pub const OPEN_MAX: i32 = 10_240;

/// The status bits `F_SETFL` can change on Darwin. MEASURED (2026-09-30,
/// Darwin 25.6): `F_SETFL(O_APPEND|O_NONBLOCK|O_RDWR|O_CLOEXEC|O_FSYNC)` on a
/// pipe's write end leaves `F_GETFL == O_WRONLY|O_NONBLOCK|O_APPEND|O_FSYNC`
/// and `FD_CLOEXEC` clear; `O_ASYNC` and `O_DSYNC` are accepted; `0x10`,
/// `0x100`, `0x20000` are ignored.
pub const SETFL_MASK: i32 = O_NONBLOCK | O_APPEND | O_ASYNC | O_FSYNC | O_DSYNC;

/// XNU's `FWASWRITTEN`, visible through `F_GETFL`. MEASURED (Darwin 25.6):
/// after a `write` on a pipe write end or a socket, `F_GETFL` on that
/// description (and its duplicates) reads this bit; `F_SETFL(0)` does not
/// clear it.
pub const FWASWRITTEN: i32 = 0x0001_0000;

/// The status bits an `open` carries into the new description.
pub const OPEN_STATUS_MASK: i32 = O_NONBLOCK | O_APPEND | O_FSYNC | O_DSYNC;

/// `openat(2)`'s "the current directory" (`sys/fcntl.h`).
pub const AT_FDCWD: i32 = -2;

// ---- flock(2) -----------------------------------------------------------------

pub const LOCK_SH: i32 = 1;
pub const LOCK_EX: i32 = 2;
pub const LOCK_NB: i32 = 4;
pub const LOCK_UN: i32 = 8;

/// XNU's `FHASLOCK`, visible through `F_GETFL`. MEASURED (Darwin 25.6): set on
/// the DESCRIPTION (a `dup` reads it too) by every `flock` that GRANTS a lock
/// and by an `O_EXLOCK`/`O_SHLOCK` open; never by `LOCK_UN`, by a refused
/// `LOCK_NB` request, or by an `flock` that fails on a non-vnode; kept by
/// `LOCK_UN` and by `F_SETFL` (a "was locked" bit, not "is locked").
pub const FHASLOCK: i32 = 0x4000;

// ---- file types (st_mode & S_IFMT) ------------------------------------------------

pub const S_IFMT: i32 = 0o170_000;
pub const S_IFIFO: i32 = 0o010_000;
pub const S_IFCHR: i32 = 0o020_000;
pub const S_IFDIR: i32 = 0o040_000;
pub const S_IFREG: i32 = 0o100_000;
pub const S_IFLNK: i32 = 0o120_000;
pub const S_IFSOCK: i32 = 0o140_000;

// ---- ioctl(2) requests ----------------------------------------------------

pub const FIOCLEX: u64 = 0x2000_6601;
pub const FIONCLEX: u64 = 0x2000_6602;
pub const FIONBIO: u64 = 0x8004_667e;

/// Requests the model does not execute, named so a refusal is legible.
pub const IOCTL_NAMED: &[(u64, &str)] = &[
    (0x2000_6601, "FIOCLEX"),
    (0x2000_6602, "FIONCLEX"),
    (0x8004_667e, "FIONBIO"),
    (0x8004_667d, "FIOASYNC"),
    (0x4004_667f, "FIONREAD"),
    (0x8004_667c, "FIOSETOWN"),
    (0x4004_667b, "FIOGETOWN"),
    (0x4008_7468, "TIOCGWINSZ"),
    (0x8008_7467, "TIOCSWINSZ"),
    (0x2000_7461, "TIOCSCTTY"),
    (0x2000_7471, "TIOCNOTTY"),
    (0x4004_7477, "TIOCGPGRP"),
    (0x8004_7476, "TIOCSPGRP"),
    (0x4048_7413, "TIOCGETA"),
    (0x8048_7414, "TIOCSETA"),
    (0x2000_7454, "TIOCPTYGRANT"),
    (0x2000_7452, "TIOCPTYUNLK"),
    (0x4080_7453, "TIOCPTYGNAME"),
];

/// The SDK name of an `ioctl` request.
#[must_use]
pub fn ioctl_name(request: u64) -> Option<&'static str> {
    IOCTL_NAMED.iter().find(|(n, _)| *n == request).map(|(_, name)| *name)
}

// ---- sockets ----------------------------------------------------------------

pub const AF_UNIX: i32 = 1;
pub const AF_INET: i32 = 2;
pub const AF_INET6: i32 = 30;
pub const SOCK_STREAM: i32 = 1;
pub const SOCK_DGRAM: i32 = 2;
pub const SOCK_SEQPACKET: i32 = 5;
/// LINUX's `SOCK_CLOEXEC`. Darwin's `sys/socket.h` defines no such flag (nor
/// `SOCK_NONBLOCK`); a type carrying this bit is MEASURED to fail with
/// `EPROTONOSUPPORT`. Named here so a port of Linux code is diagnosable.
pub const LINUX_SOCK_CLOEXEC: i32 = 0x80000;
pub const LINUX_SOCK_NONBLOCK: i32 = 0x800;

// ---- waitpid(2) options ---------------------------------------------------------

pub const WNOHANG: i32 = 0x01;
pub const WUNTRACED: i32 = 0x02;
pub const WCONTINUED: i32 = 0x10;
pub const WNOWAIT: i32 = 0x20;

// ---- sockets options -------------------------------------------------------------

pub const SOL_SOCKET: i32 = 0xffff;
pub const SO_NOSIGPIPE: i32 = 0x1022;

// ---- resource limits --------------------------------------------------------

pub const RLIMIT_NOFILE: i32 = 8;
pub const RLIM_INFINITY: u64 = (1u64 << 63) - 1;
pub const RLIMIT_NAMES: &[(i32, &str)] = &[
    (0, "RLIMIT_CPU"),
    (1, "RLIMIT_FSIZE"),
    (2, "RLIMIT_DATA"),
    (3, "RLIMIT_STACK"),
    (4, "RLIMIT_CORE"),
    (5, "RLIMIT_AS"),
    (6, "RLIMIT_MEMLOCK"),
    (7, "RLIMIT_NPROC"),
    (8, "RLIMIT_NOFILE"),
];

#[must_use]
pub fn rlimit_name(resource: i32) -> Option<&'static str> {
    RLIMIT_NAMES.iter().find(|(n, _)| *n == resource).map(|(_, name)| *name)
}

// ---- posix_spawn attribute flags ---------------------------------------------

pub const POSIX_SPAWN_RESETIDS: i32 = 0x0001;
pub const POSIX_SPAWN_SETPGROUP: i32 = 0x0002;
pub const POSIX_SPAWN_SETSIGDEF: i32 = 0x0004;
pub const POSIX_SPAWN_SETSIGMASK: i32 = 0x0008;
pub const POSIX_SPAWN_SETSCHEDPARAM: i32 = 0x0010;
pub const POSIX_SPAWN_SETSCHEDULER: i32 = 0x0020;
pub const POSIX_SPAWN_SETEXEC: i32 = 0x0040;
pub const POSIX_SPAWN_START_SUSPENDED: i32 = 0x0080;
pub const POSIX_SPAWN_SETSID: i32 = 0x0400;
pub const POSIX_SPAWN_RESLIDE: i32 = 0x0800;
pub const POSIX_SPAWN_CLOEXEC_DEFAULT: i32 = 0x4000;

/// Spawn attribute flags with no descriptor-table effect; the model accepts
/// them and ignores them. Anything else but `CLOEXEC_DEFAULT` is refused.
pub const SPAWN_FD_NEUTRAL_FLAGS: i32 = POSIX_SPAWN_RESETIDS
    | POSIX_SPAWN_SETPGROUP
    | POSIX_SPAWN_SETSIGDEF
    | POSIX_SPAWN_SETSIGMASK
    | POSIX_SPAWN_SETSCHEDPARAM
    | POSIX_SPAWN_SETSCHEDULER
    | POSIX_SPAWN_START_SUSPENDED
    | POSIX_SPAWN_SETSID
    | POSIX_SPAWN_RESLIDE;
