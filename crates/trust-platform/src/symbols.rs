//! The symbol table: which clause (or std row) an imported name stands for.
//!
//! The derivation's census (D1) looks every foreign callee and std callee up
//! here. A name this table does not know is an [`UnmodeledPlatformEffect`] —
//! an explicit, named refusal — and NEVER a silent no-op (I-FD-SPECIFIED).
//! The same holds for a name the table knows but whose effect the model does
//! not cover ([`Modeled`] is only returned for names whose every effect on
//! the descriptor/process model is a clause, a std row, a spawn-builder
//! record, or provably nothing).

/// Which clause a modeled libc symbol is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ClauseId {
    Pipe,
    Socketpair,
    Socket,
    SocketOp,
    Accept,
    Open,
    Kqueue,
    Fcntl,
    Dup,
    Dup2,
    Close,
    Ioctl,
    Fork,
    Exec,
    Spawn,
    Getrlimit,
    Setrlimit,
    /// `proc_pidinfo(getpid(), PROC_PIDLISTFDS, …)` (X3a): the caller's own
    /// descriptor listing ([`crate::Call::ListOwnFds`]).
    ListOwnFds,
    /// `sysctlbyname` (X3a): an integer read; only `kern.maxfilesperproc`
    /// ([`crate::Call::Sysctl`]).
    Sysctl,
    Exit,
    Waitpid,
    ThreadCreate,
    /// `flock(2)` (M2).
    Flock,
    /// `openat(2)` (M2): [`crate::Call::OpenPath`] with a `dirfd`.
    Openat,
    /// `fstat(2)` (M2): node identity.
    Fstat,
    /// `mkfifo(3)` (M2).
    Mkfifo,
    /// `unlink(2)` (M2).
    Unlink,
    /// `symlink(2)` (M2).
    Symlink,
}

/// A `posix_spawn_file_actions_*` / `posix_spawnattr_*` call: it builds the
/// data a later [`ClauseId::Spawn`] consumes and touches no host state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SpawnBuilder {
    ActionsInit,
    ActionsDestroy,
    AddClose,
    AddDup2,
    AddOpen,
    AddInherit,
    /// `addchdir(_np)`: a cwd change, no descriptor effect
    /// ([`crate::call::FileAction::Chdir`]).
    AddChdir,
    /// `addfchdir(_np)`: fails the spawn on a closed descriptor, a kqueue or a
    /// non-directory ([`crate::call::FileAction::Fchdir`]).
    AddFchdir,
    AttrInit,
    AttrDestroy,
    AttrSetFlags,
    AttrGetFlags,
    /// signal mask / defaults / pgroup: no descriptor effect.
    AttrNeutral,
}

/// What a known name means for the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Modeled {
    Clause(ClauseId),
    SpawnBuilder(SpawnBuilder),
    /// A std function summarized by the std row with this id
    /// ([`crate::std_summaries`]).
    StdRow(&'static str),
    /// `std::process::Command::spawn`: STD-SPAWN-FORK or STD-SPAWN-POSIX, as
    /// std decides from the command's configuration
    /// ([`crate::std_summaries::spawn_path`]: a `pre_exec` closure,
    /// uid/gid/groups/chroot, a PATH-in-env program, `setsid`, or a
    /// `current_dir` with a relative program all take the fork path on
    /// Darwin).
    StdCommandSpawn,
    /// `std::process::Command::output` (X3a): STD-COMMAND-OUTPUT, the spawn
    /// row plus std's collection and wait
    /// ([`crate::std_summaries::command_row`] with
    /// [`crate::std_summaries::CommandOp::Output`]).
    StdCommandOutput,
    /// `std::process::Command::status` (X3a): STD-COMMAND-STATUS, the spawn
    /// row plus the wait ([`crate::std_summaries::CommandOp::Status`]).
    StdCommandStatus,
    /// `std::os::unix::process::CommandExt::exec` (X3a):
    /// STD-COMMANDEXT-EXEC, the child half of the fork row run by THIS
    /// process ([`crate::std_summaries::CommandOp::Exec`]).
    StdCommandExec,
    /// No effect on descriptors, descriptions, processes or limits.
    Neutral,
}

/// A platform name the model does not cover.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnmodeledPlatformEffect {
    /// The name as looked up.
    pub symbol: String,
    /// Why: "not in the symbol table", or the named gap.
    pub reason: &'static str,
}

impl std::fmt::Display for UnmodeledPlatformEffect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unmodeled platform effect `{}`: {}", self.symbol, self.reason)
    }
}

/// A looked-up name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lookup {
    /// The normalized name the table matched (Mach-O `_` and `$VARIANT`
    /// suffixes removed; Rust generic arguments removed).
    pub normalized: String,
    /// The Mach-O variant suffix, if any (`$NOCANCEL`, `$UNIX2003`, …).
    pub variant: Option<String>,
    pub modeled: Modeled,
}

const LIBC: &[(&str, Modeled)] = &[
    ("pipe", Modeled::Clause(ClauseId::Pipe)),
    ("socketpair", Modeled::Clause(ClauseId::Socketpair)),
    ("socket", Modeled::Clause(ClauseId::Socket)),
    ("bind", Modeled::Clause(ClauseId::SocketOp)),
    ("listen", Modeled::Clause(ClauseId::SocketOp)),
    ("connect", Modeled::Clause(ClauseId::SocketOp)),
    ("shutdown", Modeled::Clause(ClauseId::SocketOp)),
    ("setsockopt", Modeled::Clause(ClauseId::SocketOp)),
    ("getsockopt", Modeled::Clause(ClauseId::SocketOp)),
    ("getsockname", Modeled::Clause(ClauseId::SocketOp)),
    ("getpeername", Modeled::Clause(ClauseId::SocketOp)),
    ("accept", Modeled::Clause(ClauseId::Accept)),
    ("open", Modeled::Clause(ClauseId::Open)),
    ("kqueue", Modeled::Clause(ClauseId::Kqueue)),
    ("fcntl", Modeled::Clause(ClauseId::Fcntl)),
    ("dup", Modeled::Clause(ClauseId::Dup)),
    ("dup2", Modeled::Clause(ClauseId::Dup2)),
    ("close", Modeled::Clause(ClauseId::Close)),
    ("ioctl", Modeled::Clause(ClauseId::Ioctl)),
    ("fork", Modeled::Clause(ClauseId::Fork)),
    ("execve", Modeled::Clause(ClauseId::Exec)),
    ("execv", Modeled::Clause(ClauseId::Exec)),
    ("execvp", Modeled::Clause(ClauseId::Exec)),
    ("execvP", Modeled::Clause(ClauseId::Exec)),
    ("execl", Modeled::Clause(ClauseId::Exec)),
    ("execlp", Modeled::Clause(ClauseId::Exec)),
    ("execle", Modeled::Clause(ClauseId::Exec)),
    ("posix_spawn", Modeled::Clause(ClauseId::Spawn)),
    ("posix_spawnp", Modeled::Clause(ClauseId::Spawn)),
    ("getrlimit", Modeled::Clause(ClauseId::Getrlimit)),
    ("setrlimit", Modeled::Clause(ClauseId::Setrlimit)),
    ("_exit", Modeled::Clause(ClauseId::Exit)),
    ("_Exit", Modeled::Clause(ClauseId::Exit)),
    ("waitpid", Modeled::Clause(ClauseId::Waitpid)),
    ("pthread_create", Modeled::Clause(ClauseId::ThreadCreate)),
    ("flock", Modeled::Clause(ClauseId::Flock)),
    ("openat", Modeled::Clause(ClauseId::Openat)),
    ("fstat", Modeled::Clause(ClauseId::Fstat)),
    ("mkfifo", Modeled::Clause(ClauseId::Mkfifo)),
    ("unlink", Modeled::Clause(ClauseId::Unlink)),
    ("symlink", Modeled::Clause(ClauseId::Symlink)),
    ("posix_spawn_file_actions_init", Modeled::SpawnBuilder(SpawnBuilder::ActionsInit)),
    ("posix_spawn_file_actions_destroy", Modeled::SpawnBuilder(SpawnBuilder::ActionsDestroy)),
    ("posix_spawn_file_actions_addclose", Modeled::SpawnBuilder(SpawnBuilder::AddClose)),
    ("posix_spawn_file_actions_adddup2", Modeled::SpawnBuilder(SpawnBuilder::AddDup2)),
    ("posix_spawn_file_actions_addopen", Modeled::SpawnBuilder(SpawnBuilder::AddOpen)),
    ("posix_spawn_file_actions_addinherit_np", Modeled::SpawnBuilder(SpawnBuilder::AddInherit)),
    ("posix_spawn_file_actions_addchdir", Modeled::SpawnBuilder(SpawnBuilder::AddChdir)),
    ("posix_spawn_file_actions_addchdir_np", Modeled::SpawnBuilder(SpawnBuilder::AddChdir)),
    ("posix_spawn_file_actions_addfchdir", Modeled::SpawnBuilder(SpawnBuilder::AddFchdir)),
    ("posix_spawn_file_actions_addfchdir_np", Modeled::SpawnBuilder(SpawnBuilder::AddFchdir)),
    ("posix_spawnattr_init", Modeled::SpawnBuilder(SpawnBuilder::AttrInit)),
    ("posix_spawnattr_destroy", Modeled::SpawnBuilder(SpawnBuilder::AttrDestroy)),
    ("posix_spawnattr_setflags", Modeled::SpawnBuilder(SpawnBuilder::AttrSetFlags)),
    ("posix_spawnattr_getflags", Modeled::SpawnBuilder(SpawnBuilder::AttrGetFlags)),
    ("posix_spawnattr_setsigmask", Modeled::SpawnBuilder(SpawnBuilder::AttrNeutral)),
    ("posix_spawnattr_setsigdefault", Modeled::SpawnBuilder(SpawnBuilder::AttrNeutral)),
    ("posix_spawnattr_setpgroup", Modeled::SpawnBuilder(SpawnBuilder::AttrNeutral)),
    ("getpid", Modeled::Neutral),
    ("getppid", Modeled::Neutral),
    ("getuid", Modeled::Neutral),
    ("geteuid", Modeled::Neutral),
    ("getgid", Modeled::Neutral),
    ("getegid", Modeled::Neutral),
    ("getdtablesize", Modeled::Neutral),
    ("sigemptyset", Modeled::Neutral),
    ("sigaddset", Modeled::Neutral),
    ("sigfillset", Modeled::Neutral),
    ("sigprocmask", Modeled::Neutral),
    ("pthread_sigmask", Modeled::Neutral),
    ("sigaction", Modeled::Neutral),
    ("signal", Modeled::Neutral),
];

/// Known platform names whose effect the model does NOT cover, with the
/// named gap (so the refusal says what is missing, not just "unknown").
const NAMED_GAPS: &[(&str, &str)] = &[
    (
        "read",
        "read/readv/pread: data and end-of-file are M2 (only std's status-pipe read is summarized)",
    ),
    ("readv", "read/readv/pread: data and end-of-file are M2"),
    ("pread", "read/readv/pread: data and end-of-file are M2"),
    ("write", "write/writev/pwrite: data and EPIPE are M2"),
    ("writev", "write/writev/pwrite: data and EPIPE are M2"),
    ("pwrite", "write/writev/pwrite: data and EPIPE are M2"),
    ("recvmsg", "recvmsg: SCM_RIGHTS arrivals (incl. MSG_CTRUNC installs) are M2"),
    ("sendmsg", "sendmsg: SCM_RIGHTS are M2"),
    ("recv", "recv: data is M2"),
    ("send", "send: data is M2"),
    ("poll", "poll: readiness and POLLHUP are M2"),
    ("select", "select: readiness is M2"),
    ("kevent", "kevent: kqueue registrations are not modeled"),
    (
        "stat",
        "stat/lstat: path stat is not modeled (MEASURED: stat(\"/dev/fd/N\") answers fstat(N)'s \
         inode under devfs's device, EBADF for a closed N; for a kqueue EBADF on Darwin 25.6 and \
         inode 0 on 27.2)",
    ),
    ("lstat", "stat/lstat: path stat is not modeled"),
    ("rename", "rename: namespace moves are not modeled"),
    ("mkdir", "mkdir: the namespace is flat (no directories are created)"),
    ("lockf", "lockf: POSIX record locks (per process, not per description) are not modeled"),
    (
        "kill",
        "kill: signal delivery is not modeled (death by signal is the Exit clause, applied by the environment)",
    ),
    ("vfork", "vfork: shared address space until exec; not modeled"),
    (
        "exit",
        "exit(3): runs atexit handlers and flushes stdio — not async-signal-safe, so in the child \
         of a multithreaded fork it can deadlock holding every inherited descriptor (DR-1); only \
         _exit/_Exit are modeled",
    ),
    ("closefrom", "closefrom: absent on Darwin"),
    ("pipe2", "pipe2: absent on Darwin (std uses pipe + FIOCLEX)"),
    ("accept4", "accept4: absent on Darwin (std uses accept + FIOCLEX)"),
    ("dup3", "dup3: absent on Darwin"),
    ("posix_openpt", "posix_openpt: pty masters are not modeled"),
    ("openpty", "openpty: pty pairs are not modeled"),
    ("forkpty", "forkpty: not modeled"),
    ("fchdir", "fchdir: not modeled"),
    ("chdir", "chdir: cwd is not modeled"),
    ("setsid", "setsid: sessions are not modeled"),
    ("setpgid", "setpgid: process groups are not modeled"),
    ("mmap", "mmap: mappings hold no descriptor but are not modeled"),
];

const STD: &[(&str, Modeled)] = &[
    ("std::io::pipe", Modeled::StdRow("STD-PIPE")),
    ("std::sys::pipe::pipe", Modeled::StdRow("STD-PIPE")),
    ("std::os::unix::net::UnixStream::pair", Modeled::StdRow("STD-PAIR")),
    ("std::os::unix::net::UnixDatagram::pair", Modeled::StdRow("STD-PAIR-DGRAM")),
    ("std::os::unix::net::UnixListener::bind", Modeled::StdRow("STD-UNIX-BIND")),
    ("std::os::unix::net::UnixListener::accept", Modeled::StdRow("STD-ACCEPT")),
    ("std::os::unix::net::UnixStream::connect", Modeled::StdRow("STD-UNIX-CONNECT")),
    ("std::net::TcpListener::accept", Modeled::StdRow("STD-ACCEPT")),
    ("std::os::fd::OwnedFd::try_clone", Modeled::StdRow("STD-TRY-CLONE")),
    ("std::os::fd::BorrowedFd::try_clone_to_owned", Modeled::StdRow("STD-TRY-CLONE")),
    ("std::fs::File::try_clone", Modeled::StdRow("STD-TRY-CLONE")),
    ("std::os::unix::net::UnixStream::try_clone", Modeled::StdRow("STD-TRY-CLONE")),
    ("std::fs::File::open", Modeled::StdRow("STD-OPEN")),
    ("std::fs::File::create", Modeled::StdRow("STD-OPEN")),
    ("std::fs::OpenOptions::open", Modeled::StdRow("STD-OPEN")),
    ("std::process::Command::spawn", Modeled::StdCommandSpawn),
    ("std::os::fd::AsRawFd::as_raw_fd", Modeled::Neutral),
    ("std::os::fd::IntoRawFd::into_raw_fd", Modeled::Neutral),
    ("std::os::fd::FromRawFd::from_raw_fd", Modeled::Neutral),
    // Registration only: the closure runs inside STD-SPAWN-FORK's child.
    ("std::os::unix::process::CommandExt::pre_exec", Modeled::Neutral),
];

/// Remove generic arguments (`<…>`) from a Rust path.
fn strip_generics(path: &str) -> String {
    let mut out = String::with_capacity(path.len());
    let mut depth = 0usize;
    for c in path.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }
    out.replace("::::", "::").trim_end_matches("::").to_string()
}

/// Look a name up: a C function name AS C SPELLS IT (`pipe`, `_exit`,
/// `exit`, `execvp`) or a Rust path (`std::os::unix::net::UnixStream::pair`).
/// No underscore is stripped: `_exit` is `_exit(2)` and `exit` is `exit(3)`,
/// which the model does NOT treat alike. A Mach-O symbol from an import
/// census goes through [`lookup_macho`].
pub fn lookup(name: &str) -> Result<Lookup, UnmodeledPlatformEffect> {
    if name.contains("::") {
        let path = strip_generics(name);
        let path = path.strip_prefix("::").unwrap_or(&path).to_string();
        if let Some((_, m)) = STD.iter().chain(STD_X3A).find(|(n, _)| *n == path) {
            return Ok(Lookup { normalized: path, variant: None, modeled: *m });
        }
        if let Some((_, reason)) = STD_NAMED_GAPS.iter().find(|(n, _)| *n == path) {
            return Err(UnmodeledPlatformEffect { symbol: name.to_string(), reason });
        }
        return Err(UnmodeledPlatformEffect {
            symbol: name.to_string(),
            reason: "not in the std summary table",
        });
    }
    lookup_c(name, name, None)
}

/// Look a Mach-O symbol up (`_pipe`, `__exit`, `_close$NOCANCEL`): exactly
/// one leading `_` is the C name's decoration, so `_exit` is C `exit(3)` —
/// a named gap — and `__exit` is `_exit(2)`. A `$VARIANT` suffix is kept in
/// [`Lookup::variant`]. A symbol without the leading `_` is not a Mach-O C
/// symbol and is refused.
pub fn lookup_macho(symbol: &str) -> Result<Lookup, UnmodeledPlatformEffect> {
    let (base, variant) = match symbol.split_once('$') {
        Some((b, v)) => (b, Some(format!("${v}"))),
        None => (symbol, None),
    };
    let Some(c_name) = base.strip_prefix('_') else {
        return Err(UnmodeledPlatformEffect {
            symbol: symbol.to_string(),
            reason: "not a Mach-O C symbol (no leading `_`)",
        });
    };
    lookup_c(c_name, symbol, variant)
}

fn lookup_c(
    c_name: &str,
    as_given: &str,
    variant: Option<String>,
) -> Result<Lookup, UnmodeledPlatformEffect> {
    if let Some((_, m)) = LIBC.iter().chain(LIBC_X3A).find(|(n, _)| *n == c_name) {
        return Ok(Lookup { normalized: c_name.to_string(), variant, modeled: *m });
    }
    if let Some((_, reason)) = NAMED_GAPS.iter().chain(NAMED_GAPS_X3A).find(|(n, _)| *n == c_name) {
        return Err(UnmodeledPlatformEffect { symbol: as_given.to_string(), reason });
    }
    Err(UnmodeledPlatformEffect {
        symbol: as_given.to_string(),
        reason: "not in the platform symbol table",
    })
}

/// Whether the C function `c_name` may be called in the child of a `fork`
/// made by a multithreaded process (DR-1): POSIX's async-signal-safe list,
/// restricted to the names this table models, plus Darwin's raw-syscall
/// stubs (`ioctl`, `getrlimit`, `setrlimit`: one trap in
/// `libsystem_kernel`, no lock, no allocation) and `execvp`/`execvP` (Darwin's
/// Libc `exec.c` searches PATH with `alloca` and stack buffers — no `malloc`).
/// `exit`, `posix_spawn(p)`, `pthread_create` and every std function are NOT
/// safe there; neither is a name this table does not know.
#[must_use]
pub fn async_signal_safe(c_name: &str) -> bool {
    const SAFE: &[&str] = &[
        "_exit",
        "_Exit",
        "accept",
        "bind",
        "close",
        "connect",
        "dup",
        "dup2",
        "execl",
        "execle",
        "execv",
        "execve",
        "fcntl",
        "fork",
        "getpeername",
        "getsockname",
        "getsockopt",
        "listen",
        "open",
        "pipe",
        "read",
        "setsockopt",
        "shutdown",
        "socket",
        "socketpair",
        "waitpid",
        "write",
        "getpid",
        "getppid",
        "getuid",
        "geteuid",
        "getgid",
        "getegid",
        "sigaction",
        "sigaddset",
        "sigemptyset",
        "sigfillset",
        "sigprocmask",
        "pthread_sigmask",
        "signal",
        // Darwin, beyond POSIX's list (see the doc comment).
        "ioctl",
        "getrlimit",
        "setrlimit",
        // X3a: libproc's `proc_pidinfo` is the `__proc_info` trap and nothing
        // more (Darwin libproc.c; what aterm's strip relies on in the child).
        "proc_pidinfo",
        "execvp",
        "execvP",
        // M2. POSIX lists these four; `flock` is a raw Darwin syscall stub
        // (one trap in libsystem_kernel, no lock, no allocation).
        "fstat",
        "openat",
        "unlink",
        "mkfifo",
        "symlink",
        "flock",
    ];
    SAFE.contains(&c_name)
}

/// What an `open` path names, as far as the model needs to know.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpenPath {
    /// `/dev/null`: a character device that never blocks on open — a fresh
    /// description ([`crate::Call::Open`]).
    DevNull,
    /// `/dev/fd/N` or `/dev/stdin|stdout|stderr`: Darwin's fdesc alias of
    /// descriptor N ([`crate::Call::OpenAlias`]).
    FdAlias(i32),
    /// A device whose every open reaches a DIFFERENT device, or a per-process
    /// alias: refused by name. MEASURED (Darwin 25.6, the M2 model review's
    /// p8): two opens of `/dev/ptmx` stat alike (devfs, one inode) but are two
    /// pty masters (different `rdev`), and their locks do not conflict;
    /// `/dev/tty` is the opener's controlling terminal (`ENXIO` without one).
    Refused(&'static str),
    /// Any other path. It is a fresh description ([`crate::Call::Open`])
    /// ONLY IF it names a regular file, a directory or a non-blocking device:
    /// a FIFO (whose open blocks until a peer opens the other end) and a path
    /// that resolves into `/dev/fd` through a symlink are not modeled, so a
    /// census that cannot rule them out for this path must refuse it.
    Other,
}

/// Classify a literal `open` path.
#[must_use]
pub fn classify_open_path(path: &str) -> OpenPath {
    match path {
        "/dev/null" => OpenPath::DevNull,
        "/dev/ptmx" => OpenPath::Refused(
            "a cloning device: every open is a new pty master (one inode, a different rdev; \
             their locks do not conflict)",
        ),
        "/dev/tty" => {
            OpenPath::Refused("the opener's controlling terminal: a different device per process")
        }
        "/dev/stdin" => OpenPath::FdAlias(0),
        "/dev/stdout" => OpenPath::FdAlias(1),
        "/dev/stderr" => OpenPath::FdAlias(2),
        _ => match path.strip_prefix("/dev/fd/").and_then(|n| n.parse::<i32>().ok()) {
            Some(n) if n >= 0 => OpenPath::FdAlias(n),
            _ => OpenPath::Other,
        },
    }
}

/// Every name the table models (for census joins and coverage reports).
pub fn modeled_names() -> impl Iterator<Item = (&'static str, Modeled)> {
    LIBC.iter().chain(LIBC_X3A).chain(STD.iter()).chain(STD_X3A).copied()
}

/// Every name the table knows is NOT modeled, with its reason.
pub fn named_gaps() -> impl Iterator<Item = (&'static str, &'static str)> {
    NAMED_GAPS.iter().chain(NAMED_GAPS_X3A).chain(STD_NAMED_GAPS).copied()
}

// ---- X3a (design §2.6, census PR 13) --------------------------------------

/// X3a libc names. Each clause is a family the census narrows by its
/// constant operands, refusing the rest as `PC-UNMODELED{symbol, …}`:
/// `proc_pidinfo` only as `(getpid(), PROC_PIDLISTFDS, _, non-NULL, bytes)`;
/// `sysctlbyname` only as a read (`new` NULL) of a constant name into a
/// non-NULL buffer.
const LIBC_X3A: &[(&str, Modeled)] = &[
    ("proc_pidinfo", Modeled::Clause(ClauseId::ListOwnFds)),
    ("sysctlbyname", Modeled::Clause(ClauseId::Sysctl)),
];

/// Names that can create a process, run a program, or reach any descriptor,
/// which the model does not decompose (Critique C-3): a census that meets
/// one must say WHICH gap it met, never "unknown".
const NAMED_GAPS_X3A: &[(&str, &str)] = &[
    (
        "system",
        "system(3): fork + exec of /bin/sh that inherits every descriptor not marked \
         close-on-exec; a spawn site the model does not decompose",
    ),
    (
        "popen",
        "popen(3): a pipe and a spawn of /bin/sh (Darwin Libc); a spawn site the model does \
         not decompose",
    ),
    ("pclose", "pclose(3): closes a popen stream and waits for its shell; not modeled"),
    (
        "daemon",
        "daemon(3): fork, setsid, and 0/1/2 reopened on /dev/null; a spawn site the model does \
         not decompose",
    ),
    (
        "syscall",
        "syscall(2): a system call by number; any descriptor or process effect is possible",
    ),
    ("dlsym", "dlsym(3): a function resolved at run time may be any platform call"),
    ("sysctl", "sysctl(3) by MIB: only sysctlbyname(\"kern.maxfilesperproc\") reads are modeled"),
    (
        "proc_pidfdinfo",
        "proc_pidfdinfo: per-descriptor info is not modeled (only proc_pidinfo \
         PROC_PIDLISTFDS)",
    ),
];

/// X3a std rows.
const STD_X3A: &[(&str, Modeled)] = &[
    ("std::process::Command::output", Modeled::StdCommandOutput),
    ("std::process::Command::status", Modeled::StdCommandStatus),
    ("std::os::unix::process::CommandExt::exec", Modeled::StdCommandExec),
    ("std::thread::spawn", Modeled::StdRow("STD-THREAD-SPAWN")),
    ("std::thread::Builder::spawn", Modeled::StdRow("STD-THREAD-SPAWN")),
    ("std::thread::Builder::spawn_unchecked", Modeled::StdRow("STD-THREAD-SPAWN")),
    ("std::thread::Builder::spawn_scoped", Modeled::StdRow("STD-THREAD-SPAWN")),
    ("std::thread::Scope::spawn", Modeled::StdRow("STD-THREAD-SPAWN")),
];

/// The STD-FILE-LOCK reason (design §2.6 X3): std's `File::lock` family is
/// `flock` on Darwin — verified at this pin, and by the conformance suite's
/// `std_file_lock_is_flock` check. The `flock` clause is in the model since
/// `Trust.Platform/darwin/v1` (M2); the std row that expands the family into
/// it is not written yet, so the family stays a named gap.
const STD_FILE_LOCK_GAP: &str = "STD-FILE-LOCK: std's File::lock/lock_shared/try_lock/\
    try_lock_shared/unlock are flock(fd, LOCK_EX | LOCK_SH [| LOCK_NB] | LOCK_UN) on Darwin \
    (library/std/src/sys/fs/unix.rs:1468-1601 at this pin; tests/conformance_darwin.rs checks \
    it is the description-level flock); the flock clause is in the model (since \
    Trust.Platform/darwin/v1, M2) but the std row over it is not written yet";

/// std paths the table knows and does not model, with the gap.
const STD_NAMED_GAPS: &[(&str, &str)] = &[
    ("std::fs::File::lock", STD_FILE_LOCK_GAP),
    ("std::fs::File::lock_shared", STD_FILE_LOCK_GAP),
    ("std::fs::File::try_lock", STD_FILE_LOCK_GAP),
    ("std::fs::File::try_lock_shared", STD_FILE_LOCK_GAP),
    ("std::fs::File::unlock", STD_FILE_LOCK_GAP),
    (
        "std::process::Child::wait",
        "Child::wait (drop stdin, waitpid): the Child's pipe ends are a CommandRow's `ours`; \
         not yet a row",
    ),
    (
        "std::process::Child::wait_with_output",
        "Child::wait_with_output: not yet a row (Command::output is STD-COMMAND-OUTPUT)",
    ),
    ("std::process::Child::try_wait", "Child::try_wait (waitpid WNOHANG): not yet a row"),
    ("std::process::Child::kill", "Child::kill: signal delivery is not modeled"),
];

/// Types whose drop closes exactly the one descriptor they own: on Unix each
/// wraps a single `OwnedFd` (directly, or through `sys::fd::FileDesc` /
/// `sys::net::Socket` / `sys::pipe::Pipe`), and only `OwnedFd` has a `Drop`
/// impl (`library/std/src/os/fd/owned.rs:196`). Their drop is STD-DROP-FD.
pub const FD_CARRIERS: &[&str] = &[
    "std::os::fd::OwnedFd",
    "std::fs::File",
    "std::os::unix::net::UnixStream",
    "std::os::unix::net::UnixListener",
    "std::os::unix::net::UnixDatagram",
    "std::net::TcpStream",
    "std::net::TcpListener",
    "std::net::UdpSocket",
    "std::process::ChildStdin",
    "std::process::ChildStdout",
    "std::process::ChildStderr",
    "std::io::PipeReader",
    "std::io::PipeWriter",
];

/// Types that OWN descriptors through fields but are not a single carrier:
/// their drop closes several (or none), so a census meeting one must
/// decompose it field by field or refuse it (`PC-DROP-UNMODELED`).
const DROP_NAMED_GAPS: &[(&str, &str)] = &[
    (
        "std::process::Child",
        "dropping a Child closes its stdin/stdout/stderr pipe ends (each STD-DROP-FD) and \
         neither waits nor kills; decompose it by field",
    ),
    (
        "std::process::Command",
        "dropping a Command closes the descriptors its Stdio::from(..) settings own; \
         decompose it by field",
    ),
    ("std::process::Stdio", "a Stdio owns a descriptor only when made from one; decompose it"),
    (
        "std::os::fd::BorrowedFd",
        "a BorrowedFd owns nothing: its drop closes nothing (not a carrier)",
    ),
];

/// What the drop of a value of type `type_path` does (the census's `Drop`
/// of an fd carrier, design §2.4): STD-DROP-FD for a type in
/// [`FD_CARRIERS`] (generic arguments ignored, `<…>` stripped), a named gap
/// for a known composite, otherwise unmodeled.
pub fn lookup_drop(type_path: &str) -> Result<Lookup, UnmodeledPlatformEffect> {
    let path = strip_generics(type_path);
    let path = path.strip_prefix("::").unwrap_or(&path).to_string();
    if FD_CARRIERS.contains(&path.as_str()) {
        return Ok(Lookup {
            normalized: path,
            variant: None,
            modeled: Modeled::StdRow("STD-DROP-FD"),
        });
    }
    if let Some((_, reason)) = DROP_NAMED_GAPS.iter().find(|(n, _)| *n == path) {
        return Err(UnmodeledPlatformEffect { symbol: type_path.to_string(), reason });
    }
    Err(UnmodeledPlatformEffect {
        symbol: type_path.to_string(),
        reason: "the drop of a type the table does not know to carry a descriptor",
    })
}
