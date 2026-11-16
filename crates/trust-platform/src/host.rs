//! The host state the clauses act on: processes, their descriptor tables, and
//! the open file descriptions those tables name.
//!
//! The shape is the `Trust.Platform` sketch of the M1 plan (§2.2):
//!
//! * a **descriptor table** per process, `fd -> Entry { ofd, cloexec }` —
//!   the close-on-exec bit is per *descriptor*, per *process*;
//! * **open file descriptions** shared by every entry that names them, across
//!   processes (`dup`, `dup2`, `F_DUPFD`, `fork` and `posix_spawn` share; only
//!   creation calls mint a new one). Status flags (`O_NONBLOCK`, `O_APPEND`, …)
//!   live here, which is why `F_SETFL` through one descriptor is visible
//!   through its duplicates — and in a forked child;
//! * a description exists exactly while some entry names it
//!   ([`Host::refs`] `> 0`): `close` drops the description only at zero, and
//!   the peer of a pipe or socketpair end then reads end-of-file;
//! * a process **phase** (`Running`, `ForkedPreExec`, `Execd`, `Exited`), its
//!   thread count, and its `RLIMIT_NOFILE`;
//! * a flat **namespace** of path names to **nodes** (M2): a regular file, a
//!   directory, a character device, a FIFO or a symlink. Every open of one
//!   name reaches one node, which is what `fstat` identity (`dev`, `ino`)
//!   compares and what `flock` conflicts are computed over. A node lives while
//!   it is named, some description is open on it (an unlinked file stays
//!   reachable through its descriptors), or an `open` of it is in flight; each
//!   file has one canonical spelling (v2);
//! * per process, the calls of its threads that have not returned
//!   ([`InFlight`], v2): a waiting `open`'s reserved number, a sleeping
//!   `flock`'s number;
//! * the **`flock` lock lives on the open file description** ([`Ofd::lock`]),
//!   not on a descriptor or a process: every entry naming the description —
//!   a `dup`, a `fork` child's copy — holds it, `LOCK_UN` through any of them
//!   releases it for all, and it ends with the description, i.e. when the LAST
//!   reference in ANY process closes (MEASURED, 2026-10-01).
//!
//! All collections are `BTreeMap`s so a `Host` is `Ord + Hash` with a
//! deterministic iteration order: the derivation can use it directly as a
//! state of an explicit-state exploration ([`Host::canonical`] renumbers the
//! description ids so two hosts that differ only in allocation history
//! compare equal).

use std::collections::{BTreeMap, BTreeSet};

use crate::darwin;

/// A process id in the model. Model pids are allocated sequentially from 1
/// and are NOT the kernel's numbers; the conformance harness maps between them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Pid(pub u32);

/// An open-file-description id (a kernel `fileglob`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OfdId(pub u32);

/// A node of the namespace (a vnode: what `fstat` identifies by `dev`, `ino`).
/// Ids are minted in order and NEVER renumbered or reused within one host's
/// history: a program may hold one (an `fstat` result it compares later), so
/// a renumbering would change what it compares.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);

/// What a node is. Only what changes a clause's outcome is distinguished.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NodeKind {
    Regular,
    Directory,
    /// A character device that never blocks on open (`/dev/null`).
    CharDevice,
    /// A named pipe (`mkfifo`). MEASURED: `open` of the read end blocks until a
    /// writer exists (`O_NONBLOCK`: it does not wait), of the write end until a
    /// reader exists (`O_NONBLOCK`: `ENXIO`), `O_RDWR` never blocks; `flock` on
    /// it, and `O_EXLOCK`/`O_SHLOCK`, fail `ENOTSUP`.
    Fifo,
    /// A symbolic link; its target is [`Node::target`]. MEASURED: `open`
    /// follows it (the descriptor names the target's node), `O_NOFOLLOW` fails
    /// `ELOOP`.
    Symlink,
}

impl NodeKind {
    /// `st_mode & S_IFMT`.
    #[must_use]
    pub fn mode(self) -> i32 {
        match self {
            NodeKind::Regular => darwin::S_IFREG,
            NodeKind::Directory => darwin::S_IFDIR,
            NodeKind::CharDevice => darwin::S_IFCHR,
            NodeKind::Fifo => darwin::S_IFIFO,
            NodeKind::Symlink => darwin::S_IFLNK,
        }
    }

    /// `flock` (and `O_EXLOCK`/`O_SHLOCK`) work on it. MEASURED: a regular
    /// file, a directory and `/dev/null` take locks; a FIFO fails `ENOTSUP`.
    #[must_use]
    pub fn lockable(self) -> bool {
        matches!(self, NodeKind::Regular | NodeKind::Directory | NodeKind::CharDevice)
    }
}

/// A node.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Node {
    pub kind: NodeKind,
    /// A symlink's target path (a name in the same namespace).
    pub target: Option<String>,
}

/// An `flock` lock mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LockMode {
    Shared,
    Exclusive,
}

impl LockMode {
    /// Whether a lock of mode `self` held by ANOTHER description on the same
    /// node keeps a request for `want` from being granted.
    #[must_use]
    pub fn blocks(self, want: LockMode) -> bool {
        self == LockMode::Exclusive || want == LockMode::Exclusive
    }
}

/// One descriptor-table slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Entry {
    pub ofd: OfdId,
    /// `FD_CLOEXEC`: per descriptor, per process; never shared by `dup`.
    pub cloexec: bool,
    /// `FD_CLOFORK` (Darwin 27): closed in the child at `fork`. The model sets
    /// it only on the descriptor `kqueue()` returns (Darwin 27.2), whose entry
    /// `fork` never copies anyway; `F_GETFD` of such an entry is refused by
    /// name, and `F_SETFD` clears it (PLATFORM-KQUEUE-ALIAS-1).
    pub clofork: bool,
}

/// What an open file description is. Only what changes a clause's outcome
/// is distinguished.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OfdKind {
    PipeRead,
    PipeWrite,
    Socket {
        domain: i32,
        ty: i32,
    },
    /// A kqueue. MEASURED on Darwin 25.6: `kqueue()` returns a descriptor
    /// with `FD_CLOEXEC` set; `fork` and `posix_spawn` do not copy ANY entry
    /// naming a kqueue (including `dup`s with `FD_CLOEXEC` clear); `execve`
    /// closes them whatever their `FD_CLOEXEC`.
    Kqueue,
    /// A vnode opened by `open`/`openat` (file, device, directory).
    File,
    /// A description the environment provided whose kind the model does not
    /// know (RL-INIT): treated as an ordinary, fork- and exec-inheritable one.
    Opaque,
}

impl OfdKind {
    /// `fork`/`posix_spawn` copy an entry naming this description.
    #[must_use]
    pub fn inherited_by_fork(self) -> bool {
        !matches!(self, OfdKind::Kqueue)
    }

    /// `execve` keeps a non-cloexec entry naming this description.
    #[must_use]
    pub fn survives_exec(self) -> bool {
        !matches!(self, OfdKind::Kqueue)
    }

    #[must_use]
    pub fn is_socket(self) -> bool {
        matches!(self, OfdKind::Socket { .. })
    }
}

/// The access mode an open file description was created with
/// (`F_GETFL & O_ACCMODE`). `F_SETFL` never changes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Access {
    ReadOnly,
    WriteOnly,
    ReadWrite,
}

impl Access {
    #[must_use]
    pub fn bits(self) -> i32 {
        match self {
            Access::ReadOnly => darwin::O_RDONLY,
            Access::WriteOnly => darwin::O_WRONLY,
            Access::ReadWrite => darwin::O_RDWR,
        }
    }

    #[must_use]
    pub fn from_open_flags(flags: i32) -> Option<Access> {
        match flags & darwin::O_ACCMODE {
            darwin::O_RDONLY => Some(Access::ReadOnly),
            darwin::O_WRONLY => Some(Access::WriteOnly),
            darwin::O_RDWR => Some(Access::ReadWrite),
            _ => None,
        }
    }
}

/// The other end of a pipe or socketpair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Peer {
    /// Not a connected pair (a lone socket, a file, an accepted connection
    /// whose client the model does not track).
    None,
    /// The peer description is still referenced.
    Open(OfdId),
    /// Every reference to the peer is gone: a read here returns end-of-file
    /// once the buffer is empty.
    Closed,
}

/// An open file description.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ofd {
    pub kind: OfdKind,
    pub access: Access,
    /// The `F_SETFL`-settable status bits ([`darwin::SETFL_MASK`]), plus
    /// [`darwin::FWASWRITTEN`] once the description was written to (which
    /// `F_SETFL` keeps).
    pub status: i32,
    pub peer: Peer,
    /// A socket on which `listen(2)` succeeded (`SO_ACCEPTCONN`): `accept`
    /// on any other socket is `EINVAL`.
    pub listening: bool,
    /// Data is pending for a read on this description (its peer wrote,
    /// [`crate::Call::WriteSome`]); contents and byte counts are abstract.
    pub unread: bool,
    /// The namespace node a NAMED open reached ([`crate::Call::OpenPath`]),
    /// shared by every description opened on it. `None` for a description
    /// whose node the model does not know: an anonymous [`crate::Call::Open`]
    /// (two of them may or may not be one file), a pipe, a socket, a kqueue,
    /// an RL-INIT descriptor. `fstat` identity and `flock` need it.
    pub node: Option<NodeId>,
    /// The `flock` lock this description holds, if any.
    pub lock: Option<LockMode>,
}

impl Ofd {
    /// A fresh description of `kind` with no peer, nothing pending, not
    /// listening, no known node and no lock.
    #[must_use]
    pub fn fresh(kind: OfdKind, access: Access, status: i32) -> Ofd {
        Ofd {
            kind,
            access,
            status,
            peer: Peer::None,
            listening: false,
            unread: false,
            node: None,
            lock: None,
        }
    }

    /// What `F_GETFL` answers.
    #[must_use]
    pub fn getfl(&self) -> i32 {
        self.access.bits() | self.status
    }
}

/// Where a process is in its life.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Phase {
    /// The program the model is about (a root).
    Running,
    /// A `fork` child that has not exec'd. `parent_threads` is the parent's
    /// thread count at the fork: when it was > 1 the child may call only
    /// async-signal-safe functions (DR-1).
    ForkedPreExec { parent_threads: u32 },
    /// A `posix_spawn` child between [`crate::Call::SpawnBegin`] and
    /// [`crate::Call::SpawnEnd`]: it holds a copy of its parent's whole table
    /// (close-on-exec entries included) while its file actions run and its
    /// image is activated (MEASURED, Darwin 25.6: a close-on-exec lock stayed
    /// held after the parent's last close in 3626 of 20000 trials beside a
    /// concurrent `posix_spawn`). It runs no code of its own.
    Spawning { parent_threads: u32 },
    /// Running an image installed by `execve` or `posix_spawn`.
    Execd,
    /// Exited, not yet reaped; its table is empty.
    Exited { status: i32 },
}

/// `struct rlimit` for `RLIMIT_NOFILE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Rlimit {
    pub soft: u64,
    pub hard: u64,
}

/// A call one of a process's threads made that has not returned
/// ([`crate::Ret::Pending`]), keyed by the descriptor number it holds
/// ([`Proc::inflight`]). MEASURED, Darwin 25.6 (the M2 model review's probes,
/// re-run 2026-10-01):
///
/// * an `open` allocates its number FIRST: while it waits the number is
///   reserved — `lowest_free` skips it (`dup(0)` answered 4 with 3 reserved),
///   `F_GETFD` and `close` on it are `EBADF`, and `dup2` onto it waits for the
///   open to finish and then replaces its descriptor (1003 ms);
/// * a FIFO open that waits already counts as a reader (a writer): a
///   concurrent `open(O_WRONLY|O_NONBLOCK)` succeeds, and a blocking read
///   open and a blocking write open rendezvous;
/// * an `O_CREAT` open with `O_EXLOCK`/`O_SHLOCK` creates the file BEFORE it
///   takes the lock: a racer may lock the new file first, and the open then
///   fails `EAGAIN` (`O_NONBLOCK`) leaving the file created (46 of 20000);
/// * a `flock` that sleeps holds the description its number named: `close`
///   and `dup2` of that number wait until it returns (1003 ms, 810 ms), and
///   it returns `0` — the lock taken — on a description being closed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InFlight {
    /// An `open` that has not returned: `ofd` is the description it will
    /// install at the reserved number (its node already resolved, or created).
    Open { ofd: Ofd, cloexec: bool, lock: Option<LockMode>, nonblock: bool },
    /// A `flock` sleeping on description `ofd` for a lock of mode `want`.
    Flock { ofd: OfdId, want: LockMode },
}

/// One process.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Proc {
    pub table: BTreeMap<i32, Entry>,
    pub phase: Phase,
    pub threads: u32,
    pub nofile: Rlimit,
    pub parent: Option<Pid>,
    /// Calls of this process's threads that have not returned, by the
    /// descriptor number each holds ([`InFlight`]).
    pub inflight: BTreeMap<i32, InFlight>,
}

impl Proc {
    /// The descriptor numbers this process holds.
    #[must_use]
    pub fn fds(&self) -> BTreeSet<i32> {
        self.table.keys().copied().collect()
    }

    /// Whether the process can take a step of its own.
    #[must_use]
    pub fn is_live(&self) -> bool {
        !matches!(self.phase, Phase::Exited { .. })
    }

    /// Whether `fd` is reserved by an `open` that has not returned.
    #[must_use]
    pub fn reserves(&self, fd: i32) -> bool {
        matches!(self.inflight.get(&fd), Some(InFlight::Open { .. }))
    }
}

/// The whole modeled host.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Host {
    pub(crate) procs: BTreeMap<Pid, Proc>,
    pub(crate) ofds: BTreeMap<OfdId, Ofd>,
    /// `kern.maxfilesperproc`: descriptor numbers at or above
    /// `min(soft RLIMIT_NOFILE, this)` cannot be allocated. MEASURED: Darwin
    /// accepts a soft limit above it (and `RLIM_INFINITY`) without clamping,
    /// and then refuses allocation at it (`F_DUPFD` → `EINVAL`, `dup2` → `EBADF`).
    pub(crate) max_files_per_proc: u64,
    /// The namespace's nodes (M2).
    pub(crate) nodes: BTreeMap<NodeId, Node>,
    /// Path name -> node: one flat namespace, keyed by each file's ONE
    /// canonical absolute spelling ([`Host::canonical_path`]: every other
    /// spelling is refused by name). Directories are not created, and there
    /// is no `link` or `rename`.
    pub(crate) names: BTreeMap<String, NodeId>,
    pub(crate) next_pid: u32,
    pub(crate) next_ofd: u32,
    /// Monotone: node ids are never reused (see [`NodeId`]).
    pub(crate) next_node: u32,
    /// The working directory every modeled process shares (no `chdir` is
    /// modeled, and a `fork` child inherits it), as a canonical absolute path
    /// ([`Host::canonical_path`]); `None`: unknown, and a relative path is
    /// refused by name.
    pub(crate) cwd: Option<String>,
}

/// An error building an initial host (never a platform behaviour).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuildError {
    NoSuchProcess(Pid),
    NoSuchOfd(OfdId),
    SlotTaken {
        pid: Pid,
        fd: i32,
    },
    NegativeFd(i32),
    NameTaken(String),
    NoSuchNode(NodeId),
    /// A path the namespace refuses ([`Host::canonical_path`]).
    BadPath(String),
}

impl Host {
    /// An empty host with the given `kern.maxfilesperproc`.
    #[must_use]
    pub fn new(max_files_per_proc: u64) -> Host {
        Host {
            procs: BTreeMap::new(),
            ofds: BTreeMap::new(),
            max_files_per_proc,
            nodes: BTreeMap::new(),
            names: BTreeMap::new(),
            next_pid: 1,
            next_ofd: 1,
            next_node: 1,
            cwd: None,
        }
    }

    /// Environment setup: the working directory every modeled process shares
    /// (a canonical absolute path); relative paths then resolve against it.
    pub fn set_cwd(&mut self, path: &str) -> Result<(), BuildError> {
        if !path.starts_with('/') {
            return Err(BuildError::BadPath(format!(
                "{path:?}: the working directory is relative"
            )));
        }
        let c = self.canonical_path(path).map_err(BuildError::BadPath)?;
        self.cwd = Some(c);
        Ok(())
    }

    /// The working directory, if the environment set one.
    #[must_use]
    pub fn cwd(&self) -> Option<&str> {
        self.cwd.as_deref()
    }

    /// `path` as the ONE spelling the flat namespace keys its file by, or why
    /// the model refuses it (MEASURED, Darwin 25.6, the M2 model review's P10:
    /// every one of these spellings reaches one node — same `(dev, ino)`, and
    /// a `flock` through one conflicts with a lock through the other):
    ///
    /// * a relative path is joined to the working directory; with none set it
    ///   is refused (a relative and an absolute spelling may name one file);
    /// * `.` and `..` components, an empty component (`//`) and a trailing
    ///   `/` are refused (another spelling of a name);
    /// * a path through `/tmp`, `/var` or `/etc` (symlinks to `/private/…`)
    ///   or `/System/Volumes/Data` (the firmlinked data volume) is refused:
    ///   spell it under `/private`;
    /// * a non-ASCII path is refused (APFS normalizes Unicode);
    /// * a path that differs from an existing name only in ASCII case is
    ///   refused (APFS is case-insensitive by default; a case-sensitive
    ///   volume would make them two files);
    /// * a path whose proper prefix is a symlink of the namespace is refused
    ///   (it resolves through the link; only a final symlink is followed).
    pub fn canonical_path(&self, path: &str) -> Result<String, String> {
        let full = if path.starts_with('/') {
            path.to_string()
        } else {
            match &self.cwd {
                Some(c) if path.is_empty() => c.clone(),
                Some(c) => format!("{c}/{path}"),
                None => {
                    return Err(format!(
                        "{path:?} is relative and the working directory is not modeled: a \
                         relative and an absolute spelling may name one file"
                    ));
                }
            }
        };
        if !full.is_ascii() {
            return Err(format!("{full:?}: a non-ASCII path (APFS normalizes Unicode names)"));
        }
        if full != "/" {
            let comps: Vec<&str> = full[1..].split('/').collect();
            if comps.iter().any(|c| c.is_empty() || *c == "." || *c == "..") {
                return Err(format!(
                    "{full:?}: an empty, `.` or `..` component is another spelling of a name"
                ));
            }
        }
        for alias in ["/tmp", "/var", "/etc", "/System/Volumes/Data"] {
            if full == alias || full.starts_with(&format!("{alias}/")) {
                return Err(format!(
                    "{full:?}: {alias} is another spelling of a directory (a symlink or firmlink \
                     on macOS); spell the path under /private"
                ));
            }
        }
        if !self.names.contains_key(&full)
            && let Some(other) = self.names.keys().find(|n| n.eq_ignore_ascii_case(&full))
        {
            return Err(format!(
                "{full:?} differs from the existing name {other:?} only in case: one file on \
                 APFS (case-insensitive), two on a case-sensitive volume"
            ));
        }
        let mut at = 0;
        while let Some(i) = full[at + 1..].find('/') {
            let prefix = &full[..at + 1 + i];
            if let Some(n) = self.names.get(prefix)
                && self.nodes.get(n).is_some_and(|node| node.kind == NodeKind::Symlink)
            {
                return Err(format!(
                    "{full:?} goes through the symlink {prefix:?}: only a final component's link \
                     is followed"
                ));
            }
            at += 1 + i;
        }
        Ok(full)
    }

    /// The path a symlink at `link` (a canonical name) with target `target`
    /// names: an absolute target as is, a relative one against the LINK's
    /// directory (MEASURED: `sub/rl -> Lease.lock` names `sub/Lease.lock`),
    /// canonicalized.
    pub fn link_target(&self, link: &str, target: &str) -> Result<String, String> {
        if target.starts_with('/') {
            return self.canonical_path(target);
        }
        let dir = link.rfind('/').map_or("", |i| &link[..i]);
        self.canonical_path(&format!("{dir}/{target}"))
    }

    /// Whether some name of the namespace resolves to `node` (through
    /// symlinks): a later open of that name reaches it.
    #[must_use]
    pub fn reachable_by_name(&self, node: NodeId) -> bool {
        self.names.keys().any(|path| {
            let mut name = path.clone();
            for _ in 0..32 {
                let Some(n) = self.names.get(&name) else { return false };
                if *n == node {
                    return true;
                }
                match self.nodes.get(n) {
                    Some(Node { kind: NodeKind::Symlink, target: Some(t) }) => {
                        match self.link_target(&name, t) {
                            Ok(next) => name = next,
                            Err(_) => return false,
                        }
                    }
                    _ => return false,
                }
            }
            false
        })
    }

    /// Environment setup: a name that exists before the program runs (the
    /// system's `/dev/null`, a dead instance's lease file), naming a fresh node
    /// of `kind` (a symlink needs [`Host::add_symlink`]).
    pub fn add_name(&mut self, path: &str, kind: NodeKind) -> Result<NodeId, BuildError> {
        let path = self.canonical_path(path).map_err(BuildError::BadPath)?;
        if self.names.contains_key(&path) {
            return Err(BuildError::NameTaken(path));
        }
        let n = self.mint_node(Node { kind, target: None });
        self.names.insert(path, n);
        Ok(n)
    }

    /// Environment setup: a symlink `path` -> `target`.
    pub fn add_symlink(&mut self, path: &str, target: &str) -> Result<NodeId, BuildError> {
        let path = self.canonical_path(path).map_err(BuildError::BadPath)?;
        if self.names.contains_key(&path) {
            return Err(BuildError::NameTaken(path));
        }
        let n = self.mint_node(Node { kind: NodeKind::Symlink, target: Some(target.to_string()) });
        self.names.insert(path, n);
        Ok(n)
    }

    /// Environment install (RL-INIT, a probe root's stdio): a fresh
    /// description open on namespace node `node` at `fd` in `pid`.
    pub fn install_on_node(
        &mut self,
        pid: Pid,
        fd: i32,
        node: NodeId,
        access: Access,
        cloexec: bool,
    ) -> Result<OfdId, BuildError> {
        if !self.nodes.contains_key(&node) {
            return Err(BuildError::NoSuchNode(node));
        }
        let mut o = Ofd::fresh(OfdKind::File, access, 0);
        o.node = Some(node);
        let ofd = self.mint_ofd(o);
        if let Err(e) = self.install_dup(pid, fd, ofd, cloexec) {
            self.ofds.remove(&ofd);
            return Err(e);
        }
        Ok(ofd)
    }

    /// Environment step (RL-FOREIGN): foreign code's own descriptor at `fd`
    /// in `pid`, unflagged — a fresh description open on a fresh file no name
    /// reaches (a file only foreign code knows; `fstat` answers its own
    /// identity, no other description's).
    pub fn install_foreign_file(&mut self, pid: Pid, fd: i32) -> Result<OfdId, BuildError> {
        let n = self.mint_node(Node { kind: NodeKind::Regular, target: None });
        let r = self.install_on_node(pid, fd, n, Access::ReadWrite, false);
        if r.is_err() {
            self.collect_node(n);
        }
        r
    }

    /// Add a root process (phase `Running`, one thread, empty table).
    pub fn add_root(&mut self, nofile: Rlimit) -> Pid {
        self.add_root_with_threads(nofile, 1)
    }

    /// Add a root process that already runs `threads` threads (a GUI app's
    /// main thread plus its framework threads): a `fork` it makes produces a
    /// child restricted to async-signal-safe calls (DR-1). `threads` is at
    /// least 1.
    pub fn add_root_with_threads(&mut self, nofile: Rlimit, threads: u32) -> Pid {
        let pid = Pid(self.next_pid);
        self.next_pid += 1;
        self.procs.insert(
            pid,
            Proc {
                table: BTreeMap::new(),
                phase: Phase::Running,
                threads: threads.max(1),
                nofile,
                parent: None,
                inflight: BTreeMap::new(),
            },
        );
        pid
    }

    /// Environment install (RL-INIT): a fresh description at `fd` in `pid`.
    pub fn install_fresh(
        &mut self,
        pid: Pid,
        fd: i32,
        kind: OfdKind,
        access: Access,
        status: i32,
        cloexec: bool,
    ) -> Result<OfdId, BuildError> {
        let ofd = self.mint_ofd(Ofd::fresh(kind, access, status & darwin::SETFL_MASK));
        if let Err(e) = self.install_dup(pid, fd, ofd, cloexec) {
            self.ofds.remove(&ofd);
            return Err(e);
        }
        Ok(ofd)
    }

    /// Environment install (RL-INIT): another entry for an existing description.
    pub fn install_dup(
        &mut self,
        pid: Pid,
        fd: i32,
        ofd: OfdId,
        cloexec: bool,
    ) -> Result<(), BuildError> {
        if fd < 0 {
            return Err(BuildError::NegativeFd(fd));
        }
        if !self.ofds.contains_key(&ofd) {
            return Err(BuildError::NoSuchOfd(ofd));
        }
        let proc = self.procs.get_mut(&pid).ok_or(BuildError::NoSuchProcess(pid))?;
        if proc.table.contains_key(&fd) || proc.inflight.contains_key(&fd) {
            return Err(BuildError::SlotTaken { pid, fd });
        }
        proc.table.insert(fd, Entry { ofd, cloexec, clofork: false });
        Ok(())
    }

    /// Link two descriptions as each other's peer (an environment-provided
    /// pipe or socketpair).
    pub fn link_peers(&mut self, a: OfdId, b: OfdId) -> Result<(), BuildError> {
        if !self.ofds.contains_key(&a) {
            return Err(BuildError::NoSuchOfd(a));
        }
        if !self.ofds.contains_key(&b) {
            return Err(BuildError::NoSuchOfd(b));
        }
        if let Some(o) = self.ofds.get_mut(&a) {
            o.peer = Peer::Open(b);
        }
        if let Some(o) = self.ofds.get_mut(&b) {
            o.peer = Peer::Open(a);
        }
        Ok(())
    }

    // ---- reading ----------------------------------------------------------

    #[must_use]
    pub fn proc(&self, pid: Pid) -> Option<&Proc> {
        self.procs.get(&pid)
    }

    pub fn procs(&self) -> impl Iterator<Item = (Pid, &Proc)> {
        self.procs.iter().map(|(p, proc)| (*p, proc))
    }

    #[must_use]
    pub fn ofd(&self, id: OfdId) -> Option<&Ofd> {
        self.ofds.get(&id)
    }

    pub fn ofds(&self) -> impl Iterator<Item = (OfdId, &Ofd)> {
        self.ofds.iter().map(|(o, ofd)| (*o, ofd))
    }

    #[must_use]
    pub fn entry(&self, pid: Pid, fd: i32) -> Option<Entry> {
        self.procs.get(&pid).and_then(|p| p.table.get(&fd)).copied()
    }

    #[must_use]
    pub fn max_files_per_proc(&self) -> u64 {
        self.max_files_per_proc
    }

    #[must_use]
    pub fn node(&self, id: NodeId) -> Option<&Node> {
        self.nodes.get(&id)
    }

    pub fn nodes(&self) -> impl Iterator<Item = (NodeId, &Node)> {
        self.nodes.iter().map(|(n, node)| (*n, node))
    }

    /// The node `path` names, if any (a symlink's own node, not followed).
    #[must_use]
    pub fn name(&self, path: &str) -> Option<NodeId> {
        self.names.get(path).copied()
    }

    pub fn names(&self) -> impl Iterator<Item = (&str, NodeId)> {
        self.names.iter().map(|(p, n)| (p.as_str(), *n))
    }

    /// The next node id this host will mint (it is part of the state: ids are
    /// never reused).
    #[must_use]
    pub fn next_node(&self) -> u32 {
        self.next_node
    }

    /// Every description open on `node`.
    pub fn ofds_on(&self, node: NodeId) -> impl Iterator<Item = (OfdId, &Ofd)> {
        self.ofds.iter().filter(move |(_, o)| o.node == Some(node)).map(|(id, o)| (*id, o))
    }

    /// The `flock` lock a request for `want` by description `me` would wait
    /// for: a lock another description on `me`'s node holds that conflicts.
    #[must_use]
    pub fn lock_blocker(&self, me: OfdId, want: LockMode) -> Option<OfdId> {
        let node = self.ofds.get(&me)?.node?;
        self.ofds_on(node)
            .find(|(id, o)| *id != me && o.lock.is_some_and(|m| m.blocks(want)))
            .map(|(id, _)| id)
    }

    /// Whether FIFO `node` has a reader and a writer: a description open on
    /// it for reading (writing), or an `open` of it for reading (writing)
    /// that has not returned — a waiting opener counts (MEASURED). `except`
    /// leaves out one in-flight open (the one asking).
    #[must_use]
    pub fn fifo_parties(&self, node: NodeId, except: Option<(Pid, i32)>) -> (bool, bool) {
        let mut reads = false;
        let mut writes = false;
        let mut see = |a: Access| {
            reads |= a != Access::WriteOnly;
            writes |= a != Access::ReadOnly;
        };
        for (_, o) in self.ofds_on(node) {
            see(o.access);
        }
        for (pid, p) in &self.procs {
            for (fd, f) in &p.inflight {
                if except == Some((*pid, *fd)) {
                    continue;
                }
                if let InFlight::Open { ofd, .. } = f
                    && ofd.node == Some(node)
                {
                    see(ofd.access);
                }
            }
        }
        (reads, writes)
    }

    /// Entries naming `ofd`, over every process.
    #[must_use]
    pub fn refs(&self, ofd: OfdId) -> usize {
        self.procs.values().map(|p| p.table.values().filter(|e| e.ofd == ofd).count()).sum()
    }

    /// Every (pid, fd) naming `ofd`.
    #[must_use]
    pub fn holders(&self, ofd: OfdId) -> Vec<(Pid, i32)> {
        let mut out = Vec::new();
        for (pid, p) in &self.procs {
            for (fd, e) in &p.table {
                if e.ofd == ofd {
                    out.push((*pid, *fd));
                }
            }
        }
        out
    }

    /// The first descriptor number at or above which `pid` cannot allocate:
    /// `min(soft RLIMIT_NOFILE, kern.maxfilesperproc)`, capped to `i32`.
    #[must_use]
    pub fn alloc_limit(&self, pid: Pid) -> i64 {
        let soft = self.procs.get(&pid).map_or(0, |p| p.nofile.soft);
        let lim = soft.min(self.max_files_per_proc);
        i64::try_from(lim).unwrap_or(i64::MAX).min(i64::from(i32::MAX))
    }

    /// Lowest free descriptor number `>= floor` below the allocation limit.
    #[must_use]
    pub fn lowest_free(&self, pid: Pid, floor: i32) -> Option<i32> {
        let proc = self.procs.get(&pid)?;
        let limit = self.alloc_limit(pid);
        let mut fd = floor.max(0);
        loop {
            if i64::from(fd) >= limit {
                return None;
            }
            if !proc.table.contains_key(&fd) && !proc.reserves(fd) {
                return Some(fd);
            }
            fd = fd.checked_add(1)?;
        }
    }

    /// Whether a read on `pid`'s `fd` would see end-of-file (empty buffer
    /// assumed): `Some(true)` when the peer description is gone, `Some(false)`
    /// while it is referenced, `None` when the model tracks no peer.
    #[must_use]
    pub fn peer_closed(&self, pid: Pid, fd: i32) -> Option<bool> {
        let entry = self.entry(pid, fd)?;
        match self.ofds.get(&entry.ofd)?.peer {
            Peer::None => None,
            Peer::Open(_) => Some(false),
            Peer::Closed => Some(true),
        }
    }

    /// Check the structural invariants every clause preserves:
    /// every entry names a live description, every description is named by
    /// some entry (refs > 0), peers are symmetric, exited processes hold none.
    pub fn check_invariants(&self) -> Result<(), String> {
        for (pid, p) in &self.procs {
            for (fd, e) in &p.table {
                if *fd < 0 {
                    return Err(format!("{pid:?} holds negative fd {fd}"));
                }
                if !self.ofds.contains_key(&e.ofd) {
                    return Err(format!("{pid:?} fd {fd} names dropped {:?}", e.ofd));
                }
            }
            if matches!(p.phase, Phase::Exited { .. }) && !p.table.is_empty() {
                return Err(format!("{pid:?} exited but holds {:?}", p.fds()));
            }
            if !p.inflight.is_empty() && !matches!(p.phase, Phase::Running) {
                return Err(format!("{pid:?} has calls in flight but is {:?}", p.phase));
            }
            for (fd, f) in &p.inflight {
                match f {
                    InFlight::Open { ofd, .. } => {
                        if p.table.contains_key(fd) {
                            return Err(format!("{pid:?} fd {fd} is both open and reserved"));
                        }
                        if !ofd.node.is_some_and(|n| self.nodes.contains_key(&n)) {
                            return Err(format!("{pid:?} fd {fd}: a pending open on no node"));
                        }
                    }
                    InFlight::Flock { ofd, .. } => {
                        if p.table.get(fd).map(|e| e.ofd) != Some(*ofd) {
                            return Err(format!(
                                "{pid:?} fd {fd}: a sleeping flock on {ofd:?} it does not name"
                            ));
                        }
                    }
                }
            }
            if let Some(parent) = p.parent
                && parent == *pid
            {
                return Err(format!("{pid:?} is its own parent"));
            }
        }
        for (path, n) in &self.names {
            if !self.nodes.contains_key(n) {
                return Err(format!("name {path:?} names dropped {n:?}"));
            }
        }
        for (n, node) in &self.nodes {
            let named = self.names.values().any(|m| m == n);
            let open = self.ofds.values().any(|o| o.node == Some(*n)) || self.pending_on(*n);
            if !named && !open {
                return Err(format!("{n:?} is neither named nor open but kept"));
            }
            if (node.kind == NodeKind::Symlink) != node.target.is_some() {
                return Err(format!("{n:?}: a symlink target on a {:?}", node.kind));
            }
            if n.0 >= self.next_node {
                return Err(format!("{n:?} is at or above the node counter {}", self.next_node));
            }
        }
        for (id, o) in &self.ofds {
            if self.refs(*id) == 0 {
                return Err(format!("{id:?} is unreferenced but kept"));
            }
            if let Some(n) = o.node {
                match self.nodes.get(&n) {
                    None => return Err(format!("{id:?} is open on dropped {n:?}")),
                    Some(node) if node.kind == NodeKind::Symlink => {
                        return Err(format!("{id:?} is open on symlink {n:?}"));
                    }
                    Some(_) => {}
                }
            }
            if o.lock.is_some() {
                let lockable = o.kind == OfdKind::File
                    && o.node.and_then(|n| self.nodes.get(&n)).is_some_and(|n| n.kind.lockable());
                if !lockable {
                    return Err(format!("{id:?} holds a lock but is not a lockable vnode"));
                }
                if o.status & darwin::FHASLOCK == 0 {
                    return Err(format!("{id:?} holds a lock without FHASLOCK"));
                }
                if let Some(other) = self.lock_blocker(*id, o.lock.unwrap_or(LockMode::Shared))
                    && o.lock == Some(LockMode::Exclusive)
                {
                    return Err(format!("{id:?} holds LOCK_EX beside {other:?}'s lock"));
                }
            }
            if let Peer::Open(peer) = o.peer {
                match self.ofds.get(&peer) {
                    Some(po) if po.peer == Peer::Open(*id) => {}
                    other => {
                        return Err(format!("{id:?} peer {peer:?} is not symmetric: {other:?}"));
                    }
                }
            }
        }
        Ok(())
    }

    /// Renumber description ids in first-reference order (processes by pid,
    /// descriptors ascending) and reset the pid counter to one past the
    /// largest live pid. Two hosts that differ only in allocation history
    /// become equal; live pids are kept (programs see them). A reaped pid may
    /// be reused by the next `fork` — as a real kernel may — so a consumer
    /// that remembers pids must forget a pid once it is reaped.
    #[must_use]
    pub fn canonical(&self) -> Host {
        let mut map: BTreeMap<OfdId, OfdId> = BTreeMap::new();
        let mut next = 1u32;
        for p in self.procs.values() {
            for e in p.table.values() {
                map.entry(e.ofd).or_insert_with(|| {
                    let id = OfdId(next);
                    next += 1;
                    id
                });
            }
        }
        let remap = |o: OfdId| map.get(&o).copied().unwrap_or(o);
        let procs = self
            .procs
            .iter()
            .map(|(pid, p)| {
                let mut p = p.clone();
                for e in p.table.values_mut() {
                    e.ofd = remap(e.ofd);
                }
                for f in p.inflight.values_mut() {
                    if let InFlight::Flock { ofd, .. } = f {
                        *ofd = remap(*ofd);
                    }
                }
                (*pid, p)
            })
            .collect();
        let ofds = self
            .ofds
            .iter()
            .map(|(id, o)| {
                let mut o = *o;
                if let Peer::Open(p) = o.peer {
                    o.peer = Peer::Open(remap(p));
                }
                (remap(*id), o)
            })
            .collect();
        let next_pid = self.procs.keys().map(|p| p.0).max().map_or(1, |m| m + 1);
        Host {
            procs,
            ofds,
            max_files_per_proc: self.max_files_per_proc,
            nodes: self.nodes.clone(),
            names: self.names.clone(),
            next_pid,
            next_ofd: next,
            // Node ids are kept (a program may hold one), so the counter is too.
            next_node: self.next_node,
            cwd: self.cwd.clone(),
        }
    }

    /// A one-line rendering of EVERY field a clause reads (processes with
    /// their phase, threads, parent and `RLIMIT_NOFILE`; descriptions with
    /// kind, flags, peer, listening, pending data, node and lock; nodes and
    /// names; the host's `kern.maxfilesperproc`), so two hosts that render
    /// equal behave equal.
    /// Allocation counters are not rendered: use it on a [`Host::canonical`]
    /// host when it names a state.
    #[must_use]
    pub fn render(&self) -> String {
        let mut s = format!("maxfiles={} ", self.max_files_per_proc);
        for (pid, p) in &self.procs {
            let phase = match p.phase {
                Phase::Running => "run".to_string(),
                Phase::ForkedPreExec { parent_threads } => format!("forked(pt{parent_threads})"),
                Phase::Spawning { parent_threads } => format!("spawning(pt{parent_threads})"),
                Phase::Execd => "execd".to_string(),
                Phase::Exited { status } => format!("exited({status})"),
            };
            let parent = p.parent.map_or_else(String::new, |q| format!("^p{}", q.0));
            s.push_str(&format!(
                "p{}{parent}[{phase} t{} nofile={}/{}",
                pid.0, p.threads, p.nofile.soft, p.nofile.hard
            ));
            for (fd, e) in &p.table {
                s.push_str(&format!(" {fd}:o{}{}", e.ofd.0, if e.cloexec { "x" } else { "" }));
            }
            for (fd, f) in &p.inflight {
                s.push_str(&format!(" {fd}:{}", render_inflight(f)));
            }
            s.push_str("] ");
        }
        for (id, o) in &self.ofds {
            let peer = match o.peer {
                Peer::None => String::new(),
                Peer::Open(p) => format!("~o{}", p.0),
                Peer::Closed => "~eof".to_string(),
            };
            let node = o.node.map_or_else(String::new, |n| format!("@n{}", n.0));
            let lock = match o.lock {
                None => "",
                Some(LockMode::Shared) => "/SH",
                Some(LockMode::Exclusive) => "/EX",
            };
            s.push_str(&format!(
                "o{}={:?}/{:#x}{peer}{}{}{node}{lock} ",
                id.0,
                o.kind,
                o.getfl(),
                if o.listening { "/listen" } else { "" },
                if o.unread { "/unread" } else { "" }
            ));
        }
        for (n, node) in &self.nodes {
            let target = node.target.as_ref().map_or_else(String::new, |t| format!("->{t:?}"));
            s.push_str(&format!("n{}={:?}{target} ", n.0, node.kind));
        }
        for (path, n) in &self.names {
            s.push_str(&format!("{path:?}=n{} ", n.0));
        }
        if !self.nodes.is_empty() || self.next_node != 1 {
            s.push_str(&format!("nextnode={} ", self.next_node));
        }
        if let Some(c) = &self.cwd {
            s.push_str(&format!("cwd={c:?} "));
        }
        s.trim_end().to_string()
    }

    // ---- crate-internal mutation (only clauses call these) ----------------

    pub(crate) fn mint_ofd(&mut self, ofd: Ofd) -> OfdId {
        let id = OfdId(self.next_ofd);
        self.next_ofd += 1;
        self.ofds.insert(id, ofd);
        id
    }

    pub(crate) fn mint_pid(&mut self) -> Pid {
        let pid = Pid(self.next_pid);
        self.next_pid += 1;
        pid
    }

    /// Remove one entry; drop its description iff that was the last
    /// reference, and mark the peer's end `Closed`.
    pub(crate) fn remove_entry(&mut self, pid: Pid, fd: i32) -> Option<Entry> {
        let entry = self.procs.get_mut(&pid)?.table.remove(&fd)?;
        self.collect(entry.ofd);
        Some(entry)
    }

    /// Drop `ofd` if nothing references it any more — and with it its
    /// `flock` lock (the lock lives on the description); drop its node too
    /// when no name and no other description keeps that.
    pub(crate) fn collect(&mut self, ofd: OfdId) {
        if self.refs(ofd) > 0 {
            return;
        }
        let Some(dropped) = self.ofds.remove(&ofd) else { return };
        if let Peer::Open(peer) = dropped.peer
            && let Some(p) = self.ofds.get_mut(&peer)
        {
            p.peer = Peer::Closed;
        }
        if let Some(n) = dropped.node {
            self.collect_node(n);
        }
    }

    /// Drop `node` if no name, no description and no pending open keeps it.
    pub(crate) fn collect_node(&mut self, node: NodeId) {
        let named = self.names.values().any(|m| *m == node);
        let open = self.ofds.values().any(|o| o.node == Some(node)) || self.pending_on(node);
        if !named && !open {
            self.nodes.remove(&node);
        }
    }

    /// Whether an `open` that has not returned is on `node` (it reaches the
    /// node: a waiting lock open contends for the node's lock).
    #[must_use]
    pub fn pending_on(&self, node: NodeId) -> bool {
        self.procs.values().any(|p| {
            p.inflight
                .values()
                .any(|f| matches!(f, InFlight::Open { ofd, .. } if ofd.node == Some(node)))
        })
    }

    pub(crate) fn mint_node(&mut self, node: Node) -> NodeId {
        let id = NodeId(self.next_node);
        self.next_node += 1;
        self.nodes.insert(id, node);
        id
    }

    pub(crate) fn bind_name(&mut self, path: &str, node: NodeId) {
        self.names.insert(path.to_string(), node);
    }

    /// Remove `path`'s name; its node lives on while a description is open on
    /// it.
    pub(crate) fn unbind_name(&mut self, path: &str) -> Option<NodeId> {
        let n = self.names.remove(path)?;
        self.collect_node(n);
        Some(n)
    }

    pub(crate) fn proc_mut(&mut self, pid: Pid) -> Option<&mut Proc> {
        self.procs.get_mut(&pid)
    }

    pub(crate) fn insert_proc(&mut self, pid: Pid, proc: Proc) {
        self.procs.insert(pid, proc);
    }

    pub(crate) fn remove_proc(&mut self, pid: Pid) -> Option<Proc> {
        self.procs.remove(&pid)
    }

    pub(crate) fn ofd_mut(&mut self, id: OfdId) -> Option<&mut Ofd> {
        self.ofds.get_mut(&id)
    }
}

/// One in-flight call, for [`Host::render`].
fn render_inflight(f: &InFlight) -> String {
    let mode = |m: LockMode| match m {
        LockMode::Shared => "SH",
        LockMode::Exclusive => "EX",
    };
    match f {
        InFlight::Open { ofd, cloexec, lock, nonblock } => format!(
            "pending-open(n{}/{:#x}{}{}{})",
            ofd.node.map_or(0, |n| n.0),
            ofd.getfl(),
            if *cloexec { "x" } else { "" },
            lock.map_or_else(String::new, |m| format!("/{}", mode(m))),
            if *nonblock { "/nb" } else { "" }
        ),
        InFlight::Flock { ofd, want } => format!("pending-flock(o{}/{})", ofd.0, mode(*want)),
    }
}
