//! trust-platform: `Trust.Platform/darwin` ([`PLATFORM_SPEC`], now v7) — the
//! executable Darwin model of descriptors, open file descriptions and
//! processes (v0: the M1 rows of the D-10/D-11(e) plan, §2.2; v1/v2: M2 and
//! its review; v3: the census's X3a rows; v4: Darwin 27's `FD_CLOFORK`
//! refused; v5: the `Command` rows of Trust's std, SP-1; v6: those rows with
//! an explicit Upstream selector; v7: a kqueue's `/dev/fd` alias and its first
//! `F_GETFD` refused; each below).
//!
//! # What it is
//!
//! * [`Host`] — every process's descriptor table (`fd -> {ofd, cloexec}`),
//!   the open file descriptions those entries share (kind, access mode,
//!   status flags, peer), each process's phase, thread count and
//!   `RLIMIT_NOFILE`.
//! * [`Call`] / [`step`] — one pure clause per platform call:
//!   `Host × pid × call × oracle → Host × result`. Nondeterminism the
//!   descriptor model cannot decide (does the path exist? does the image
//!   exec?) is an explicit [`Oracle`] choice, restricted to
//!   [`admissible_failures`]. What the model does not cover is a
//!   [`Refusal::Unmodeled`] that names it.
//! * [`symbols::lookup`] — libc / std import names to clauses or std rows;
//!   an unknown name is an [`symbols::UnmodeledPlatformEffect`].
//! * [`std_summaries`] — std functions (Darwin) as programs over the clauses.
//! * [`script`] — programs over the clauses, evaluated by any [`Semantics`];
//!   straight-line, except where a std row branches on a descriptor number
//!   ([`script::When`], [`script::Assumed`]); the shape the derivation emits
//!   and the replay checks.
//!
//! # Where the definition is checked
//!
//! `tests/conformance_darwin.rs` runs real syscalls on the host (pipe,
//! socketpair, socket, accept, open, kqueue, fcntl, dup, dup2, close, ioctl,
//! fork, exec of a reporter that lists its own descriptors, posix_spawn with
//! file actions and `POSIX_SPAWN_CLOEXEC_DEFAULT`, getrlimit/setrlimit, and
//! the real std functions the rows summarize) and compares every step's
//! result and every process's observable table with [`Darwin`]. The same
//! probes run against a matrix of deliberately wrong specs; each must be
//! caught.
//!
//! # Darwin facts this model encodes that the plan did not have
//!
//! (MEASURED on Darwin 25.6, 2026-09-30; re-checked by the conformance run.)
//!
//! * `kqueue()` descriptors are born `FD_CLOEXEC`; `fork` and `posix_spawn`
//!   copy no entry naming a kqueue (dups included, whatever their
//!   `FD_CLOEXEC`); `execve` closes them even with `FD_CLOEXEC` clear.
//! * `posix_spawn_file_actions_adddup2(fd, fd)` keeps `FD_CLOEXEC` (no
//!   POSIX-2024 clear), with or without `CLOEXEC_DEFAULT`; under
//!   `CLOEXEC_DEFAULT` an entry survives iff `FD_CLOEXEC` is clear AND an
//!   action named it; `addinherit_np` clears `FD_CLOEXEC` (also without
//!   `CLOEXEC_DEFAULT`); `addopen` that lands directly on its target keeps
//!   its own `O_CLOEXEC`.
//! * `setrlimit(RLIMIT_NOFILE)` accepts `RLIM_INFINITY` and soft limits above
//!   `kern.maxfilesperproc` unclamped; allocation stops at
//!   `min(soft, maxfilesperproc)`.
//! * `dup2(fd, fd)` with `fd` at or above the limit is `EBADF`.
//! * `open` at a full table is `EMFILE` even for a missing path.
//! * No `pipe2`, `accept4`, `dup3`, `SOCK_CLOEXEC` or `SOCK_NONBLOCK`
//!   exists in the SDK (nor did `FD_CLOFORK` before Darwin 27: see v4); a
//!   socket type with Linux's `SOCK_CLOEXEC` bit fails `EPROTONOSUPPORT`.
//!   Atomic close-on-exec at creation exists only for `open`/`openat`
//!   (`O_CLOEXEC`), `fcntl` (`F_DUPFD_CLOEXEC`) and, for children,
//!   `POSIX_SPAWN_CLOEXEC_DEFAULT`. (`open` accepts a close-on-FORK bit,
//!   0x08000000, private on Darwin 25.6 and `O_CLOFORK` on 27, which the
//!   model refuses.)
//!
//! Measured after the 2026-09-30 adversarial review (each pinned by a
//! conformance probe or check):
//!
//! * `fork` and `posix_spawn` copy the table WITHOUT a snapshot: a slot
//!   another thread is `dup2`-ing onto, or a description it is moving, can
//!   be missing in the child (about a third of 3000 forks against a racing
//!   `dup2`). [`clauses::step_torn`] executes that outcome; the child's
//!   table is always a subset of an atomic snapshot.
//! * libc validates `posix_spawn_file_actions_add*` descriptors against
//!   `OPEN_MAX` (10240) at ADD time ([`clauses::file_action_add`]).
//! * `open("/dev/fd/N")` names the SAME description as N
//!   ([`Call::OpenAlias`]); `FD_CLOEXEC` is N's OR `O_CLOEXEC`. A kqueue's
//!   alias is refused by name since v7.
//! * `F_SETFL` on a kqueue fails `ENOTTY` for every argument yet changes the
//!   bits; a write sets `FWASWRITTEN` (0x10000) in `F_GETFL`.
//! * `socket` allocates before it checks the shape (`EMFILE` first);
//!   `socketpair` checks the type, then allocates, then connects; `accept`
//!   on a datagram socket is `EOPNOTSUPP` and on a socket that is not
//!   listening `EINVAL`; `addfchdir` fails the spawn on a closed descriptor
//!   (`EBADF`), a kqueue or a pipe (`EINVAL`).
//! * `open` bits with effects the model does not carry (`O_EVTONLY`, the
//!   close-on-fork bit, …) are refused by name; `O_EXLOCK`/`O_SHLOCK` are
//!   refused on an anonymous [`Call::Open`] and executed on a named
//!   [`Call::OpenPath`] (M2).
//!
//! M2 (2026-10-01, `Trust.Platform/darwin/v1`; each a conformance probe or a
//! bespoke multi-process check):
//!
//! * `flock` locks live on the open file DESCRIPTION ([`Ofd::lock`]): a `dup`
//!   and a `fork` child's copy hold it, closing one of two references keeps
//!   it, `LOCK_UN` through any holder releases it for all, and it ends with
//!   the description's last reference — in any process; a child that
//!   inherited it keeps it after its parent's exit;
//! * `flock` on a pipe, socket or kqueue is `ENOTSUP` before `op` is decoded
//!   (a FIFO decodes `op` first: v2); `LOCK_UN` wins over `LOCK_EX` over
//!   `LOCK_SH`, anything else is `EBADF`; a refused `LOCK_EX|LOCK_NB` conversion keeps `LOCK_SH`; a
//!   blocking conversion that must wait drops `LOCK_SH` first (refused by
//!   name); a granted lock sets the sticky `FHASLOCK` (0x4000) in `F_GETFL`;
//! * a flat namespace of nodes ([`Host::name`]): two opens of one path reach
//!   one node (`fstat` identity, `flock` conflicts); FIFO open rules;
//!   symlinks; `openat` reads its `dirfd` only for a relative path; `EMFILE`
//!   precedes every other open error.
//!
//! The M2 review (2026-10-01, `Trust.Platform/darwin/v2`; each a probe or a
//! multi-threaded check whose kernel observation every listed mutant
//! contradicts):
//!
//! * `posix_spawn` is two events ([`Call::SpawnBegin`], [`Call::SpawnEnd`]):
//!   between them the child holds a copy of the caller's whole table,
//!   close-on-exec entries included — a lock its holder's last close
//!   "released" stays held, a pipe's reader sees no end-of-file — and a spawn
//!   that FAILS passes through that window too;
//! * a call that waits is IN FLIGHT ([`InFlight`], [`Ret::Pending`],
//!   [`Call::Resume`]): an `open` reserves its number first (`dup` skips it,
//!   `F_GETFD`/`close` are `EBADF`, `dup2` onto it waits), a waiting FIFO
//!   opener counts as a reader/writer (blocking opens rendezvous), a sleeping
//!   `flock` holds its number (`close`/`dup2` of it wait), and a signal
//!   handler without `SA_RESTART` interrupts either (`EINTR`);
//! * an `O_CREAT` open with a lock bit creates the file, then locks it (a racer
//!   can lock it first: `EAGAIN` with the file left created);
//! * a FIFO's `flock` decodes `op` before it fails `ENOTSUP`;
//! * one spelling per file ([`Host::canonical_path`]): relative paths resolve
//!   against the environment's working directory or are refused, and `.`,
//!   `..`, `//`, `/tmp`/`/var`/`/etc`, a case variant of an existing name and
//!   a path through a symlink are refused by name; a relative symlink target
//!   names a file in the link's directory; `/dev/ptmx` and `/dev/tty` are
//!   refused for a named open.
//!
//! v3 (2026-10-01, `Trust.Platform/darwin/v3`): v2 plus the census's X3a rows
//! (design 2026-10-01 §2.6, built on v0 as `v0+x3a`), each beside a
//! conformance probe and spec mutants:
//!
//! * [`Call::ListOwnFds`] (`proc_pidinfo(getpid(), PROC_PIDLISTFDS)`, refused
//!   for a multithreaded caller) and [`Call::Sysctl`] (reads of
//!   `kern.maxfilesperproc` only), in [`introspect`];
//! * the std rows STD-DROP-FD, STD-THREAD-SPAWN, STD-COMMAND-OUTPUT/STATUS and
//!   STD-COMMANDEXT-EXEC ([`std_summaries`]); STD-FILE-LOCK stays a named gap:
//!   the `flock` clause is in the model, the std row over it is not written.
//!
//! v4 (2026-10-18, `Trust.Platform/darwin/v4`): v3 with `F_SETFD` carrying
//! `FD_CLOFORK` refused by name (PLATFORM-CLOFORK-1). MEASURED on Darwin 27.0
//! (macOS 27.0.1): close-on-fork is a descriptor flag — `F_SETFD` keeps it
//! (`F_SETFD(3)` reads back 3), `O_CLOFORK` and `F_DUPFD_CLOFORK` set it,
//! `dup`/`F_DUPFD` clear it, and `fork` and `posix_spawn` drop the
//! descriptor; on Darwin 25.6, where v0–v3 were measured, `F_SETFD` ignored
//! the bit. v3 ran such a call as if the bit were ignored, so on Darwin 27 its
//! child kept a descriptor the kernel closes. The model has no close-on-fork
//! flag, so every way to set one is now refused (`O_CLOFORK` and
//! `F_DUPFD_CLOFORK` already were); the conformance check
//! `clofork_is_refused_by_name` names which kernel it ran on.
//!
//! v5 (2026-10-21): Trust std SP1 process summaries. The fork path marks
//! child descriptors before hooks; POSIX uses conditional stdio inheritance
//! and CLOEXEC_DEFAULT. Same-number owned stdio clears CLOEXEC, and status
//! relocation retains the parent dup/close window. Raw syscall clauses and
//! CommandExt::exec inheritance retain their contracts. These are still
//! trusted modeled facts, never kernel-checked proofs.
//!
//! v6 (2026-10-22): combine the exact Trust std compositions above with
//! explicit [`std_summaries::CommandStd::Upstream`] rows, the additional
//! [`Call::CloexecFrom`] clause, and generic guarded/assumed script steps.
//! Trust's inherited stdio is conditional, same-number owned stdio clears
//! CLOEXEC, and failed status relocation retains its original writer. These
//! modeled branches no longer require the conservative v5 row assumptions.
//! Explicit `inherit_all_fds` opts out of stripping without selecting the
//! Upstream std's different placement and relocation behavior. Raw syscall
//! contracts, generic assumption refusals, and authority grades are unchanged.
//!
//! v7 (2026-11-06, PLATFORM-KQUEUE-ALIAS-1): v6 with `open("/dev/fd/N")` of
//! a kqueue refused by name. MEASURED on Darwin 27.2 (macOS 27.2): that open
//! is `EACCES` for every access mode, where Darwin 25.6 and 27.0 answered
//! `EBADF`, the answer v0–v6 gave. Every other kind's alias still follows the
//! access rule on 27.2 (pipes, sockets, files, directories, `/dev/null`;
//! MEASURED), and a full table is still `EMFILE` first. The model names no
//! kernel release, so it gives neither errno; the conformance check
//! `kqueue_alias_is_refused_by_name` names which answer its kernel gives.
//! Also on 27.2, the descriptor `kqueue()` returns has `FD_CLOFORK` set
//! (`F_GETFD` reads 3; Darwin 25.6 has no such bit and reads 1), so v7 refuses
//! that `F_GETFD` by name until an `F_SETFD` sets the flags; its `dup`s and an
//! `F_SETFD` read the same on both (`kqueue_getfd_is_refused_by_name`). `fork`
//! never copies a kqueue's entry, so the bit changes nothing else the model runs.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

pub mod call;
pub mod clauses;
pub mod darwin;
pub mod host;
pub mod introspect;
pub mod script;
mod std_execution;
pub mod std_summaries;
pub mod symbols;

pub use call::{Call, FileAction, Oracle, Refusal, Ret, Semantics, SocketOp, Step, SysResult};
pub use clauses::{Admits, Darwin, admissible_failures, oracle_space, step};
pub use darwin::Errno;
pub use host::{
    Access, BuildError, Entry, Host, InFlight, LockMode, Node, NodeId, NodeKind, Ofd, OfdId,
    OfdKind, Peer, Phase, Pid, Proc, Rlimit,
};

/// The model's identity, for verdicts that must name it (I-TARGET-SCOPED).
/// v1 adds the M2 rows: `flock`, named `open`/`openat` (with `O_EXLOCK` /
/// `O_SHLOCK`), `fstat` identity, `mkfifo`, `unlink`, `symlink`. v2 (the M2
/// review): `posix_spawn` in two halves with the child holding the whole
/// table between them, calls in flight (a waiting `open` reserves its number
/// and counts as a FIFO reader/writer, a sleeping `flock` holds its number,
/// `EINTR`), `O_CREAT` before `O_EXLOCK`, a FIFO's `flock` op decoded first,
/// one canonical spelling per file, and cloning devices refused by name. v3:
/// v2 plus the X3a rows (design §2.6, census PR 13; built on v0 as
/// `v0+x3a` and merged onto v2) — the `proc_pidinfo(PROC_PIDLISTFDS)`
/// listing and `sysctlbyname` (`crate::introspect`), and STD-DROP-FD,
/// STD-COMMAND-OUTPUT/STATUS, STD-COMMANDEXT-EXEC, STD-THREAD-SPAWN
/// (`crate::std_summaries`). v4: v3 with `F_SETFD` carrying `FD_CLOFORK`
/// refused by name (Darwin 27 keeps that bit and drops the descriptor at
/// `fork`). v5: Trust std SP1 fork/POSIX rows, same-number stdio
/// placement and status-writer relocation, with the raw clause contracts
/// retained. v6 combines those exact compositions with an explicit Upstream
/// selector, the additional `CloexecFrom` clause, and guarded/assumed scripts.
/// Its identity distinguishes the combined contract from both v5 histories.
/// v7: v6 with `open("/dev/fd/N")` of a kqueue refused by name (Darwin 27.2
/// answers `EACCES` where 25.6 and 27.0 answered `EBADF`), and `F_GETFD` of
/// the descriptor `kqueue()` returned refused until an `F_SETFD` (27.2 sets
/// `FD_CLOFORK` on it).
pub const PLATFORM_SPEC: &str = "Trust.Platform/darwin/v7";

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_x3a;
