//! std summary rows (Darwin): what a std function does to the descriptor
//! model, as a [`Program`] over the clauses.
//!
//! Until std itself has trust-ir these rows are TRUSTED modeled facts
//! (`docs/TCB.md`, the modeled-fact class): each cites the std source it
//! summarizes, and the conformance suite runs the real std function beside
//! the row and compares the outcome. A row's steps are separate events: a
//! non-`atomic` row has an interleaving point between every two steps (the
//! Darwin windows a concurrent `fork` can slip through — RL-STDWIN).
//!
//! Error behaviour, uniform for these rows: a root step that fails ends the
//! row with that error, after closing every descriptor an earlier step of
//! the row returned (std's `OwnedFd` drops). A step std retries on `EINTR`
//! (`cvt_r`) is listed in [`StdRow::retried_eintr`]: `EINTR` is not one of
//! its outcomes. The `Command::spawn` fork row also carries std's error path
//! ([`ForkRow`]): a failing stdio `dup2`, `pre_exec` closure or `execvp` in
//! the child writes an errno message to the status pipe and `_exit(1)`s; the
//! parent's read then returns data, it reaps the child and returns `Err`.
//!
//! The `Command` rows follow the std a program is built with
//! ([`CommandStd`]): Trust's (DECISION_QUEUE SP-1, Trust a7f474346f, shipped
//! in 0.11.0) hands a spawned child its stdio and nothing else; upstream's
//! hands it every descriptor not marked close-on-exec. Trust's rows branch on
//! descriptor numbers where its std does (the exec-status pipe's move, a
//! stdio source already on its target, an inherited stdio slot that would
//! not pass an exec). These branches use the shared primitive compositions.
//! Generic scripts can also use [`crate::script::When`] and
//! [`crate::script::Assumed`]; taking an unsupported assumption still refuses
//! by name. An explicit inheritance opt-out preserves Trust's placement and
//! status relocation rather than selecting upstream's different contract.

use crate::call::{Call, FileAction, SocketOp};
use crate::script::{Actor, Operand, Program, ProgramStep};
use crate::{darwin, introspect};

mod x3a;
pub use x3a::{
    CommandOp, CommandRow, Fidelity, command_row, effective_stdio, fidelity, std_drop_fd,
    std_thread_spawn,
};

/// One std summary row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StdRow {
    pub id: &'static str,
    /// The std paths this row summarizes.
    pub paths: &'static [&'static str],
    /// The std source it was read from (this tree's `library/std/src`).
    pub source: &'static str,
    pub program: Program,
    /// What the std function returns, in terms of the program's results.
    pub returns: Vec<Operand>,
    /// No interleaving point inside the row.
    pub atomic: bool,
    /// Steps std retries on `EINTR` (`cvt_r`): `EINTR` is never their
    /// outcome in the row.
    pub retried_eintr: Vec<usize>,
}

fn r(step: usize, comp: u8) -> Operand {
    Operand::Ret { step, comp }
}

fn fioclex(fd: Operand) -> Call<Operand> {
    Call::Ioctl { fd, request: darwin::FIOCLEX, arg: 0 }
}

/// `std::sys::pipe::pipe` on Darwin: `pipe`, then `FIOCLEX` on each end —
/// three events, two windows (no `pipe2`).
#[must_use]
pub fn std_pipe() -> StdRow {
    StdRow {
        id: "STD-PIPE",
        paths: &["std::io::pipe", "std::sys::pipe::pipe"],
        source: "library/std/src/sys/pipe/unix.rs:8-43",
        program: vec![
            ProgramStep::root(Call::Pipe),
            ProgramStep::root(fioclex(r(0, 0))),
            ProgramStep::root(fioclex(r(0, 1))),
        ],
        returns: vec![r(0, 0), r(0, 1)],
        atomic: false,
        retried_eintr: Vec::new(),
    }
}

/// `Socket::new_pair(AF_UNIX, ty)` on Darwin: `socketpair`, then `FIOCLEX`
/// on each end (no `SOCK_CLOEXEC`).
#[must_use]
pub fn std_pair(ty: i32) -> StdRow {
    StdRow {
        id: if ty == darwin::SOCK_DGRAM { "STD-PAIR-DGRAM" } else { "STD-PAIR" },
        paths: if ty == darwin::SOCK_DGRAM {
            &["std::os::unix::net::UnixDatagram::pair"]
        } else {
            &["std::os::unix::net::UnixStream::pair"]
        },
        source: "library/std/src/sys/net/connection/socket/unix.rs:112-145",
        program: vec![
            ProgramStep::root(Call::Socketpair { domain: darwin::AF_UNIX, ty, protocol: 0 }),
            ProgramStep::root(fioclex(r(0, 0))),
            ProgramStep::root(fioclex(r(0, 1))),
        ],
        returns: vec![r(0, 0), r(0, 1)],
        atomic: false,
        retried_eintr: Vec::new(),
    }
}

/// `Socket::new(AF_UNIX, SOCK_STREAM)` on Apple: `socket`, `set_cloexec`
/// (`FIOCLEX`), then `setsockopt(SOL_SOCKET, SO_NOSIGPIPE, 1)`
/// (`library/std/src/sys/net/connection/socket/unix.rs:94-103`).
fn socket_new_unix_stream() -> Vec<ProgramStep> {
    vec![
        ProgramStep::root(Call::Socket {
            domain: darwin::AF_UNIX,
            ty: darwin::SOCK_STREAM,
            protocol: 0,
        }),
        ProgramStep::root(fioclex(r(0, 0))),
        ProgramStep::root(Call::SocketOp { fd: r(0, 0), op: SocketOp::Setsockopt }),
    ]
}

/// `Socket::new(AF_UNIX, SOCK_STREAM)` + `bind` + `listen`
/// (`UnixListener::bind`).
#[must_use]
pub fn std_unix_listener_bind() -> StdRow {
    let mut program = socket_new_unix_stream();
    program.push(ProgramStep::root(Call::SocketOp { fd: r(0, 0), op: SocketOp::Bind }));
    program.push(ProgramStep::root(Call::SocketOp { fd: r(0, 0), op: SocketOp::Listen }));
    StdRow {
        id: "STD-UNIX-BIND",
        paths: &["std::os::unix::net::UnixListener::bind"],
        source: "library/std/src/sys/net/connection/socket/unix.rs:66-104; library/std/src/os/unix/net/listener.rs:71-90",
        program,
        returns: vec![r(0, 0)],
        atomic: false,
        retried_eintr: Vec::new(),
    }
}

/// `Socket::new(AF_UNIX, SOCK_STREAM)` + `connect` (`UnixStream::connect`).
#[must_use]
pub fn std_unix_stream_connect() -> StdRow {
    let mut program = socket_new_unix_stream();
    program.push(ProgramStep::root(Call::SocketOp { fd: r(0, 0), op: SocketOp::Connect }));
    StdRow {
        id: "STD-UNIX-CONNECT",
        paths: &["std::os::unix::net::UnixStream::connect"],
        source: "library/std/src/sys/net/connection/socket/unix.rs:66-104; library/std/src/os/unix/net/stream.rs:108-125",
        program,
        returns: vec![r(0, 0)],
        atomic: false,
        retried_eintr: Vec::new(),
    }
}

/// `Socket::accept` on Darwin: `accept` (retried on `EINTR`: `cvt_r`), then
/// `FIOCLEX` (no `accept4`). Argument 0 is the listener.
#[must_use]
pub fn std_accept() -> StdRow {
    StdRow {
        id: "STD-ACCEPT",
        paths: &["std::os::unix::net::UnixListener::accept", "std::net::TcpListener::accept"],
        source: "library/std/src/sys/net/connection/socket/unix.rs:243-275",
        program: vec![
            ProgramStep::root(Call::Accept { fd: Operand::Arg(0) }),
            ProgramStep::root(fioclex(r(0, 0))),
        ],
        returns: vec![r(0, 0)],
        atomic: false,
        retried_eintr: vec![0],
    }
}

/// `try_clone` family: `fcntl(fd, F_DUPFD_CLOEXEC, 3)` — ONE atomic event.
/// Argument 0 is the source.
#[must_use]
pub fn std_try_clone() -> StdRow {
    StdRow {
        id: "STD-TRY-CLONE",
        paths: &[
            "std::os::fd::OwnedFd::try_clone",
            "std::os::fd::BorrowedFd::try_clone_to_owned",
            "std::fs::File::try_clone",
            "std::os::unix::net::UnixStream::try_clone",
        ],
        source: "library/std/src/os/fd/owned.rs:113-130",
        program: vec![ProgramStep::root(Call::Fcntl {
            fd: Operand::Arg(0),
            cmd: darwin::F_DUPFD_CLOEXEC,
            arg: 3,
        })],
        returns: vec![r(0, 0)],
        atomic: true,
        retried_eintr: Vec::new(),
    }
}

/// `File::open_c`: `open(path, O_CLOEXEC | access | creation | custom)` —
/// ONE atomic event. `flags` is everything but `O_CLOEXEC`.
#[must_use]
pub fn std_open(flags: i32) -> StdRow {
    StdRow {
        id: "STD-OPEN",
        paths: &["std::fs::File::open", "std::fs::File::create", "std::fs::OpenOptions::open"],
        source: "library/std/src/sys/fs/unix.rs:1381-1392",
        program: vec![ProgramStep::root(Call::Open { flags: flags | darwin::O_CLOEXEC })],
        returns: vec![r(0, 0)],
        atomic: true,
        retried_eintr: Vec::new(),
    }
}

/// STD-OPEN for a path the model's namespace resolves: the same one step as
/// [`std_open`] (`open(path, flags | O_CLOEXEC, 0o666)`, retried on `EINTR`),
/// as a [`Call::OpenPath`] so that two opens of one path reach one node — what
/// `flock` conflicts and `fstat` identity need. `File::open` passes
/// `O_RDONLY`; `File::create` passes `O_WRONLY | O_CREAT | O_TRUNC`.
#[must_use]
pub fn std_open_path(path: &str, flags: i32) -> StdRow {
    StdRow {
        program: vec![ProgramStep::root(Call::OpenPath {
            at: None,
            path: path.to_string(),
            flags: flags | darwin::O_CLOEXEC,
        })],
        ..std_open(flags)
    }
}

/// How one of a `Command`'s stdio streams is configured.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StdioPlan {
    /// `Stdio::inherit()` (what `spawn()` defaults to).
    Inherit,
    /// `Stdio::null()`: `/dev/null`, opened `O_CLOEXEC`, read-only for stdin
    /// and write-only for stdout/stderr, `dup2`'d into place in the child.
    Null,
    /// `Stdio::piped()` (std's `MakePipe`, what `output()` defaults stdout
    /// and stderr to): STD-PIPE (`pipe`, `FIOCLEX` x2); the child `dup2`s the
    /// read end (stdin) or the write end (stdout/stderr) into place, the
    /// parent keeps the other end (`ChildStdin`/`ChildStdout`/`ChildStderr`).
    /// Only a [`CommandRow`] returns that end; [`command_spawn_fork`] and
    /// [`command_spawn_posix`] refuse it.
    Piped,
}

/// Where `Command`'s stdio setup put each stream (`setup_io` and
/// `to_child_stdio`, `library/std/src/sys/process/unix/common.rs:354-440`:
/// stdin, then stdout, then stderr).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct StdioSetup {
    /// What the child `dup2`s onto 0, 1 and 2 (`None`: inherited). Every one
    /// is owned by the row (`ChildStdio::Owned`) and closed by the parent
    /// once the child exists.
    pub(crate) theirs: [Option<Operand>; 3],
    /// What the parent keeps ([`StdioPlan::Piped`]): the `Child`'s handles.
    pub(crate) ours: [Option<Operand>; 3],
}

fn stdio_setup(stdio: [StdioPlan; 3], program: &mut Program) -> StdioSetup {
    let mut s = StdioSetup::default();
    for (i, plan) in stdio.iter().enumerate() {
        match plan {
            StdioPlan::Inherit => {}
            StdioPlan::Null => {
                let access = if i == 0 { darwin::O_RDONLY } else { darwin::O_WRONLY };
                s.theirs[i] = Some(r(program.len(), 0));
                program.push(ProgramStep::root(Call::Open { flags: access | darwin::O_CLOEXEC }));
            }
            StdioPlan::Piped => {
                // `sys::pipe::pipe()`: STD-PIPE; `(reader, writer)`.
                let k = program.len();
                program.push(ProgramStep::root(Call::Pipe));
                program.push(ProgramStep::root(fioclex(r(k, 0))));
                program.push(ProgramStep::root(fioclex(r(k, 1))));
                // `to_child_stdio(readable)`: stdin is readable by the child.
                let (theirs, ours) = if i == 0 { (r(k, 0), r(k, 1)) } else { (r(k, 1), r(k, 0)) };
                s.theirs[i] = Some(theirs);
                s.ours[i] = Some(ours);
            }
        }
    }
    s
}

/// The rows that return no handle for a parent pipe end refuse one.
fn refuse_piped(stdio: [StdioPlan; 3]) -> Result<(), String> {
    if stdio.contains(&StdioPlan::Piped) {
        return Err("Stdio::piped(): the Child's pipe ends are returned only by a CommandRow \
                    (std_summaries::command_row); this row has no handle for them"
            .to_string());
    }
    Ok(())
}

/// Which std a `Command` row summarizes (DECISION_QUEUE SP-1).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum CommandStd {
    /// Trust's std (SP-1, Trust a7f474346f, shipped in 0.11.0): a spawned
    /// child inherits fds 0, 1 and 2 as configured and nothing else. The
    /// posix path sets `POSIX_SPAWN_CLOEXEC_DEFAULT` and names each stdio
    /// slot; the fork path marks every descriptor from 3 up close-on-exec in
    /// the child after placing stdio and before the first `pre_exec` hook
    /// ([`Call::StdMarkCloexec`]), and with hooks attempts to move the
    /// exec-status pipe's write end to 10 or above first, retaining it on
    /// allocation failure. `CommandExt::exec` keeps upstream's inheritance.
    /// The explicit `inherit_all_fds` shape preserves Trust's placement and
    /// relocation while opting out of the strip; the source census still
    /// refuses that API as an unknown `Command` method.
    #[default]
    Trust,
    /// Upstream's std (Trust before 0.11.0): the child inherits every
    /// descriptor not marked close-on-exec at the spawn. Historical fixtures
    /// select this explicitly; the census and program builders use Trust.
    /// Its declared upstream harness premise is conditional evidence,
    /// not a default Trust Command witness: status relocation also changes
    /// descriptor numbers, so this selector supplies no losslessness proof.
    Upstream,
}

/// What std's `Command::spawn` decides its Darwin path from
/// (`library/std/src/sys/process/unix/unix.rs:524-1008`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CommandShape {
    /// Which std builds the child ([`CommandStd`]).
    pub std: CommandStd,
    /// Explicit `CommandExt::inherit_all_fds()`: opt out of the strip while
    /// retaining the selected std's placement and relocation behavior.
    /// The default remains SP1. Historical fixtures and the synthetic hook
    /// harness name this premise; the source census still refuses this API.
    pub inherit_all_fds: bool,
    /// At least one `pre_exec` closure.
    pub pre_exec: bool,
    /// `uid`, `gid`, `groups`, `chroot` set.
    pub uid: bool,
    pub gid: bool,
    pub groups: bool,
    pub chroot: bool,
    /// The command's environment sets `PATH` and the program has no `/`.
    pub path_in_env_bare_program: bool,
    /// `setsid(true)`.
    pub setsid: bool,
    /// `current_dir(..)` set.
    pub cwd: bool,
    /// The program is a relative path containing `/` (`../prog`,
    /// `std::process::ProgramKind::Relative`).
    pub program_relative: bool,
    /// `process_group(..)` set.
    pub pgroup: bool,
}

impl CommandShape {
    /// A command with `pre_exec` closures and nothing else.
    #[must_use]
    pub fn with_pre_exec() -> CommandShape {
        CommandShape { pre_exec: true, ..CommandShape::default() }
    }

    /// This shape under `std`.
    #[must_use]
    pub fn under(self, std: CommandStd) -> CommandShape {
        CommandShape { std, ..self }
    }
}

/// The lowest number Trust's std moves its exec-status write end to when
/// `pre_exec` hooks run (`inherit::STATUS_FD_FLOOR`): above 0..=9, where a
/// hook conventionally places what it hands over.
pub const STATUS_FD_FLOOR: i32 = 10;

/// The first descriptor Trust's strip marks (`inherit::FIRST_STRIPPED`).
pub const FIRST_STRIPPED: i32 = 3;

/// Which Darwin implementation std uses for a command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpawnPath {
    /// `fork` + `execvp` (STD-SPAWN-FORK).
    Fork,
    /// `posix_spawnp` (STD-SPAWN-POSIX).
    Posix,
}

/// std's choice (`unix.rs:537-544`, `:796-805`, `:926-935` on Darwin): the
/// fork path for a `pre_exec` closure, a uid/gid/groups/chroot, a
/// PATH-in-env bare program, `setsid` (Darwin has no
/// `POSIX_SPAWN_SETSID` arm in std), or a `current_dir` with a relative
/// program (macOS's `addchdir_np` misreports `ENOENT` for it).
#[must_use]
pub fn spawn_path(shape: &CommandShape) -> SpawnPath {
    let fork = shape.pre_exec
        || shape.uid
        || shape.gid
        || shape.groups
        || shape.chroot
        || shape.path_in_env_bare_program
        || shape.setsid
        || (shape.cwd && shape.program_relative);
    if fork { SpawnPath::Fork } else { SpawnPath::Posix }
}

/// STD-SPAWN-FORK with its error path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForkRow {
    /// The success path, straight-line.
    pub row: StdRow,
    /// The `fork` step (the child is `Actor::Child(fork)`).
    pub fork: usize,
    /// The child's `execvp` step.
    pub exec: usize,
    /// The parent's status-pipe read ([`Call::ReadSome`]): `0` is success,
    /// data means the child failed.
    pub status_read: usize,
    /// What std's child does after a failing stdio `dup2`, `pre_exec`
    /// closure or `execvp`: write the 8-byte errno message to the status
    /// pipe, `_exit(1)` (`unix.rs:140-161`).
    pub child_error: Vec<Call<Operand>>,
    /// What the parent does when the status read returns data, before the
    /// closes the success path also makes: reap the child (`p.wait()`,
    /// `unix.rs:176-202`), then return `Err`.
    pub parent_error: Vec<Call<Operand>>,
    /// The parent's pipe ends ([`StdioPlan::Piped`]); always `None` from
    /// [`command_spawn_fork`], which refuses `Piped`.
    pub ours: [Option<Operand>; 3],
}

/// `Command::spawn` on Darwin when std takes the FORK path
/// ([`spawn_path`]). Only the child steps that touch descriptors are
/// summarized: a shape with uid/gid/groups/chroot/cwd/pgroup/setsid (child
/// steps the model does not run) is refused by name.
///
/// Root (parent): stdio setup; the status pipe (STD-PIPE: `pipe`, `FIOCLEX`
/// ×2); `fork`. Child: close the status read end; `dup2` each owned stdio
/// into place; mark every descriptor above stdio CLOEXEC; the `pre_exec` closures in registration order (`hooks`, each
/// a list of calls whose operands are literals or the hooks' own
/// [`Operand::Arg`]s); `execvp`. Root: close the status write end; read the
/// status pipe ([`Call::ReadSome`]: end-of-file once the child's exec has
/// closed its cloexec copy); close the read end; drop the child's stdio
/// descriptors.
pub fn command_spawn_fork(
    stdio: [StdioPlan; 3],
    shape: &CommandShape,
    hooks: &[Vec<Call<Operand>>],
) -> Result<ForkRow, String> {
    refuse_piped(stdio)?;
    fork_row(stdio, shape, hooks)
}

/// [`command_spawn_fork`] for any [`StdioPlan`], `Piped` included (its
/// parent ends in [`ForkRow::ours`]).
fn fork_row(
    stdio: [StdioPlan; 3],
    shape: &CommandShape,
    hooks: &[Vec<Call<Operand>>],
) -> Result<ForkRow, String> {
    if spawn_path(shape) != SpawnPath::Fork {
        return Err("std takes the posix_spawnp path for this command".to_string());
    }
    let mut unmodeled = Vec::new();
    for (on, what) in [
        (shape.uid, "setuid"),
        (shape.gid, "setgid"),
        (shape.groups, "setgroups"),
        (shape.chroot, "chroot"),
        (shape.cwd, "chdir"),
        (shape.pgroup, "setpgid"),
        (shape.setsid, "setsid"),
    ] {
        if on {
            unmodeled.push(what);
        }
    }
    if !unmodeled.is_empty() {
        return Err(format!(
            "STD-SPAWN-FORK child steps not modeled: {} (unix.rs:368-420)",
            unmodeled.join(", ")
        ));
    }
    let trust = shape.std == CommandStd::Trust;
    let strip = trust && !shape.inherit_all_fds;
    let mut p: Program = Vec::new();
    let setup = stdio_setup(stdio, &mut p);
    if strip {
        // `FdStrip::prepare` (inherit.rs `descriptor_bound`), before the fork.
        p.push(ProgramStep::root(Call::Sysctl {
            name: introspect::SYSCTL_MAXFILESPERPROC.to_string(),
            oldlen: 4,
        }));
    }
    let pipe_at = p.len();
    p.push(ProgramStep::root(Call::Pipe));
    p.push(ProgramStep::root(fioclex(r(pipe_at, 0))));
    p.push(ProgramStep::root(fioclex(r(pipe_at, 1))));
    // Trust SP1: move the status writer out of conventional hook targets.
    // The helper retains the original on allocation failure, like std.
    let writer = if trust && shape.pre_exec {
        let k = p.len();
        p.push(ProgramStep::root(Call::StdStatusFd { fd: r(pipe_at, 1) }));
        p.push(ProgramStep::root(Call::StdCloseMovedStatus { old: r(pipe_at, 1), new: r(k, 0) }));
        r(k, 0)
    } else {
        r(pipe_at, 1)
    };
    let fork = p.len();
    p.push(ProgramStep::root(Call::Fork));
    let child = Actor::Child(fork);
    p.push(ProgramStep::by(child, Call::Close { fd: r(pipe_at, 0) }));
    let mut retried_eintr = Vec::new();
    for (n, theirs) in setup.theirs.iter().enumerate() {
        if let Some(from) = theirs {
            let target = i32::try_from(n).unwrap_or(0);
            retried_eintr.push(p.len());
            p.push(ProgramStep::by(
                child,
                if trust {
                    Call::StdPlaceFd { from: *from, to: Operand::Lit(target) }
                } else {
                    Call::Dup2 { from: *from, to: Operand::Lit(target) }
                },
            ));
        }
    }
    // Mark, never close: failed exec must still report on the status pipe.
    // Hooks run afterwards so their explicit placements survive exec.
    if strip {
        p.push(ProgramStep::by(child, Call::StdMarkCloexec));
    }
    for hook in hooks {
        for call in hook {
            p.push(ProgramStep::by(child, call.clone()));
        }
    }
    let exec = p.len();
    p.push(ProgramStep::by(child, Call::Exec));
    p.push(ProgramStep::root(Call::Close { fd: writer }));
    let status_read = p.len();
    p.push(ProgramStep::root(Call::ReadSome { fd: r(pipe_at, 0) }));
    p.push(ProgramStep::root(Call::Close { fd: r(pipe_at, 0) }));
    for theirs in setup.theirs.iter().flatten() {
        p.push(ProgramStep::root(Call::Close { fd: *theirs }));
    }
    let row = StdRow {
        id: "STD-SPAWN-FORK",
        paths: &["std::process::Command::spawn", "std::os::unix::process::CommandExt::pre_exec"],
        source: "library/std/src/sys/process/unix/unix.rs; library/std/src/sys/process/unix/inherit.rs",
        program: p,
        returns: vec![r(fork, 0)],
        atomic: false,
        // The child's stdio dup2s are cvt_r (unix.rs:333-352).
        retried_eintr,
    };
    Ok(ForkRow {
        row,
        fork,
        exec,
        status_read,
        child_error: vec![Call::WriteSome { fd: writer }, Call::Exit { status: 1 }],
        parent_error: vec![Call::Waitpid { pid: r(fork, 0), options: 0 }],
        ours: setup.ours,
    })
}

/// `Command::spawn` on Darwin when std takes the `posix_spawnp` path
/// ([`spawn_path`]): stdio setup; ONE `posix_spawnp` with an `adddup2(fd, n)`
/// per owned stdio (same-number sources use `addinherit_np`), conditional
/// `addinherit_np` for open inherited stdio without CLOEXEC, an `addchdir_np` when `current_dir` is set, and
/// `POSIX_SPAWN_SETSIGDEF` (plus `POSIX_SPAWN_SETPGROUP` for a process
/// group) and Trust's `POSIX_SPAWN_CLOEXEC_DEFAULT`; drop the child's
/// stdio descriptors (`unix.rs:690-760`).
pub fn command_spawn_posix(
    stdio: [StdioPlan; 3],
    shape: &CommandShape,
) -> Result<(StdRow, usize), String> {
    refuse_piped(stdio)?;
    posix_row(stdio, shape).map(|(row, spawn, _)| (row, spawn))
}

/// [`command_spawn_posix`] for any [`StdioPlan`], `Piped` included; also
/// returns the parent's pipe ends.
fn posix_row(
    stdio: [StdioPlan; 3],
    shape: &CommandShape,
) -> Result<(StdRow, usize, [Option<Operand>; 3]), String> {
    if spawn_path(shape) != SpawnPath::Posix {
        return Err("std takes the fork path for this command".to_string());
    }
    let trust = shape.std == CommandStd::Trust;
    let strip = trust && !shape.inherit_all_fds;
    let mut p: Program = Vec::new();
    let setup = stdio_setup(stdio, &mut p);
    let mut actions = Vec::new();
    for (n, theirs) in setup.theirs.iter().enumerate() {
        if let Some(from) = theirs {
            let to = Operand::Lit(i32::try_from(n).unwrap_or(0));
            actions.push(if trust {
                FileAction::PlaceStdio { from: *from, to }
            } else {
                FileAction::Dup2 { from: *from, to }
            });
        } else if strip {
            let fd = Operand::Lit(i32::try_from(n).unwrap_or(0));
            let k = p.len();
            p.push(ProgramStep::root(Call::StdPassesExec { fd }));
            actions.push(FileAction::InheritIf { fd, enabled: r(k, 0) });
        }
    }
    if shape.cwd {
        actions.push(FileAction::Chdir);
    }
    let mut flags = darwin::POSIX_SPAWN_SETSIGDEF;
    if strip {
        flags |= darwin::POSIX_SPAWN_CLOEXEC_DEFAULT;
    }
    if shape.pgroup {
        flags |= darwin::POSIX_SPAWN_SETPGROUP;
    }
    let spawn = p.len();
    p.push(ProgramStep::root(Call::Spawn { actions, flags }));
    for theirs in setup.theirs.iter().flatten() {
        p.push(ProgramStep::root(Call::Close { fd: *theirs }));
    }
    let row = StdRow {
        id: "STD-SPAWN-POSIX",
        paths: &["std::process::Command::spawn"],
        source: "library/std/src/sys/process/unix/unix.rs; library/std/src/sys/process/unix/inherit.rs",
        program: p,
        returns: vec![r(spawn, 0)],
        atomic: false,
        retried_eintr: Vec::new(),
    };
    Ok((row, spawn, setup.ours))
}

/// Every fixed (non-parametric) row.
#[must_use]
pub fn rows() -> Vec<StdRow> {
    vec![
        std_pipe(),
        std_pair(darwin::SOCK_STREAM),
        std_pair(darwin::SOCK_DGRAM),
        std_unix_listener_bind(),
        std_unix_stream_connect(),
        std_accept(),
        std_try_clone(),
        std_open(darwin::O_RDONLY),
        std_drop_fd(),
        std_thread_spawn(),
    ]
}

/// The fixed row with this id.
#[must_use]
pub fn row(id: &str) -> Option<StdRow> {
    rows().into_iter().find(|r| r.id == id)
}
