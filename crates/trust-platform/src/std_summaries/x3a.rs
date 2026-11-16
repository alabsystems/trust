//! The X3a std rows (design §2.6, census PR 13): STD-DROP-FD,
//! STD-THREAD-SPAWN, and the `Command` methods past `spawn` —
//! STD-COMMAND-OUTPUT, STD-COMMAND-STATUS, STD-COMMANDEXT-EXEC — as one
//! [`CommandRow`] shape; plus [`fidelity`], each row's declared
//! approximation direction (Critique C-1.3).
//!
//! Read from this tree's `library/std/src` (line numbers at this pin); each
//! is compared with the real std function by `tests/conformance_darwin.rs`.

use super::{
    CommandShape, CommandStd, ForkRow, SpawnPath, StdRow, StdioPlan, fork_row, posix_row, r,
    spawn_path, stdio_setup,
};
use crate::call::Call;
use crate::script::{Operand, Program, ProgramStep};

/// STD-DROP-FD: the drop of an fd carrier
/// ([`crate::symbols::FD_CARRIERS`]) — `OwnedFd::drop`, `close(fd)` with
/// its result IGNORED (`library/std/src/os/fd/owned.rs:196-221`). Argument 0
/// is the descriptor. The row returns nothing; a failing `close` ends it
/// with nothing else to do. Under `ub_checks` (debug builds) std first
/// `fcntl(fd, F_GETFD)`s and aborts on `EBADF` (`sys/fs/unix.rs:1016-1025`):
/// [`fidelity`] lists that as elided.
#[must_use]
pub fn std_drop_fd() -> StdRow {
    StdRow {
        id: "STD-DROP-FD",
        paths: &["std::os::fd::OwnedFd"],
        source: "library/std/src/os/fd/owned.rs:196-221",
        program: vec![ProgramStep::root(Call::Close { fd: Operand::Arg(0) })],
        returns: Vec::new(),
        atomic: true,
        retried_eintr: Vec::new(),
    }
}

/// STD-THREAD-SPAWN: `thread::spawn` / `Builder::spawn{,_unchecked,_scoped}`
/// / `Scope::spawn` — `pthread_attr_init`, `pthread_attr_setstacksize`,
/// `pthread_create`, `pthread_attr_destroy` (`sys/thread/unix.rs:51-110`),
/// of which only `pthread_create` touches the model (one more thread, which
/// makes a later `fork`'s child async-signal-safe-only, DR-1). The closure
/// body is the new thread's own root (the census's `SpawnThread`); this row
/// is the calling thread's side. Returns the `JoinHandle` (no descriptor).
#[must_use]
pub fn std_thread_spawn() -> StdRow {
    StdRow {
        id: "STD-THREAD-SPAWN",
        paths: &[
            "std::thread::spawn",
            "std::thread::Builder::spawn",
            "std::thread::Builder::spawn_unchecked",
            "std::thread::Builder::spawn_scoped",
            "std::thread::Scope::spawn",
        ],
        source: "library/std/src/thread/builder.rs:187-258; library/std/src/sys/thread/unix.rs:51-110",
        program: vec![ProgramStep::root(Call::ThreadCreate)],
        returns: Vec::new(),
        atomic: true,
        retried_eintr: Vec::new(),
    }
}

/// Which `Command` method a [`CommandRow`] summarizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommandOp {
    /// `Command::spawn` (STD-SPAWN-FORK / STD-SPAWN-POSIX), with the
    /// `Child`'s pipe ends in [`CommandRow::ours`].
    Spawn,
    /// `Command::output` (STD-COMMAND-OUTPUT).
    Output,
    /// `Command::status` (STD-COMMAND-STATUS).
    Status,
    /// `CommandExt::exec` (STD-COMMANDEXT-EXEC).
    Exec,
}

impl CommandOp {
    /// The row id.
    #[must_use]
    pub fn row_id(self, path: Option<SpawnPath>) -> &'static str {
        match (self, path) {
            (CommandOp::Spawn, Some(SpawnPath::Posix)) => "STD-SPAWN-POSIX",
            (CommandOp::Spawn, _) => "STD-SPAWN-FORK",
            (CommandOp::Output, _) => "STD-COMMAND-OUTPUT",
            (CommandOp::Status, _) => "STD-COMMAND-STATUS",
            (CommandOp::Exec, _) => "STD-COMMANDEXT-EXEC",
        }
    }
}

/// The stdio a `Command` method runs with: the user's setting where there is
/// one, else the method's default (`setup_io(default, needs_stdin)`,
/// `sys/process/unix/common.rs:354-370`): `spawn`, `status` and `exec` pass
/// `Inherit` with `needs_stdin`; `output` passes `MakePipe` WITHOUT it, so
/// its stdin defaults to `Null` (`sys/process/mod.rs:55`).
#[must_use]
pub fn effective_stdio(op: CommandOp, user: [Option<StdioPlan>; 3]) -> [StdioPlan; 3] {
    let (stdin, out) = match op {
        CommandOp::Output => (StdioPlan::Null, StdioPlan::Piped),
        CommandOp::Spawn | CommandOp::Status | CommandOp::Exec => {
            (StdioPlan::Inherit, StdioPlan::Inherit)
        }
    };
    [user[0].unwrap_or(stdin), user[1].unwrap_or(out), user[2].unwrap_or(out)]
}

/// A `Command` method on Darwin, as one program with its error paths.
///
/// * [`CommandOp::Spawn`], [`CommandOp::Output`], [`CommandOp::Status`]:
///   std's spawn — the posix path or the fork path, as [`spawn_path`]
///   decides — then the method's own tail.
/// * [`CommandOp::Exec`]: the child half of the fork path run by THIS
///   process (`unix.rs:268-292` then `do_exec`, `unix.rs:325-482`): stdio
///   setup, the `dup2`s, the `pre_exec` closures, `execvp`. Not
///   async-signal-safe (it allocates: `os/unix/process.rs:248`), like every
///   std function.
///
/// The success path is [`CommandRow::row`]. A failing ROOT step of the posix
/// path, or of the fork path before its status read, follows the module's
/// uniform rule (the row ends after closing what earlier steps returned).
/// Every other error path is spelled out in [`CommandRow::error_tail`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommandRow {
    pub op: CommandOp,
    /// The stdio the method ran with ([`effective_stdio`]).
    pub stdio: [StdioPlan; 3],
    /// Which spawn implementation std takes; `None` for `Exec`.
    pub path: Option<SpawnPath>,
    pub row: StdRow,
    /// The step that creates the child: `posix_spawnp` or `fork`; `None` for
    /// `Exec`.
    pub spawn: Option<usize>,
    /// The step after which the new image runs: the child's `execvp` (fork
    /// path), the `posix_spawnp` (posix path), this process's `execvp`
    /// (`Exec`).
    pub image: usize,
    /// Fork path: the parent's status-pipe read ([`Call::ReadSome`]: `0` is
    /// success, data means the child failed).
    pub status_read: Option<usize>,
    /// Fork path: what the child does after a failing stdio `dup2`,
    /// `pre_exec` closure or `execvp` (`unix.rs:140-161`).
    pub child_error: Vec<Call<Operand>>,
    /// The root's WHOLE error path, in order (unlike
    /// [`ForkRow::parent_error`], nothing is appended): fork path — after the
    /// status read returns data, reap the child, then drop the status read
    /// end, the child's stdio and the parent's pipe ends (`unix.rs:176-202`,
    /// the drops of `spawn`'s locals); `Exec` — after any failing step, drop
    /// the child stdio (`do_exec`'s argument) and then the parent ends. Empty
    /// on the posix path.
    pub error_tail: Vec<Call<Operand>>,
    /// The parent's pipe ends the method leaves open: `Spawn`'s `Child`
    /// handles; `None` for the methods that consume or drop them.
    pub ours: [Option<Operand>; 3],
}

/// The [`CommandRow`] for `op` on a command with the user's stdio settings
/// `user`, `shape`, and the `pre_exec` closures `hooks` (each a list of
/// calls by the child — or, for `Exec`, by this process).
///
/// Refused (by name, never approximated): a shape whose child steps the
/// model does not run (uid, gid, groups, chroot, cwd on the fork path or in
/// `Exec`, a process group or `setsid` on the fork path or in `Exec`), and
/// `hooks` with a command that takes the posix path (std takes the fork path
/// for any `pre_exec` closure: give the shape `pre_exec`).
pub fn command_row(
    op: CommandOp,
    user: [Option<StdioPlan>; 3],
    shape: &CommandShape,
    hooks: &[Vec<Call<Operand>>],
) -> Result<CommandRow, String> {
    let stdio = effective_stdio(op, user);
    if !hooks.is_empty() && !shape.pre_exec {
        return Err("pre_exec closures on a shape without `pre_exec`".to_string());
    }
    if op == CommandOp::Exec {
        return exec_row(stdio, shape, hooks);
    }
    let path = spawn_path(shape);
    let mut error_tail = Vec::new();
    let (mut program, pid, image, status_read, child_error, mut retried_eintr, ours) = match path {
        SpawnPath::Posix => {
            let (row, spawn, ours) = posix_row(stdio, shape)?;
            (row.program, spawn, spawn, None, Vec::new(), row.retried_eintr, ours)
        }
        SpawnPath::Fork => {
            let ForkRow { row, fork, exec, status_read, child_error, ours, .. } =
                fork_row(stdio, shape, hooks)?;
            // `spawn` returning `Err` from its status loop: reap, then its
            // locals drop — the status read end, the child stdio
            // (`theirs`), then the parent ends (`ours`).
            error_tail.push(Call::Waitpid { pid: r(fork, 0), options: 0 });
            error_tail.extend(status_end(&row.program, status_read).map(|fd| Call::Close { fd }));
            let theirs = theirs_of(&row.program, &row.retried_eintr);
            error_tail.extend(theirs.iter().flatten().map(|fd| Call::Close { fd: *fd }));
            error_tail.extend(ours.iter().flatten().map(|fd| Call::Close { fd: *fd }));
            (row.program, fork, exec, Some(status_read), child_error, row.retried_eintr, ours)
        }
    };
    let child = r(pid, 0);
    let wait = match op {
        CommandOp::Output => Some(output_tail(&mut program, child, ours)),
        CommandOp::Status => Some(status_tail(&mut program, child, ours)),
        CommandOp::Spawn | CommandOp::Exec => None,
    };
    let (returns, left_open) = match wait {
        Some(wait) => {
            // `Process::wait`'s waitpid is `cvt_r` (unix.rs:1206).
            retried_eintr.push(wait);
            (vec![r(wait, 0)], [None; 3])
        }
        None => (vec![child], ours),
    };
    let row = StdRow {
        id: op.row_id(Some(path)),
        paths: match op {
            CommandOp::Spawn => &["std::process::Command::spawn"],
            CommandOp::Output => &["std::process::Command::output"],
            CommandOp::Status => &["std::process::Command::status"],
            CommandOp::Exec => &[],
        },
        source: match op {
            CommandOp::Spawn => {
                "library/std/src/sys/process/unix/unix.rs; library/std/src/sys/process/unix/inherit.rs"
            }
            CommandOp::Output => {
                "library/std/src/process.rs:1138-1141; library/std/src/sys/process/mod.rs:54-77; \
                 library/std/src/sys/process/unix/common.rs:354-440,636-685; \
                 library/std/src/sys/process/unix/unix.rs; library/std/src/sys/process/unix/inherit.rs"
            }
            CommandOp::Status => {
                "library/std/src/process.rs:1176-1181,2395-2398; \
                 library/std/src/sys/process/unix/unix.rs; library/std/src/sys/process/unix/inherit.rs"
            }
            CommandOp::Exec => "",
        },
        retried_eintr,
        program,
        returns,
        atomic: false,
    };
    Ok(CommandRow {
        op,
        stdio,
        path: Some(path),
        row,
        spawn: Some(pid),
        image,
        status_read,
        child_error,
        error_tail,
        ours: left_open,
    })
}

/// The child stdio a fork row `dup2`s into place, by target (read back from
/// the row's child steps, which [`fork_row`] emits in stdin..stderr order).
fn theirs_of(program: &Program, dup2s: &[usize]) -> [Option<Operand>; 3] {
    let mut out = [None; 3];
    for k in dup2s {
        if let Some(ProgramStep { call: Call::StdPlaceFd { from, to: Operand::Lit(n) }, .. }) =
            program.get(*k)
            && let Some(slot) = usize::try_from(*n).ok().and_then(|n| out.get_mut(n))
        {
            *slot = Some(*from);
        }
    }
    out
}

/// The status pipe's read end, from the fork row's status read.
fn status_end(program: &Program, status_read: usize) -> Option<Operand> {
    match program.get(status_read).map(|ps| &ps.call) {
        Some(Call::ReadSome { fd }) => Some(*fd),
        _ => None,
    }
}

/// `sys::process::output` after the spawn (`sys/process/mod.rs:57-75`):
/// drop the stdin end; read each piped stream to end of file (with both
/// piped, `read_output`, whose arguments drop in reverse order: stderr's end,
/// then stdout's); `process.wait()`. Returns the `waitpid` step.
fn output_tail(p: &mut Program, child: Operand, ours: [Option<Operand>; 3]) -> usize {
    if let Some(stdin) = ours[0] {
        p.push(ProgramStep::root(Call::Close { fd: stdin }));
    }
    match (ours[1], ours[2]) {
        (None, None) => {}
        (Some(one), None) | (None, Some(one)) => {
            p.push(ProgramStep::root(Call::ReadSome { fd: one }));
            p.push(ProgramStep::root(Call::Close { fd: one }));
        }
        (Some(out), Some(err)) => {
            p.push(ProgramStep::root(Call::ReadSome { fd: out }));
            p.push(ProgramStep::root(Call::ReadSome { fd: err }));
            p.push(ProgramStep::root(Call::Close { fd: err }));
            p.push(ProgramStep::root(Call::Close { fd: out }));
        }
    }
    let wait = p.len();
    p.push(ProgramStep::root(Call::Waitpid { pid: child, options: 0 }));
    wait
}

/// `Command::status` after the spawn (`process.rs:1176-1181`):
/// `Child::wait` drops the stdin end and reaps (`process.rs:2395-2398`,
/// `unix.rs:1194-1209`), then the `Child` drops its stdout and stderr ends.
/// Returns the `waitpid` step.
fn status_tail(p: &mut Program, child: Operand, ours: [Option<Operand>; 3]) -> usize {
    if let Some(stdin) = ours[0] {
        p.push(ProgramStep::root(Call::Close { fd: stdin }));
    }
    let wait = p.len();
    p.push(ProgramStep::root(Call::Waitpid { pid: child, options: 0 }));
    for o in ours[1..].iter().flatten() {
        p.push(ProgramStep::root(Call::Close { fd: *o }));
    }
    wait
}

/// STD-COMMANDEXT-EXEC: `Command::exec(Stdio::Inherit)` (`unix.rs:268-292`)
/// in this process: `setup_io(Inherit, true)`, then `do_exec`
/// (`unix.rs:325-482`) — each child stdio `dup2`'d into place (`cvt_r`),
/// the `pre_exec` closures, `execvp`. On success nothing returns (the owned
/// stdio and the parent pipe ends are `O_CLOEXEC`, so the exec closes them);
/// on failure `do_exec`'s argument drops the child stdio, then the parent
/// ends drop — the `dup2`s already made stay made. Trust's std keeps
/// upstream's inheritance here (no strip: a failed exec would leave this
/// process's own table stripped), but its `place` clears `FD_CLOEXEC` on a
/// source already on its target instead of `dup2`ing it, a branch the row
/// refuses by name.
fn exec_row(
    stdio: [StdioPlan; 3],
    shape: &CommandShape,
    hooks: &[Vec<Call<Operand>>],
) -> Result<CommandRow, String> {
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
            "STD-COMMANDEXT-EXEC steps not modeled: {} (unix.rs:368-420)",
            unmodeled.join(", ")
        ));
    }
    let mut p: Program = Vec::new();
    let setup = stdio_setup(stdio, &mut p);
    let mut retried_eintr = Vec::new();
    for (n, theirs) in setup.theirs.iter().enumerate() {
        if let Some(from) = theirs {
            let to = Operand::Lit(i32::try_from(n).unwrap_or(0));
            // `place(fd, n)`: `cvt_r(|| dup2(fd, n))` (unix.rs:333-352).
            retried_eintr.push(p.len());
            p.push(ProgramStep::root(if shape.std == CommandStd::Trust {
                Call::StdPlaceFd { from: *from, to }
            } else {
                Call::Dup2 { from: *from, to }
            }));
        }
    }
    for hook in hooks {
        for call in hook {
            p.push(ProgramStep::root(call.clone()));
        }
    }
    let image = p.len();
    p.push(ProgramStep::root(Call::Exec));
    let mut error_tail: Vec<Call<Operand>> =
        setup.theirs.iter().flatten().map(|fd| Call::Close { fd: *fd }).collect();
    error_tail.extend(setup.ours.iter().flatten().map(|fd| Call::Close { fd: *fd }));
    let row = StdRow {
        id: CommandOp::Exec.row_id(None),
        paths: &["std::os::unix::process::CommandExt::exec"],
        source: "library/std/src/os/unix/process.rs:247-251; \
                 library/std/src/sys/process/unix/unix.rs:268-292,325-482; \
                 library/std/src/sys/process/unix/common.rs:354-440",
        retried_eintr,
        program: p,
        returns: Vec::new(),
        atomic: false,
    };
    Ok(CommandRow {
        op: CommandOp::Exec,
        stdio,
        path: None,
        row,
        spawn: None,
        image,
        status_read: None,
        child_error: Vec::new(),
        error_tail,
        ours: [None; 3],
    })
}

/// A row's approximation direction (Critique C-1.3): what std does that the
/// row leaves out (`under`: a verdict that passes must print it as a
/// premise) and what the row admits that std cannot do (`over`: a refutation
/// that relies on it is not an error, `PC-OVERAPPROX`). A row with neither
/// is exact for the descriptor and process model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fidelity {
    pub under: &'static [&'static str],
    pub over: &'static [&'static str],
}

const EXACT: Fidelity = Fidelity { under: &[], over: &[] };

/// The declared [`Fidelity`] of the row `id` (every id [`super::rows`],
/// [`super::std_open`], [`super::command_spawn_fork`],
/// [`super::command_spawn_posix`] and [`command_row`] produce); `None` for
/// an unknown id, which a census must refuse.
#[must_use]
pub fn fidelity(id: &str) -> Option<Fidelity> {
    Some(match id {
        "STD-PIPE" | "STD-PAIR" | "STD-PAIR-DGRAM" | "STD-TRY-CLONE" => EXACT,
        "STD-UNIX-BIND" | "STD-UNIX-CONNECT" | "STD-ACCEPT" | "STD-OPEN" => Fidelity {
            under: &[],
            over: &["the address or path is not modeled: its failures are oracle choices"],
        },
        "STD-SPAWN-FORK" | "STD-SPAWN-POSIX" | "STD-COMMAND-STATUS" => Fidelity {
            under: &[],
            over: &["the image is not modeled: whether it execs is an oracle choice"],
        },
        "STD-COMMAND-OUTPUT" => Fidelity {
            under: &[
                "read_output's O_NONBLOCK toggles (fcntl F_GETFL/F_SETFL) on the parent's read \
                 ends and its poll loop (sys/process/unix/common.rs:641-685) are not steps: \
                 they change only the status bits of descriptions private to the row and \
                 closed before it returns",
                "read_to_end is one end-of-file read per stream: the exec'd image's output is \
                 not modeled; a read error panics (sys/process/mod.rs:63,67,71)",
            ],
            over: &["the image is not modeled: whether it execs is an oracle choice"],
        },
        "STD-COMMANDEXT-EXEC" => Fidelity {
            under: &[],
            over: &["the image is not modeled: whether it execs is an oracle choice"],
        },
        "STD-DROP-FD" => Fidelity {
            under: &[
                "under ub_checks (debug builds) std first fcntl(fd, F_GETFD)s and aborts the \
                 process on EBADF (sys/fs/unix.rs:1016-1025); the row is the release shape",
            ],
            over: &[],
        },
        "STD-THREAD-SPAWN" => Fidelity {
            under: &["spawn hooks (thread::add_spawn_hook) run in the new thread and are not \
                 summarized"],
            over: &["a thread is never counted out (join and thread exit are not modeled), so a \
                 later fork's child is held to async-signal-safety (DR-1) even after a join"],
        },
        _ => return None,
    })
}
