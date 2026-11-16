//! State-dependent Trust std operations, composed from the same primitive
//! clauses as every other platform event. No conformance-only table edits.

use crate::call::{Call, FileAction, Oracle, Refusal, Ret, Semantics, Step};
use crate::darwin;
use crate::host::{Host, Phase, Pid};

fn unsupported(call: &Call, detail: &str) -> Refusal {
    Refusal::Unmodeled { symbol: call.symbol(), detail: detail.to_string() }
}

fn result(host: &Host, value: i32) -> Step {
    Step { host: host.clone(), result: Ok(Ret::Int(i64::from(value))) }
}

/// Resolve std builder decisions captured before the table-copy window.
/// Existing literal POSIX actions retain their original meaning.
pub(crate) fn actions(input: &[FileAction]) -> Result<Vec<FileAction>, Refusal> {
    let mut out = Vec::with_capacity(input.len());
    for action in input {
        match *action {
            FileAction::InheritIf { fd, enabled: 1 } => out.push(FileAction::Inherit { fd }),
            FileAction::InheritIf { enabled: 0, .. } => {}
            FileAction::InheritIf { .. } => {
                return Err(Refusal::Unmodeled {
                    symbol: "std::process::passes_exec",
                    detail: "a captured inheritance guard must be exactly zero or one".to_string(),
                });
            }
            FileAction::PlaceStdio { from, to } if from == to => {
                out.push(FileAction::Inherit { fd: from });
            }
            FileAction::PlaceStdio { from, to } => out.push(FileAction::Dup2 { from, to }),
            _ => out.push(*action),
        }
    }
    Ok(out)
}

fn clear<S: Semantics + ?Sized>(sem: &S, host: &Host, pid: Pid, fd: i32) -> Result<Step, Refusal> {
    // Other threads could replace this number between the read and write.
    if host.proc(pid).is_some_and(|p| p.threads != 1) {
        return Err(unsupported(
            &Call::StdClearCloexec { fd },
            "a composed flag clear requires a single-threaded descriptor table",
        ));
    }
    let get = Call::Fcntl { fd, cmd: darwin::F_GETFD, arg: 0 };
    let read = sem.step(host, pid, &get, Oracle::Nominal)?;
    match read.result {
        Err(_) => Ok(read),
        Ok(Ret::Int(flags)) if flags & darwin::FD_CLOEXEC != 0 => sem.step(
            &read.host,
            pid,
            &Call::Fcntl { fd, cmd: darwin::F_SETFD, arg: flags & !darwin::FD_CLOEXEC },
            Oracle::Nominal,
        ),
        Ok(Ret::Int(_)) => Ok(result(&read.host, 0)),
        _ => Err(unsupported(&get, "F_GETFD did not return descriptor flags")),
    }
}

pub(crate) fn is_composite<V>(call: &Call<V>) -> bool {
    matches!(
        call,
        Call::StdPlaceFd { .. }
            | Call::StdClearCloexec { .. }
            | Call::StdPassesExec { .. }
            | Call::StdMarkCloexec
            | Call::StdStatusFd { .. }
            | Call::StdCloseMovedStatus { .. }
    )
}

pub(crate) fn step<S: Semantics + ?Sized>(
    sem: &S,
    host: &Host,
    pid: Pid,
    call: &Call,
    oracle: Oracle,
) -> Result<Step, Refusal> {
    if is_composite(call) {
        let proc = host.proc(pid).ok_or(Refusal::NoSuchProcess(pid))?;
        if !proc.is_live() {
            return Err(Refusal::NotLive(pid));
        }
        if oracle != Oracle::Nominal {
            return Err(Refusal::InadmissibleOracle { symbol: call.symbol(), oracle });
        }
    }
    match call {
        Call::StdClearCloexec { fd } => clear(sem, host, pid, *fd),
        Call::StdPlaceFd { from, to } if from == to => clear(sem, host, pid, *from),
        Call::StdPlaceFd { from, to } => {
            sem.step(host, pid, &Call::Dup2 { from: *from, to: *to }, Oracle::Nominal)
        }
        Call::StdPassesExec { fd } => {
            let get = Call::Fcntl { fd: *fd, cmd: darwin::F_GETFD, arg: 0 };
            let read = sem.step(host, pid, &get, Oracle::Nominal)?;
            let passes = match read.result {
                Ok(Ret::Int(flags)) => flags & darwin::FD_CLOEXEC == 0,
                Err(_) => false,
                _ => return Err(unsupported(&get, "F_GETFD did not return descriptor flags")),
            };
            Ok(result(&read.host, i32::from(passes)))
        }
        Call::StdMarkCloexec => {
            let proc = host.proc(pid).ok_or(Refusal::NoSuchProcess(pid))?;
            if !proc.is_live() {
                return Err(Refusal::NotLive(pid));
            }
            if proc.threads != 1 || !matches!(proc.phase, Phase::ForkedPreExec { .. }) {
                return Err(unsupported(
                    call,
                    "the descriptor strip requires a single-threaded forked child",
                ));
            }
            // The forked child's descriptor flags are private to that child.
            // No other actor can change this table during the strip. Listing
            // every live entry also covers entries above a lowered soft limit.
            let fds: Vec<_> = proc.table.range(3..).map(|(fd, _)| *fd).collect();
            let mut h = host.clone();
            for fd in fds {
                let get = Call::Fcntl { fd, cmd: darwin::F_GETFD, arg: 0 };
                let read = sem.step(&h, pid, &get, Oracle::Nominal)?;
                h = read.host;
                if let Ok(Ret::Int(flags)) = read.result
                    && flags & darwin::FD_CLOEXEC == 0
                {
                    // mark_cloexec ignores a primitive errno, as std does;
                    // a semantics refusal remains a refusal, never success.
                    let marked = sem.step(
                        &h,
                        pid,
                        &Call::Fcntl { fd, cmd: darwin::F_SETFD, arg: flags | darwin::FD_CLOEXEC },
                        Oracle::Nominal,
                    )?;
                    h = marked.host;
                }
            }
            Ok(result(&h, 0))
        }
        Call::StdStatusFd { fd } if *fd >= 10 => Ok(result(host, *fd)),
        Call::StdStatusFd { fd } => {
            let dup = Call::Fcntl { fd: *fd, cmd: darwin::F_DUPFD_CLOEXEC, arg: 10 };
            let copied = sem.step(host, pid, &dup, Oracle::Nominal)?;
            match copied.result {
                Err(_) => Ok(result(&copied.host, *fd)),
                Ok(Ret::Int(new)) => {
                    let new = i32::try_from(new)
                        .map_err(|_| unsupported(call, "the status descriptor does not fit i32"))?;
                    Ok(result(&copied.host, new))
                }
                _ => Err(unsupported(&dup, "F_DUPFD_CLOEXEC did not return a descriptor")),
            }
        }
        Call::StdCloseMovedStatus { old, new } if old == new => Ok(result(host, 0)),
        Call::StdCloseMovedStatus { old, .. } => {
            sem.step(host, pid, &Call::Close { fd: *old }, Oracle::Nominal)
        }
        Call::Spawn { actions: input, flags } => {
            let call = Call::Spawn { actions: actions(input)?, flags: *flags };
            sem.step_raw(host, pid, &call, oracle)
        }
        Call::SpawnEnd { child, actions: input, flags } => {
            let call = Call::SpawnEnd { child: *child, actions: actions(input)?, flags: *flags };
            sem.step_raw(host, pid, &call, oracle)
        }
        _ => sem.step_raw(host, pid, call, oracle),
    }
}
