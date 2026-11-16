//! Trust (VERIFIER-PULSE-OWN-EXECUTION): lend one admitted protocol-1 execution.
//!
//! The owned GNU pool has zero tokens. It grants no additional parallelism,
//! CPU, SDK or proof authority, and never replaces an advertised scheduler.

#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::ffi::OsString;
use std::io;
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::process::Command;
use std::process::ExitCode;

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn own_execution_owed() -> bool {
    std::env::var_os("BUILD_SLOT_CPU_PROTOCOL").is_some_and(|value| value == "1")
        && std::env::var_os("BUILD_SLOT_HELD").is_some_and(|value| value == "1")
        && [
            jobserver_utils::DESCENDANT_HANDOFF_ENV,
            jobserver_utils::CPU_HANDOFF_ENV,
            jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            "TRUST_CPU_IMPLICIT_FD",
            "BUILD_SLOT_FENCE_FDS",
            "ATERM_SDK_LEASE_V3",
            "ATERM_WORKLOAD_CPU_FDS_V1",
            "ATERM_WORKLOAD_HOST_STORE_FD_V1",
            "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
        ]
        .into_iter()
        .all(|name| std::env::var_os(name).is_none())
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn run() -> io::Result<ExitCode> {
    // These observations open no descriptors. Anything advertised belongs to
    // its original importer; this entry may neither replace nor repair it.
    if !own_execution_owed() {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "a loan requires bare build-slot protocol 1 with no advertised custody",
        ));
    }
    let mut arguments = std::env::args_os().skip(1);
    let program: OsString = arguments.next().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "usage: lend_execution PROGRAM [ARG ...]",
        )
    })?;
    let mut owner = jobserver_utils::Jobserver::new(0)?;
    owner.enable_descendant_handoff()?;
    let mut child = Command::new(program);
    child.args(arguments);
    owner.configure_make(&mut child);
    // Retain the same owner and descendant handoff until the actual child is
    // reaped. The waiting coordinator lends only its own implicit execution.
    let status = child.status()?;
    drop(child);
    drop(owner);
    forward_status(status)
}

// Trust: keep an ordinary exit 128+N distinct from a child actually killed by
// signal N. The owner and handoff above are retired only after the child wait.
#[cfg(unix)]
fn forward_status(status: std::process::ExitStatus) -> io::Result<ExitCode> {
    use std::os::unix::process::ExitStatusExt;
    if let Some(code) = status.code() {
        return Ok(ExitCode::from(code as u8));
    }
    let signal = status
        .signal()
        .ok_or_else(|| io::Error::other("child wait returned neither an exit code nor a signal"))?;
    // SAFETY: the signal came from this child's actual wait status. Restore
    // its default disposition and unblock it before sending it to ourselves;
    // an inherited mask or ignored disposition must not turn it into an exit.
    unsafe {
        if signal != libc::SIGKILL
            && signal != libc::SIGSTOP
            && libc::signal(signal, libc::SIG_DFL) == libc::SIG_ERR
        {
            return Err(io::Error::last_os_error());
        }
        let mut signals: libc::sigset_t = std::mem::zeroed();
        if libc::sigemptyset(&mut signals) != 0
            || libc::sigaddset(&mut signals, signal) != 0
            || libc::sigprocmask(libc::SIG_UNBLOCK, &signals, std::ptr::null_mut()) != 0
            || libc::kill(libc::getpid(), signal) != 0
        {
            return Err(io::Error::last_os_error());
        }
    }
    Err(io::Error::other(
        "child termination signal did not terminate execution lender",
    ))
}

#[cfg(not(unix))]
fn forward_status(status: std::process::ExitStatus) -> io::Result<ExitCode> {
    Ok(ExitCode::from(status.code().unwrap_or(1) as u8))
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn run() -> io::Result<ExitCode> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "execution lending is unavailable on this host",
    ))
}

fn main() -> ExitCode {
    match run() {
        Ok(status) => status,
        Err(error) => {
            eprintln!("lend_execution: {error}");
            ExitCode::from(75)
        }
    }
}
