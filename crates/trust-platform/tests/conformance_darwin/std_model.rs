//! Measure the default SP-1 behavior and its explicit native Trust opt-out
//! independently of the model rows.

use std::os::unix::process::CommandExt;
use std::path::Path;

use super::{Env, REPORTER_FLAG, RealFd, in_fresh_process};

fn measure(dir: &Path) -> Result<String, String> {
    // SAFETY: this fresh single-threaded process owns stdin and the new fd.
    let fd = unsafe { libc::fcntl(0, libc::F_DUPFD, 64) };
    if fd != 64 {
        return Err(format!("expected fresh unflagged fd 64, got {fd}"));
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    for pre_exec in [false, true] {
        for upstream in [false, true] {
            let path = dir.join(format!("inherit-{pre_exec}-{upstream}.table"));
            let mut command = std::process::Command::new(&exe);
            command.arg(REPORTER_FLAG).arg(&path);
            if upstream {
                command.inherit_all_fds();
            }
            if pre_exec {
                // SAFETY: the no-op hook forces std's fork implementation.
                unsafe { command.pre_exec(|| Ok(())) };
            }
            let status = command.status().map_err(|e| e.to_string())?;
            if !status.success() {
                return Err(format!("reporter failed: {status}"));
            }
            let table = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            let fds: Vec<_> = table
                .lines()
                .filter_map(|line| line.strip_prefix("H "))
                .map(|line| {
                    RealFd::decode(line).ok_or_else(|| "invalid reporter entry".to_string())
                })
                .collect::<Result<_, _>>()?;
            if ![0, 1, 2].iter().all(|fd| fds.iter().any(|entry| entry.fd == *fd)) {
                return Err("reporter lost inherited stdio".to_string());
            }
            let inherited = fds.iter().any(|entry| entry.fd == 64);
            if inherited != upstream {
                return Err(format!(
                    "pre_exec={pre_exec}, upstream={upstream}: fd 64 inherited={inherited}"
                ));
            }
        }
    }
    // SAFETY: the fresh process owns this descriptor and has reaped its children.
    unsafe { libc::close(fd) };
    Ok("P-STD-MODEL=Trust: default strip and explicit opt-out verified on posix and fork paths"
        .to_string())
}

pub(super) fn check(env: &Env) -> Result<String, String> {
    let line = in_fresh_process(env, "std-model-identity", |dir| match measure(dir) {
        Ok(message) => format!("ok {message}"),
        Err(error) => format!("error {error}"),
    })?;
    line.strip_prefix("ok ").map(str::to_owned).ok_or(line.clone())
}
