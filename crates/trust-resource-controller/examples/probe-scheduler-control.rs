//! Focused transport fixture only; no compiler/resource/proof authentication.
use std::io::Write;
use std::process::{Command, ExitCode};

use trust_resource_controller::client::probe_scheduler::ProbeScheduler;

fn main() -> ExitCode {
    // SAFETY: genuine first native entry, before any descriptor-opening work.
    let scheduler = match unsafe { ProbeScheduler::capture_at_entry() } {
        Ok(value) => value,
        Err(error) => {
            eprintln!("probe custody refused: {error}");
            return ExitCode::from(75);
        }
    };
    let mut args: Vec<_> = std::env::args_os().skip(1).collect();
    let owned = args.first().is_some_and(|a| a == "--owned" || a == "--hop");
    let hop = args.first().is_some_and(|a| a == "--hop");
    if owned {
        args.remove(0);
        if args.is_empty() || !std::path::Path::new(&args[0]).is_absolute() {
            return ExitCode::from(2);
        }
        let observed = entry_descriptions();
        let before: Vec<_> =
            observed.iter().map(|(_, fd)| unsafe { libc::fcntl(*fd, libc::F_GETFD) }).collect();
        eprintln!(
            "ENTRY_TRANSPORT={:?}",
            observed.iter().map(|(identity, _)| identity).collect::<Vec<_>>()
        );
        let mut command = if hop {
            let mut command = Command::new(std::env::current_exe().unwrap());
            command.arg("--owned").args(&args);
            command
        } else {
            let mut command = Command::new(&args[0]);
            command.args(&args[1..]);
            command
        };
        // Real native-entry capture occurs again at the second executable hop.
        // This observes transport only, never authenticates resource admission.
        let output = scheduler.output(&mut command);
        let after: Vec<_> =
            observed.iter().map(|(_, fd)| unsafe { libc::fcntl(*fd, libc::F_GETFD) }).collect();
        assert_eq!(before, after, "owned query changed original parent FD flags");
        return match output {
            Ok(output) => {
                std::io::stdout().write_all(&output.stdout).unwrap();
                std::io::stderr().write_all(&output.stderr).unwrap();
                ExitCode::from(output.status.code().unwrap_or(1) as u8)
            }
            Err(error) => {
                eprintln!("owned probe refused: {error}");
                ExitCode::from(75)
            }
        };
    }
    let plain = args.first().is_some_and(|a| a == "--plain");
    if plain {
        args.remove(0);
    }
    if args.is_empty() || !std::path::Path::new(&args[0]).is_absolute() {
        return ExitCode::from(2);
    }
    let mut command = Command::new(&args[0]);
    command.args(&args[1..]);
    if std::env::var_os("PROBE_SET_SDK_CLOEXEC").is_some() {
        let fd: i32 = std::env::var("ATERM_SDK_LEASE_V3").unwrap().parse().unwrap();
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(flags >= 0);
        assert_eq!(unsafe { libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) }, 0);
    }
    let output = scheduler.with_command(&mut command, |command| {
        let flags = command
            .get_envs()
            .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten())
            .unwrap()
            .to_str()
            .unwrap();
        let pair =
            flags.split_whitespace().find_map(|v| v.strip_prefix("--jobserver-auth=")).unwrap();
        let mut fds: Vec<i32> = pair.split(',').map(|v| v.parse().unwrap()).collect();
        if let Ok(fd) = std::env::var("ATERM_SDK_LEASE_V3") {
            fds.push(fd.parse().unwrap());
        }
        let before: Vec<_> =
            fds.iter().map(|fd| unsafe { libc::fcntl(*fd, libc::F_GETFD) }).collect();
        assert!(before.iter().all(|flags| *flags >= 0));
        let captured = if plain {
            // Reproduce the old direct-Command defect with the actual owned
            // scheduler's advertisements, but without its per-child handoff.
            let mut stripped = Command::new(command.get_program());
            stripped.args(command.get_args());
            for (key, value) in command.get_envs() {
                if let Some(value) = value {
                    stripped.env(key, value);
                } else {
                    stripped.env_remove(key);
                }
            }
            stripped.output()
        } else {
            command.output()
        };
        let after: Vec<_> =
            fds.iter().map(|fd| unsafe { libc::fcntl(*fd, libc::F_GETFD) }).collect();
        assert_eq!(before, after, "native handoff changed parent descriptor flags");
        eprintln!("PARENT_FD_FLAGS_UNCHANGED=true");
        captured
    });
    match output {
        Ok(Ok(output)) => {
            std::io::stdout().write_all(&output.stdout).unwrap();
            std::io::stderr().write_all(&output.stderr).unwrap();
            ExitCode::from(output.status.code().unwrap_or(1) as u8)
        }
        error => {
            eprintln!("probe capture failed: {error:?}");
            ExitCode::from(1)
        }
    }
}

fn entry_descriptions() -> Vec<(String, i32)> {
    let mut descriptions = Vec::new();
    if let Ok(flags) = std::env::var("CARGO_MAKEFLAGS")
        && let Some(pair) =
            flags.split_whitespace().find_map(|word| word.strip_prefix("--jobserver-auth="))
    {
        descriptions.extend(pair.split(',').map(|fd| fd.parse::<i32>().unwrap()));
    }
    if let Ok(fd) = std::env::var("ATERM_SDK_LEASE_V3") {
        descriptions.push(fd.parse().unwrap());
    }
    descriptions
        .into_iter()
        .map(|fd| {
            let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
            assert_eq!(unsafe { libc::fstat(fd, stat.as_mut_ptr()) }, 0);
            let stat = unsafe { stat.assume_init() };
            (format!("{}:{}", stat.st_dev, stat.st_ino), fd)
        })
        .collect()
}
