// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! One synchronous command borrows its already-admitted caller's implicit job.
//! This owns GNU transport, never CPU/memory/SDK admission or proof authority.
#![cfg_attr(trust_std, feature(trust_process_inherit_fds))]

#[cfg(all(trust_std, any(target_os = "linux", target_os = "macos")))]
mod native {
    use std::io;
    use std::os::unix::process::{CommandExt, ExitStatusExt};
    use std::path::Path;
    use std::process::{Child, Command, ExitStatus, Stdio};
    use std::sync::atomic::{AtomicI32, Ordering};
    use std::time::Duration;

    use jobserver_utils::Jobserver;
    use trust_resource_controller::client::sdk;

    static CHILD: AtomicI32 = AtomicI32::new(0);
    static STOPPED: AtomicI32 = AtomicI32::new(0);
    const SIGNALS: [libc::c_int; 3] = [libc::SIGTERM, libc::SIGINT, libc::SIGHUP];

    extern "C" fn stopped(signal: libc::c_int) {
        let _ = STOPPED.compare_exchange(0, signal, Ordering::SeqCst, Ordering::SeqCst);
        let pid = CHILD.load(Ordering::SeqCst);
        if pid > 0 {
            // SAFETY: only an un-reaped owned child's new process group is published.
            // Reaping/clearing its PID is performed with these signals blocked.
            unsafe {
                libc::kill(-pid, signal);
            }
        }
    }

    struct Signals {
        previous: Vec<(libc::c_int, libc::sigaction)>,
    }
    impl Signals {
        fn install() -> io::Result<Self> {
            let mut result = Self { previous: Vec::new() };
            for signal in SIGNALS {
                // SAFETY: zero is valid native sigaction storage, filled before use.
                let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
                action.sa_sigaction = stopped as extern "C" fn(libc::c_int) as libc::sighandler_t;
                // SAFETY: action owns writable mask storage.
                unsafe {
                    libc::sigemptyset(&mut action.sa_mask);
                }
                // SAFETY: previous receives the actual old disposition.
                let mut previous = unsafe { std::mem::zeroed() };
                if unsafe { libc::sigaction(signal, &action, &mut previous) } != 0 {
                    return Err(io::Error::last_os_error());
                }
                result.previous.push((signal, previous));
            }
            Ok(result)
        }
    }
    impl Drop for Signals {
        fn drop(&mut self) {
            for (signal, previous) in self.previous.iter().rev() {
                // SAFETY: restore the exact dispositions saved by install.
                unsafe {
                    libc::sigaction(*signal, previous, std::ptr::null_mut());
                }
            }
        }
    }

    struct Blocked(libc::sigset_t);
    impl Blocked {
        fn new() -> io::Result<Self> {
            // SAFETY: local native mask storage is initialized before use.
            let mut mask: libc::sigset_t = unsafe { std::mem::zeroed() };
            let mut previous: libc::sigset_t = unsafe { std::mem::zeroed() };
            unsafe {
                libc::sigemptyset(&mut mask);
                for signal in SIGNALS {
                    libc::sigaddset(&mut mask, signal);
                }
            }
            // Handoff service threads inherit a blocked mask. The handler cannot
            // race a successful reap and signal a reused numeric process group.
            let code = unsafe { libc::pthread_sigmask(libc::SIG_BLOCK, &mask, &mut previous) };
            if code != 0 {
                return Err(io::Error::from_raw_os_error(code));
            }
            Ok(Self(previous))
        }
    }
    impl Drop for Blocked {
        fn drop(&mut self) {
            // SAFETY: restore this thread's previously captured mask.
            unsafe {
                libc::pthread_sigmask(libc::SIG_SETMASK, &self.0, std::ptr::null_mut());
            }
        }
    }

    struct Running {
        child: Child,
        terminal: bool,
    }
    impl Running {
        fn wait(&mut self) -> ExitStatus {
            loop {
                // Retain the child and GNU/SDK owners on transient wait or mask
                // errors. There is no forced KILL or success from an uncertain wait.
                if let Ok(blocked) = Blocked::new() {
                    if let Ok(Some(status)) = self.child.try_wait() {
                        CHILD.store(0, Ordering::SeqCst);
                        self.terminal = true;
                        drop(blocked);
                        return status;
                    }
                    drop(blocked);
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }
    impl Drop for Running {
        fn drop(&mut self) {
            if !self.terminal {
                // SAFETY: this still-unreaped child owns the published group.
                unsafe {
                    libc::kill(-(self.child.id() as i32), libc::SIGTERM);
                }
                self.wait();
            }
            // Observe only after reap: a reused numeric group can prolong this
            // conservative wait, but is NEVER signalled. No detached-session
            // or kernel-wide retirement claim is made.
            loop {
                let exists = unsafe { libc::kill(-(self.child.id() as i32), 0) };
                if exists < 0 && io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
                    break;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }

    fn execute(
        mut server: Jobserver,
        program: &std::ffi::OsStr,
        args: &[std::ffi::OsString],
    ) -> io::Result<i32> {
        // Any handoff service thread inherits the blocked termination mask;
        // only the main thread may forward while it owns/reaps CHILD.
        let blocked = Blocked::new()?;
        server.enable_descendant_handoff()?;
        let signals = Signals::install()?;
        drop(blocked);
        let mut command = Command::new(program);
        command
            .args(args)
            .stdin(Stdio::inherit())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        // An explicit pass-through preserves original SDK/CPU custody. The
        // launcher never reopens a lease path or derives authority from a number.
        command.inherit_all_fds().process_group(0);
        server.configure_make(&mut command);
        let child = command.spawn()?;
        CHILD.store(child.id() as i32, Ordering::SeqCst);
        let mut running = Running { child, terminal: false };
        let signal = STOPPED.load(Ordering::SeqCst);
        if signal != 0 {
            stopped(signal);
        }
        let status = running.wait();
        drop(running); // actual foreground terminal BEFORE server/signal owners drop
        let blocked = Blocked::new()?;
        let signal = STOPPED.load(Ordering::SeqCst);
        drop(signals);
        drop(blocked);
        Ok(if signal != 0 {
            128 + signal
        } else {
            status.code().unwrap_or_else(|| 128 + status.signal().unwrap_or(1))
        })
    }

    pub fn run() -> Result<i32, String> {
        // FIRST native-entry operation: no probe, parser, file open or logger
        // may precede the original SDK snapshot / checked GNU import / capture.
        let pending = sdk::snapshot_sdk_lease().map_err(|e| format!("SDK snapshot: {e}"))?;
        // SAFETY: only the no-allocation SDK snapshot has run at native entry.
        let inherited = unsafe { Jobserver::from_env_with_handoff_checked() }
            .map_err(|e| format!("inherited GNU transport: {e}"))?;
        // SAFETY: only the fixed checked GNU importer ran since the snapshot.
        unsafe { sdk::capture_sdk_lease(pending) }.map_err(|e| format!("SDK capture: {e}"))?;
        if inherited.is_none()
            && std::env::var_os(jobserver_utils::DESCENDANT_HANDOFF_ENV).is_some()
        {
            return Err("advertised GNU handoff has no captured transport".into());
        }
        let args: Vec<_> = std::env::args_os().skip(1).collect();
        if args == ["--version"] {
            println!("trust-serial-command {}", env!("CARGO_PKG_VERSION"));
            return Ok(0);
        }
        if args == ["--help"] {
            println!(
                "trust-serial-command -- /absolute/program [arguments...]\nBorrows one already-admitted implicit execution; adds zero GNU credits."
            );
            return Ok(0);
        }
        if args.len() < 2 || args[0] != "--" || !Path::new(&args[1]).is_absolute() {
            return Err("use -- /absolute/program [arguments...]".into());
        }
        // Refusal precondition only. The caller must actually obtain canonical
        // admission; this environment marker authenticates no resource grant.
        if std::env::var("BUILD_SLOT_HELD").as_deref() != Ok("1") {
            return Err(
                "command requires an already-admitted caller; this launcher grants no CPU/memory"
                    .into(),
            );
        }
        let server = match inherited {
            Some(server) => server,
            None => Jobserver::new(0).map_err(|e| format!("zero-extra GNU transport: {e}"))?,
        };
        execute(server, &args[1], &args[2..]).map_err(|e| format!("command launch: {e}"))
    }
}

fn main() -> std::process::ExitCode {
    #[cfg(all(trust_std, any(target_os = "linux", target_os = "macos")))]
    {
        match native::run() {
            Ok(code) => std::process::ExitCode::from(code as u8),
            Err(why) => {
                eprintln!("trust-serial-command: refused: {why}");
                std::process::ExitCode::from(75)
            }
        }
    }
    #[cfg(not(all(trust_std, any(target_os = "linux", target_os = "macos"))))]
    {
        eprintln!(
            "trust-serial-command requires Trust native descriptor inheritance on Linux/macOS"
        );
        std::process::ExitCode::from(75)
    }
}
