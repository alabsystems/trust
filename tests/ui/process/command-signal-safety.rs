// Trust: Regression test for rust-lang#64718 (Command signal safety between fork and exec).
//
// Verifies that signal handlers installed in the parent process are reset to
// SIG_DFL in child processes spawned via Command. This prevents non-async-signal-safe
// handlers (which may call malloc, take locks, etc.) from running in the child's
// fork-exec window, which would cause deadlocks.
//
// The test installs a SIGUSR1 handler in the parent, spawns a child, and the child
// verifies that its SIGUSR1 disposition is SIG_DFL (not the parent's handler).

//@ run-pass
//@ needs-subprocess
//@ only-unix
//@ ignore-emscripten (no signal support)
//@ ignore-fuchsia
//@ ignore-wasi
#![allow(function_casts_as_integer)]

#![feature(rustc_private)]

extern crate libc;

use std::env;
use std::process::Command;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() >= 2 && args[1] == "child" {
        // Child process: check that SIGUSR1 has been reset to SIG_DFL.
        // If the parent's handler leaked through, this would be SIG_IGN or
        // a function pointer, not SIG_DFL.
        unsafe {
            let mut current_action: libc::sigaction = std::mem::zeroed();
            let ret = libc::sigaction(
                libc::SIGUSR1,
                std::ptr::null(),
                &mut current_action,
            );
            assert_eq!(ret, 0, "sigaction query failed");
            // The handler should be SIG_DFL (0) since tRust resets signal
            // handlers between fork and exec.
            assert_eq!(
                current_action.sa_sigaction,
                libc::SIG_DFL,
                "SIGUSR1 handler was not reset to SIG_DFL in child process \
                 (got {}). This means the parent's signal handler leaked into \
                 the fork-exec window, which is the bug described in \
                 rust-lang#64718.",
                current_action.sa_sigaction,
            );
        }
    } else {
        // Parent process: install a custom SIGUSR1 handler, then spawn a child
        // that checks whether the handler was reset.
        unsafe {
            // Install a no-op handler for SIGUSR1. In a real scenario this handler
            // could call malloc() or take locks, making it non-async-signal-safe.
            extern "C" fn noop_handler(_: libc::c_int) {}

            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = noop_handler as usize;
            let ret = libc::sigaction(
                libc::SIGUSR1,
                &action,
                std::ptr::null_mut(),
            );
            assert_eq!(ret, 0, "failed to install SIGUSR1 handler");
        }

        // Spawn child and check its exit status
        let status = Command::new(&args[0])
            .arg("child")
            .status()
            .expect("failed to spawn child process");

        assert!(
            status.success(),
            "child process failed (signal handler was not reset to SIG_DFL): {:?}",
            status,
        );
    }
}
