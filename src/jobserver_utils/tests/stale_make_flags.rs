//! Trust (JOBSERVER-STALE-MAKEFLAGS-1): a native client below an unaware harness
//! recovers the scheduler it was started under.
//!
//! A cut's widened aterm check ran under a scheduler that advertises a numeric
//! pipe. Targo handed its children the pool at fresh descriptor numbers in
//! `CARGO_MAKEFLAGS` and left the outer scheduler's numbers in `MAKEFLAGS`. The
//! test harness below it closes descriptors and drops `CARGO_MAKEFLAGS`, so a
//! Targo started by a test read `MAKEFLAGS`, found descriptor 5 closed, could
//! not bind the handoff to it and refused: "cannot inherit Targo jobserver:
//! invalid advertised jobserver: cannot open file descriptor 5". Eight test
//! binaries of that check failed this way and passed without the scheduler.
//!
//! Its own test binary: the client half changes this process's environment.

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::process::Command;

const CLIENT: &str = "TRUST_STALE_MAKE_FLAGS_CLIENT";

/// The client half, run in a child of [`a_client_below_an_unaware_harness_recovers_the_pool`].
/// In any other process it does nothing.
#[test]
fn client() {
    if std::env::var_os(CLIENT).is_none() {
        return;
    }
    // What an unaware harness leaves: the advertised descriptors closed and
    // Cargo's own variable gone. MAKEFLAGS is as the scheduler configured it.
    let flags = std::env::var("CARGO_MAKEFLAGS").expect("the scheduler configured this child");
    let pair = flags.rsplit_once("--jobserver-auth=").unwrap().1;
    for fd in pair.split(',') {
        // SAFETY: closes only the two descriptors this child was handed.
        assert_eq!(unsafe { libc::close(fd.parse().unwrap()) }, 0);
    }
    // SAFETY: this process runs this one test and no other thread reads the
    // environment before the import below.
    unsafe { std::env::remove_var("CARGO_MAKEFLAGS") };
    // SAFETY: both advertised descriptors are closed and nothing has been opened since.
    let imported = unsafe { jobserver_utils::Jobserver::from_env_with_handoff_checked() };
    match imported {
        Ok(Some(_)) => println!("RECOVERED"),
        Ok(None) => println!("NO-SCHEDULER"),
        Err(error) => println!("REFUSED {error}"),
    }
}

#[test]
fn a_client_below_an_unaware_harness_recovers_the_pool() {
    let mut server = jobserver_utils::Jobserver::new(2).unwrap();
    server.enable_descendant_handoff().unwrap();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", "client", "--nocapture", "--test-threads", "1"])
        .env(CLIENT, "1")
        // The outer scheduler's advertisement, at numbers this child never has.
        .env("MAKEFLAGS", "-j --jobserver-fds=250,251 --jobserver-auth=250,251")
        .env("MFLAGS", "-j --jobserver-fds=250,251 --jobserver-auth=250,251");
    server.configure(&mut command);
    let output = command.output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("RECOVERED"),
        "the client did not recover its scheduler:\n{stdout}{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
