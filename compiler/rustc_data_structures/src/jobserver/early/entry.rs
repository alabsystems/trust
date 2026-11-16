//! Fresh-process fixture: the actual compiler capture is the FIRST operation.
#[path = "../early.rs"]
mod early;

fn main() {
    // SAFETY: FIRST entry operation. The fixture launcher explicitly inherits
    // disjoint GNU and SDK descriptions; no logger/probe/callback ran here.
    // Reading the environment opens no descriptor.
    let own_execution = std::env::var_os("CUSTODY_OWN_EXECUTION").is_some();
    let captured = if own_execution {
        // SAFETY: as above; the fixture asks for the embedded test-harness loan.
        unsafe { early::capture_lending_own_execution() }
    } else {
        unsafe { early::capture() }
    };
    if captured.is_err() {
        std::process::exit(75);
    }
    if own_execution {
        // The loan is an owned pool holding ZERO tokens: the compiler runs only
        // on the implicit execution of the thread that waits on it.
        assert!(early::lent_own_execution());
        assert!(!early::admitted_bounded_query(), "a loan is not a bounded query");
        assert!(early::grant_bounded_query_session().is_none());
        let client = early::local(99, false).unwrap();
        assert_eq!(client.available().unwrap(), 0, "a loan holds no token");
        assert!(early::local(3, true).is_err(), "a loan carries no native worker custody");
        // One compile at a time, structurally: an overlapping one refuses.
        let first = early::enter_lent_compile().unwrap().expect("a loan guards each compile");
        assert!(early::enter_lent_compile().is_err(), "an overlapping compile refuses");
        drop(first);
        assert!(early::enter_lent_compile().unwrap().is_some());
        println!("own execution lent");
    } else if std::env::var_os("CUSTODY_FORWARD_METADATA").is_some() {
        forward_metadata();
    } else if std::env::var_os("CUSTODY_MISSING_HOST_CONTROL").is_some() {
        missing_host_control();
    } else if std::env::var_os("CUSTODY_HOST_STORE").is_some() {
        host_store();
    } else if std::env::var_os("CUSTODY_WORKLOAD").is_some() {
        workload();
    } else if std::env::var_os("CUSTODY_METADATA").is_some() {
        metadata();
    } else if std::env::var_os("CUSTODY_BOUNDED_QUERY").is_some() {
        // An admitted bounded query is never a producing compiler.
        assert!(early::local(99, false).is_err(), "a bounded query minted a private scheduler");
        assert!(early::admitted_bounded_query(), "the admission was not recorded");
        // One session, once: a second grant is refused, the grant is taken
        // once, a grant dropped untaken is spent, and a spent grant is never
        // made again.
        let grant = early::grant_bounded_query_session().expect("an admitted query is granted");
        assert!(early::grant_bounded_query_session().is_none(), "a second grant");
        if std::env::var_os("CUSTODY_DROP_GRANT").is_some() {
            drop(grant);
            assert!(!early::take_bounded_query_session(), "a dropped grant was taken");
        } else {
            assert!(early::take_bounded_query_session());
            assert!(!early::take_bounded_query_session(), "a grant taken twice");
            drop(grant);
        }
        assert!(early::grant_bounded_query_session().is_none(), "a grant after the session");
        println!("bounded query admitted");
    } else if std::env::var_os("CUSTODY_JOINT").is_some() {
        joint();
    } else {
        assert!(early::take_workload_cpu().unwrap().is_none());
        assert_eq!(early::local(3, false).unwrap().available().unwrap(), 2);
        assert!(!early::lent_own_execution() && early::enter_lent_compile().unwrap().is_none());
        assert!(!early::admitted_bounded_query(), "a scheduled process is not a bounded query");
        assert!(early::grant_bounded_query_session().is_none());
    }
}

fn missing_host_control() {
    use std::time::{Duration, Instant};
    let cpu_fd: i32 = std::env::var("CUSTODY_WORKLOAD_FD").unwrap().parse().unwrap();
    let store_fd: i32 = std::env::var("CUSTODY_HOST_STORE_FD").unwrap().parse().unwrap();
    for name in ["ATERM_WORKLOAD_CPU_FDS_V1", "ATERM_WORKLOAD_HOST_STORE_FD_V1"] {
        assert!(std::env::var_os(name).is_none());
    }
    for fd in [cpu_fd, store_fd] {
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(flags >= 0 && flags & libc::FD_CLOEXEC != 0);
    }
    // Match activation order: consuming the CPU originals cannot erase the
    // first-entry selection or allow a legacy Store to replace Host control.
    let cpu = early::take_workload_cpu().unwrap().unwrap();
    assert!(early::take_workload_cpu().is_err());
    // SAFETY: this fresh fixture has one thread and no callbacks. These late
    // locators must never be reread as replacements for the captured originals.
    unsafe {
        std::env::set_var("ATERM_WORKLOAD_HOST_STORE_FD_V1", "malformed");
        std::env::set_var("ATERM_WORKLOAD_HOST_CONTROL_FDS_V1", "malformed");
    }
    let deadline = Instant::now() + Duration::from_secs(5);
    let error = early::take_host_controller(deadline).err().expect("control originals are absent");
    assert_eq!(error, "admitted compiler has no inherited original Host control pin");
    assert_eq!(unsafe { libc::fcntl(store_fd, libc::F_GETFD) }, -1);
    assert!(unsafe { libc::fcntl(cpu_fd, libc::F_GETFD) } >= 0);
    assert_eq!(
        early::take_host_controller(deadline).err().expect("original Store was consumed"),
        "compiler original host selection was already consumed"
    );
    drop(cpu);
    assert_eq!(unsafe { libc::fcntl(cpu_fd, libc::F_GETFD) }, -1);
}

fn forward_metadata() {
    assert!(trust_resource_controller::client::sdk::original_lease_present().unwrap());
    // SAFETY: this fresh fixture has one thread and no callbacks. A later
    // locator must not replace the original capture during transparent export.
    unsafe { std::env::set_var("ATERM_SDK_LEASE_V3", "malformed-late-locator") };
    let mut command = std::process::Command::new(std::env::current_exe().unwrap());
    command.env_clear().arg("--resource-capabilities").env("CUSTODY_METADATA", "1");
    trust_resource_controller::client::sdk::inherit_original_lease(&mut command).unwrap();
    let status = command.status().unwrap();
    std::process::exit(status.code().unwrap_or(75));
}

fn host_store() {
    let fd: i32 = std::env::var("CUSTODY_HOST_STORE_FD").unwrap().parse().unwrap();
    assert!(std::env::var_os("ATERM_WORKLOAD_HOST_STORE_FD_V1").is_none());
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    assert!(flags >= 0 && flags & libc::FD_CLOEXEC != 0);
    // SAFETY: fixed single-threaded fixture; a late locator cannot replace the
    // original selection or become a fallback to another account host.
    unsafe { std::env::set_var("ATERM_WORKLOAD_HOST_STORE_FD_V1", "malformed") };
    let original = early::take_host_store().unwrap();
    assert!(original.is_present());
    assert!(early::take_host_store().is_err());
    assert_eq!(early::local(99, false).unwrap().available().unwrap(), 2);
    drop(original);
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFD) }, -1);
}

fn workload() {
    use std::io::{BufRead, Write};
    let fd: i32 = std::env::var("CUSTODY_WORKLOAD_FD").unwrap().parse().unwrap();
    assert!(std::env::var_os("ATERM_WORKLOAD_CPU_FDS_V1").is_none());
    // SAFETY: observation of the actual first-entry-owned fixture descriptor.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    assert!(flags >= 0 && flags & libc::FD_CLOEXEC != 0);
    // SAFETY: this fixed fixture has one thread. A late locator is deliberately
    // invalid; selecting the original route must never reread or adopt it.
    unsafe { std::env::set_var("ATERM_WORKLOAD_CPU_FDS_V1", "malformed") };
    let original = early::take_workload_cpu().unwrap().unwrap();
    assert!(original.is_present());
    assert!(early::take_workload_cpu().is_err(), "an original may be consumed only once");
    assert_eq!(early::local(99, false).unwrap().available().unwrap(), 2);
    println!("ready");
    std::io::stdout().flush().unwrap();
    let mut line = String::new();
    std::io::stdin().lock().read_line(&mut line).unwrap();
    // Early ownership is not a CPU grant. No authenticated host/member
    // exchange or workload Lease is constructed by this fixture.
    drop(original);
}

fn joint() {
    use std::io::{BufRead, Write};
    use std::os::fd::{AsRawFd, BorrowedFd};
    let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
    let pair = flags.split_whitespace().find_map(|s| s.strip_prefix("--jobserver-auth=")).unwrap();
    let (read, write) = pair.split_once(',').unwrap();
    let targets: [i32; 2] = [read.parse().unwrap(), write.parse().unwrap()];
    let sdk: i32 = std::env::var("ATERM_SDK_LEASE_V3").unwrap().parse().unwrap();
    for fd in targets.into_iter().chain([sdk]) {
        // SAFETY: fixture-only ORIGINAL inherited targets, all disjoint from
        // captured private descriptions; each number is closed exactly once.
        assert_eq!(unsafe { libc::close(fd) }, 0);
    }
    let replacement = jobserver_utils::Jobserver::new(7).unwrap();
    let mut metadata = std::process::Command::new("not-executed");
    replacement.client().configure(&mut metadata);
    let flags = metadata
        .get_envs()
        .find_map(|(k, v)| (k == "CARGO_MAKEFLAGS").then_some(v).flatten())
        .unwrap()
        .to_str()
        .unwrap();
    let pair = flags.split_whitespace().find_map(|s| s.strip_prefix("--jobserver-auth=")).unwrap();
    let (read, write) = pair.split_once(',').unwrap();
    let sources: [i32; 2] = [read.parse().unwrap(), write.parse().unwrap()];
    let copies: Vec<_> = sources
        .into_iter()
        .map(|fd| {
            // SAFETY: these live fixture-only client descriptors are borrowed,
            // never owned/closed through their observed source numbers.
            unsafe { BorrowedFd::borrow_raw(fd) }.try_clone_to_owned().unwrap()
        })
        .collect();
    // Stage every source above all targets before replacing any of them:
    // replacement client creation may itself reuse original target slots.
    let copies: Vec<_> = copies
        .iter()
        .map(|source| {
            // SAFETY: duplicate a held fixture source above all original targets.
            let raw = unsafe { libc::fcntl(source.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 64) };
            assert!(raw >= 64);
            // SAFETY: successful fcntl returns one fresh owned descriptor.
            unsafe { std::os::fd::OwnedFd::from_raw_fd(raw) }
        })
        .collect();
    use std::os::fd::FromRawFd;
    for (source, target) in copies.iter().zip(targets) {
        // SAFETY: only this private helper's deliberately replaced original
        // GNU target table is changed; captured clients use other descriptors.
        assert_eq!(unsafe { libc::dup2(source.as_raw_fd(), target) }, target);
    }
    assert_eq!(
        early::local(99, false).unwrap().available().unwrap(),
        2,
        "late raw import adopted replacement scheduling tokens"
    );
    println!("ready");
    std::io::stdout().flush().unwrap();
    let mut line = String::new();
    std::io::stdin().lock().read_line(&mut line).unwrap();
}

fn metadata() {
    use std::io::{BufRead, Write};
    let sdk: i32 = std::env::var("ATERM_SDK_LEASE_V3").unwrap().parse().unwrap();
    // SAFETY: this fixture has exactly one thread and no callbacks. Removing
    // test environment locators must not erase FIRST-entry strict custody.
    unsafe {
        for name in [
            "ATERM_SDK_LEASE_V3",
            "BUILD_SLOT_CPU_PROTOCOL",
            "TRUST_CPU_HANDOFF",
            "TRUST_CPU_IMPLICIT_FD",
            "CARGO_JOBSERVER_HANDOFF",
        ] {
            std::env::remove_var(name);
        }
        // The captured SDK keeper is another description, never this number.
        assert_eq!(libc::close(sdk), 0);
    }
    assert!(
        early::local(99, false).is_err(),
        "metadata must not mint producing tokens after env changes"
    );
    println!("ready");
    std::io::stdout().flush().unwrap();
    let mut line = String::new();
    std::io::stdin().lock().read_line(&mut line).unwrap();
}
