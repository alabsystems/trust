use std::io::Read;
use std::os::unix::process::ExitStatusExt;
use std::process::Stdio;

use super::*;

pub(crate) const ACTOR: &str = "admission::resources::machine::handoff::group::tests::group_actor";
pub(crate) const MODE: &str = "TRUST_FIXED_GROUP_TEST_MODE";

fn close_inherited_claim() {
    let value = std::env::var_os(FIXED_HANDOFF_ENV).unwrap();
    let packet = trust_build_cpu::duplicate_descriptor(&value).unwrap();
    let mut bytes = vec![0; packet.metadata().unwrap().len() as usize];
    packet.read_exact_at(&mut bytes, 0).unwrap();
    let description: Packet = serde_json::from_slice(&bytes).unwrap();
    for entry in description.files {
        assert!(entry.descriptor > 2);
        // SAFETY: only this isolated actor's explicitly inherited originals.
        assert_eq!(unsafe { libc::close(entry.descriptor) }, 0);
    }
    drop(packet);
    let descriptor = value.to_str().unwrap().parse::<i32>().unwrap();
    assert!(descriptor > 2);
    assert_eq!(unsafe { libc::close(descriptor) }, 0);
}

#[test]
fn group_actor() {
    let Some(mode) = std::env::var_os(MODE) else { return };
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    if mode == "native-output-root"
        || mode == "native-output-cwd-refusal"
        || mode == "native-output-observed-root"
        || mode == "native-output-observed-closed"
        || mode == "native-output-observed-alias"
    {
        super::super::output_member::tests::actor_root();
        return;
    }
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    if mode == "native-output-leaf" {
        super::super::output_member::tests::actor_leaf();
        return;
    }
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    if mode == "native-loaded-body" {
        super::loaded_tests::body();
        return;
    }
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    if mode == "native-observer-closed-reader" {
        super::loaded_tests::closed_reader_actor();
        println!("GROUP-ACTOR-READY {}", std::process::id());
        // The parent consumes that real completion marker then closes its
        // fixture stdout reader. Do not let a later libtest postamble hit
        // default SIGPIPE and misclassify the successful EPIPE body itself.
        std::process::exit(0);
    }
    if mode == "denied-absence-owner" {
        println!("ACTUAL-DENIED-ABSENCE-OWNER-ENTERED");
        persistent_post_reap_denial_keeps_actual_status_and_resources_until_unknown_drop();
        return;
    }
    if mode == "last-close-owner" {
        println!("ACTUAL-LAST-CLOSE-OWNER-ENTERED");
        dropping_a_group_retires_original_members_that_closed_all_claim_descriptors();
        return;
    }
    if mode == "ignored-owner" {
        assert_ne!(unsafe { libc::signal(libc::SIGHUP, libc::SIG_IGN) }, libc::SIG_ERR);
        let (_root, mut group, mut input, _) = actor_with_forwarder("ignored-leader", true);
        assert_eq!(signal_handler(libc::SIGHUP), libc::SIG_IGN);
        assert_eq!(unsafe { libc::kill(std::process::id() as i32, libc::SIGHUP) }, 0);
        assert_eq!(unsafe { libc::kill(-(group.id() as i32), libc::SIGHUP) }, 0);
        std::thread::sleep(Duration::from_millis(50));
        assert!(group.try_wait().unwrap().is_none(), "ignored HUP killed the actual child");
        input.write_all(&[1]).unwrap();
        assert!(group.wait().unwrap().success());
        drop(group);
        assert_eq!(signal_handler(libc::SIGHUP), libc::SIG_IGN);
        return;
    }
    if mode == "unsupported-reaper" {
        for (handler, flags) in [(libc::SIG_IGN, 0), (libc::SIG_DFL, libc::SA_NOCLDWAIT)] {
            let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
            action.sa_sigaction = handler;
            action.sa_flags = flags;
            assert_eq!(unsafe { libc::sigemptyset(&mut action.sa_mask) }, 0);
            assert_eq!(unsafe { libc::sigaction(libc::SIGCHLD, &action, std::ptr::null_mut()) }, 0);
            let (_root, claim) = super::super::tests::fixture();
            let error = claim
                .prepare_command(Command::new("must-not-be-executed"))
                .unwrap()
                .spawn_group_checked()
                .err()
                .unwrap();
            assert!(error.to_string().contains("SIGCHLD"), "{error}");
        }
        return;
    }
    if mode == "relay-owner" {
        let expected =
            std::env::var("TRUST_FIXED_GROUP_EXPECTED_SIGNAL").unwrap().parse::<i32>().unwrap();
        let previous = [libc::SIGINT, libc::SIGTERM, libc::SIGHUP].map(signal_handler);
        let (_root, mut group, _input, _) = actor_with_forwarder("leader", true);
        assert!(SignalRelay::install().is_err(), "another relay stole the live owner");
        println!("RELAY-OWNER-READY {}", std::process::id());
        io::stdout().flush().unwrap();
        assert_eq!(group.wait().unwrap().signal(), Some(expected));
        drop(group);
        assert_eq!([libc::SIGINT, libc::SIGTERM, libc::SIGHUP].map(signal_handler), previous);
        return;
    }
    if mode == "custom-handler" {
        extern "C" fn application_handler(_: libc::c_int) {}
        let handler = application_handler as *const () as libc::sighandler_t;
        assert_ne!(unsafe { libc::signal(libc::SIGTERM, handler) }, libc::SIG_ERR);
        let (_root, claim) = super::super::tests::fixture();
        let error = claim
            .prepare_command(Command::new("must-not-be-executed"))
            .unwrap()
            .spawn_with_forwarder_checked()
            .err()
            .unwrap();
        assert!(error.to_string().contains("existing application signal handler"));
        assert_eq!(signal_handler(libc::SIGTERM), handler);
        return;
    }
    if mode == "changed-handler" {
        extern "C" fn application_handler(_: libc::c_int) {}
        let handler = application_handler as *const () as libc::sighandler_t;
        let relay = SignalRelay::install().unwrap();
        assert_ne!(unsafe { libc::signal(libc::SIGTERM, handler) }, libc::SIG_ERR);
        drop(relay);
        assert_eq!(signal_handler(libc::SIGTERM), handler);
        return;
    }
    if mode == "external-wait-check" {
        let (root, mut group, mut input, _) = actor("leader");
        input.write_all(&[1]).unwrap();
        let mut status = 0;
        // Deliberately violate the single-waiter contract in this isolated
        // process. Unknown retirement must keep the actual original files.
        assert_eq!(unsafe { libc::waitpid(group.id() as i32, &mut status, 0) }, group.id() as i32);
        assert!(group.forward_signal(FixedCommandSignal::Terminate).is_err());
        assert!(group.cancel().is_err());
        drop(group);
        locked(root.path());
        return;
    }
    if mode == "parent" {
        close_inherited_claim();
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", ACTOR, "--nocapture"])
            .env(MODE, "member")
            .env_remove(FIXED_HANDOFF_ENV)
            .stdin(Stdio::inherit())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        let _member = command.spawn().unwrap();
        std::process::exit(83);
    }
    if mode == "leader" || mode == "ignored-leader" {
        close_inherited_claim();
    }
    if mode == "ignored-leader" {
        assert_eq!(signal_handler(libc::SIGHUP), libc::SIG_IGN);
    }
    if mode == "leader" || mode == "member" {
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            // SAFETY: this isolated actor restores ordinary termination before
            // publishing readiness; no other session's handler is changed.
            assert_ne!(unsafe { libc::signal(signal, libc::SIG_DFL) }, libc::SIG_ERR);
        }
    }
    println!("GROUP-ACTOR-READY {}", std::process::id());
    io::stdout().flush().unwrap();
    let mut byte = [0];
    let _ = io::stdin().read_exact(&mut byte);
    std::process::exit(0);
}

pub(super) fn actor(
    mode: &str,
) -> (tempfile::TempDir, RunningFixedGroup, std::process::ChildStdin, u32) {
    actor_with_forwarder(mode, false)
}

fn actor_with_forwarder(
    mode: &str,
    forward: bool,
) -> (tempfile::TempDir, RunningFixedGroup, std::process::ChildStdin, u32) {
    let (root, claim) = super::super::tests::fixture();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", ACTOR, "--nocapture"])
        .env(MODE, mode)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());
    let prepared = claim.prepare_command(command).unwrap();
    let mut group = if forward {
        prepared.spawn_with_forwarder_checked().unwrap()
    } else {
        prepared.spawn_group_checked().unwrap()
    };
    let input = match group.child_mut() {
        GroupChild::Standard(child) => child.stdin.take().unwrap(),
        #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
        GroupChild::Native(_) => unreachable!("this fixture selected standard piped stdio"),
    };
    let mut output = group.take_stdout().unwrap();
    let member = read_ready(&mut output, "GROUP-ACTOR-READY ");
    // Keep no output reader: the actual actors emit nothing more before exit.
    (root, group, input, member)
}

fn read_ready(output: &mut std::process::ChildStdout, marker: &str) -> u32 {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        assert!(Instant::now() < deadline, "original group readiness expired");
        let mut bytes = Vec::new();
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            assert!(!remaining.is_zero(), "original actor readiness expired");
            let mut poll =
                libc::pollfd { fd: output.as_raw_fd(), events: libc::POLLIN, revents: 0 };
            let ready = unsafe { libc::poll(&mut poll, 1, remaining.as_millis().min(5000) as i32) };
            assert!(ready > 0, "original actor readiness unavailable");
            let mut byte = [0];
            output.read_exact(&mut byte).expect("original actor ended before readiness");
            if byte[0] == b'\n' {
                break;
            }
            bytes.push(byte[0]);
            assert!(bytes.len() <= 4096, "original readiness row too large");
        }
        let row = String::from_utf8(bytes).unwrap();
        if let Some((_, value)) = row.split_once(marker) {
            return value.parse::<u32>().unwrap();
        }
    }
}

fn signal_handler(signal: libc::c_int) -> libc::sighandler_t {
    let mut action = std::mem::MaybeUninit::<libc::sigaction>::zeroed();
    assert_eq!(unsafe { libc::sigaction(signal, std::ptr::null(), action.as_mut_ptr()) }, 0);
    unsafe { action.assume_init() }.sa_sigaction
}

pub(crate) fn finish(group: &mut RunningFixedGroup) -> ExitStatus {
    let until = Instant::now() + Duration::from_secs(5);
    loop {
        if let Some(status) = group.try_wait().unwrap() {
            return status;
        }
        assert!(Instant::now() < until, "original group did not retire");
        std::thread::sleep(POLL);
    }
}

fn leader_exited(group: &RunningFixedGroup) {
    let until = Instant::now() + Duration::from_secs(5);
    while !group.leader_exited().unwrap() {
        assert!(Instant::now() < until, "actual leader did not exit");
        std::thread::sleep(POLL);
    }
}

pub(super) fn locked(root: &Path) {
    for path in [root.join("worktree.lock"), root.join("legacy/slot-0")] {
        let file = OpenOptions::new().read(true).write(true).open(path).unwrap();
        assert!(!try_exclusive(&file).unwrap());
    }
}

#[test]
fn natural_leader_exit_preserves_status_and_resources_until_original_member_finishes() {
    let (root, mut group, mut input, member) = actor("parent");
    assert_ne!(member, group.id());
    leader_exited(&group);
    assert!(group.try_wait().unwrap().is_none(), "leader exit was mistaken for group retirement");
    locked(root.path());
    input.write_all(&[1]).unwrap();
    assert_eq!(finish(&mut group).code(), Some(83));
    assert_eq!(group.try_wait().unwrap().unwrap().code(), Some(83));
    assert!(group.retired);
    locked(root.path());
    drop(group);
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn all_forwarded_signals_reach_only_the_actual_isolated_group() {
    struct OtherChild(Child);
    impl Drop for OtherChild {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut unrelated = OtherChild(
        Command::new("/bin/cat").stdin(Stdio::piped()).stdout(Stdio::null()).spawn().unwrap(),
    );
    for (signal, raw) in [
        (FixedCommandSignal::Interrupt, libc::SIGINT),
        (FixedCommandSignal::Terminate, libc::SIGTERM),
        (FixedCommandSignal::Hangup, libc::SIGHUP),
    ] {
        let (_root, mut group, _input, member) = actor("leader");
        assert_eq!(member, group.id());
        assert_eq!(unsafe { libc::getsid(member as i32) }, member as i32);
        assert_eq!(unsafe { libc::getpgid(member as i32) }, member as i32);
        group.forward_signal(signal).unwrap();
        let status = finish(&mut group);
        assert_eq!(status.signal(), Some(raw));
        group.forward_signal(signal).unwrap();
        assert!(unrelated.0.try_wait().unwrap().is_none(), "another original group was signalled");
    }
}

#[test]
fn cancellation_after_leader_exit_retires_members_without_losing_the_actual_status() {
    let (_root, mut group, _input, _member) = actor("parent");
    leader_exited(&group);
    assert_eq!(group.cancel().unwrap().code(), Some(83));
    assert!(group.group_gone().unwrap());
    assert_eq!(group.cancel().unwrap().code(), Some(83));
}

#[test]
fn forwarded_termination_reaches_a_live_member_after_its_original_leader_exited() {
    let (_root, mut group, _input, member) = actor("parent");
    leader_exited(&group);
    group.forward_signal(FixedCommandSignal::Terminate).unwrap();
    assert_eq!(finish(&mut group).code(), Some(83));
    assert!(!process::present(member).unwrap());
}

#[test]
fn dropping_a_group_retires_original_members_that_closed_all_claim_descriptors() {
    // Open original claim descriptions only in this same-binary owner.
    // Unrelated parallel test forks must not inherit them before exec.
    if std::env::var_os(MODE).as_deref() != Some(std::ffi::OsStr::new("last-close-owner")) {
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", ACTOR, "--nocapture"])
            .env(MODE, "last-close-owner")
            .output()
            .unwrap();
        assert!(output.status.success(), "actual isolated last-close owner: {output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("ACTUAL-LAST-CLOSE-OWNER-ENTERED"),
            "actual case must execute: {output:?}"
        );
        return;
    }
    let (root, group, _input, member) = actor("parent");
    leader_exited(&group);
    let original_group = group.group;
    drop(group);
    assert_eq!(unsafe { libc::kill(-original_group, 0) }, -1);
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    assert!(!process::present(member).unwrap());
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn original_record_replacement_does_not_prevent_owned_group_cancellation() {
    let (root, mut group, _input, _member) = actor("leader");
    let path = root.path().join("legacy/slot-0");
    fs::rename(&path, path.with_extension("original")).unwrap();
    crate::owner_only::write(&path, b"replacement");
    assert!(group.try_wait().is_err());
    assert_eq!(group.cancel().unwrap().signal(), Some(libc::SIGKILL));
    assert!(group.group_gone().unwrap());
}

// Each test's actors inherit the umask of the process that runs it, so these run
// in their own process whose umask is 002: the shared fixture's namespace and the
// record replacement keep their stated modes.
#[test]
fn fixture_tests_pass_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "admission::resources::machine::handoff::group::tests::fixture_tests_pass_under_a_group_writable_umask",
        || {
            natural_leader_exit_preserves_status_and_resources_until_original_member_finishes();
            original_record_replacement_does_not_prevent_owned_group_cancellation();
        },
    );
}

#[test]
fn externally_reaped_anchor_never_authorizes_a_group_signal() {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", ACTOR, "--nocapture"])
        .env(MODE, "external-wait-check")
        .output()
        .unwrap();
    assert!(output.status.success(), "isolated unknown owner: {output:?}");
    assert!(String::from_utf8_lossy(&output.stderr).contains("actual resources retained"));
}

#[test]
fn real_launcher_interruptions_forward_to_the_group_and_restore_previous_handlers() {
    struct Supervisor(Child);
    impl Drop for Supervisor {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
        let mut supervisor = Supervisor(
            Command::new(std::env::current_exe().unwrap())
                .args(["--exact", ACTOR, "--nocapture"])
                .env(MODE, "relay-owner")
                .env("TRUST_FIXED_GROUP_EXPECTED_SIGNAL", signal.to_string())
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::inherit())
                .spawn()
                .unwrap(),
        );
        let mut output = supervisor.0.stdout.take().unwrap();
        assert_eq!(read_ready(&mut output, "RELAY-OWNER-READY "), supervisor.0.id());
        assert_eq!(unsafe { libc::kill(supervisor.0.id() as i32, signal) }, 0);
        let until = Instant::now() + Duration::from_secs(5);
        loop {
            if let Some(status) = supervisor.0.try_wait().unwrap() {
                assert!(status.success(), "isolated signal-forwarding owner: {status}");
                break;
            }
            assert!(Instant::now() < until, "isolated forwarding owner did not retire");
            std::thread::sleep(POLL);
        }
    }
}

#[test]
fn standalone_forwarding_never_replaces_an_existing_application_handler() {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", ACTOR, "--nocapture"])
        .env(MODE, "custom-handler")
        .output()
        .unwrap();
    assert!(output.status.success(), "isolated application-handler refusal: {output:?}");
}

#[test]
fn relay_drop_does_not_overwrite_a_different_application_owner() {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", ACTOR, "--nocapture"])
        .env(MODE, "changed-handler")
        .output()
        .unwrap();
    assert!(output.status.success(), "isolated changed signal owner: {output:?}");
}

#[test]
fn ignored_hangup_stays_ignored_in_the_actual_launcher_and_exec_child() {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", ACTOR, "--nocapture"])
        .env(MODE, "ignored-owner")
        .output()
        .unwrap();
    assert!(output.status.success(), "isolated ignored signal control: {output:?}");
}

#[test]
fn autoreaping_sigchld_dispositions_refuse_before_any_group_delivery() {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", ACTOR, "--nocapture"])
        .env(MODE, "unsupported-reaper")
        .output()
        .unwrap();
    assert!(output.status.success(), "isolated reaper preflight control: {output:?}");
}

#[test]
fn transient_post_reap_denial_is_pending_until_actual_native_absence() {
    let (root, mut group, mut input, _) = actor("leader");
    input.write_all(&[1]).unwrap();
    leader_exited(&group);
    ABSENCE_FAULT.with(|fault| fault.set(Some((group.group, 3))));
    for _ in 0..3 {
        assert!(group.try_wait().unwrap().is_none());
        assert!(group.status.unwrap().success(), "preserve actual owning status");
        assert!(!group.retired);
        assert_eq!(group.absence_error.as_ref().unwrap().raw_os_error(), Some(libc::EPERM));
        locked(root.path());
    }
    // The final result must come from the real kernel, not the injected refusal.
    assert!(finish(&mut group).success());
    assert!(group.retired);
    drop(group);
    assert!(crate::admission::resources::tests::released(&root.path().join("legacy/slot-0")));
}

#[test]
fn persistent_post_reap_denial_keeps_actual_status_and_resources_until_unknown_drop() {
    if std::env::var_os(MODE).as_deref() != Some(std::ffi::OsStr::new("denied-absence-owner")) {
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", ACTOR, "--nocapture"])
            .env(MODE, "denied-absence-owner")
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("ACTUAL-DENIED-ABSENCE-OWNER-ENTERED"),
            "{output:?}"
        );
        return;
    }
    let (root, mut group, mut input, _) = actor("leader");
    input.write_all(&[1]).unwrap();
    leader_exited(&group);
    ABSENCE_FAULT.with(|fault| fault.set(Some((group.group, usize::MAX))));
    let error = group.cancel().unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    assert!(error.to_string().contains("Operation not permitted"), "{error}");
    assert!(group.status.unwrap().success(), "actual owning status remains known");
    assert!(!group.retired);
    locked(root.path());
    drop(group); // Same denial: original claim is retained through process exit.
    locked(root.path());
    ABSENCE_FAULT.with(|fault| fault.set(None));
}
