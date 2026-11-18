use std::ffi::CString;
use std::fs;
use std::io::Read;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::OpenOptionsExt;

use trust_resource_provenance::program::HeldSystemCommand;

use super::*;

const BODY: &str = "TRUST_NATIVE_LOADED_BODY";
const RELEASE: &str = "TRUST_NATIVE_LOADED_RELEASE";
const GNU: &str = "TRUST_NATIVE_LOADED_GNU";
const FALLBACK: &str = "TRUST_NATIVE_LOADED_EXPECTED_FALLBACK";

pub(crate) fn pipe() -> (File, File) {
    let mut pair = [-1; 2];
    // SAFETY: two writable descriptor slots, immediately uniquely owned on success.
    assert_eq!(unsafe { libc::pipe(pair.as_mut_ptr()) }, 0);
    // SAFETY: pipe returned these two fresh, independently owned descriptors.
    let pair = unsafe { pair.map(|fd| File::from_raw_fd(fd)) };
    for file in &pair {
        // SAFETY: only these fixture-owned original descriptions are configured.
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        assert!(flags >= 0);
        assert_eq!(
            unsafe { libc::fcntl(file.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) },
            0
        );
        assert_eq!(unsafe { libc::fcntl(file.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
    }
    let [reader, writer] = pair;
    (reader, writer)
}

fn gnu_identity(server: &jobserver_utils::Jobserver) -> [(u64, u64); 2] {
    server.pipe_descriptors().unwrap().each_ref().map(|fd| {
        let mut value = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: the same retained server owns this borrowed descriptor.
        assert_eq!(unsafe { libc::fstat(fd.as_raw_fd(), value.as_mut_ptr()) }, 0);
        // SAFETY: successful fstat initialized the complete value.
        let value = unsafe { value.assume_init() };
        (value.st_dev as u64, value.st_ino)
    })
}

pub(super) fn body() {
    // SAFETY: this fixture child retains the actual explicitly inherited GNU
    // originals, and this is its first and only native scheduling import.
    let server = unsafe { jobserver_utils::Jobserver::from_env() }.unwrap().unwrap();
    let expected: [(u64, u64); 2] = serde_json::from_str(&std::env::var(GNU).unwrap()).unwrap();
    assert_eq!(gnu_identity(&server), expected);
    // This is a token-conservation observation, never execution authority.
    // The maintained available() reader supports macOS; try_acquire() does not.
    assert_eq!(server.client().available().unwrap(), 0, "a GNU credit was replenished");
    if let Some(expected) = std::env::var_os(FALLBACK) {
        assert_eq!(std::env::var_os("DYLD_FALLBACK_LIBRARY_PATH"), Some(expected));
    }
    fs::write(std::env::var_os(BODY).unwrap(), b"actual-loaded-body").unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    while !Path::new(&std::env::var_os(RELEASE).unwrap()).exists() {
        assert!(Instant::now() < deadline, "fixture release never arrived");
        std::thread::sleep(POLL);
    }
}

pub(super) fn closed_reader_actor() {
    // SAFETY: this isolated original actor alone changes its signal disposition.
    assert_ne!(unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) }, libc::SIG_ERR);
    let (reader, writer) = pipe();
    drop(reader);
    let input = ExecutionStartPipe::from_owned_writer(writer).unwrap();
    let armed = execution_start::ExecutionStart::capture(input, []).unwrap();
    let error =
        armed.notify(std::process::id(), Instant::now() + Duration::from_secs(5)).unwrap_err();
    assert_eq!(error.raw_os_error(), Some(libc::EPIPE));
}

#[test]
fn original_notification_cannot_alias_an_owned_resource_description() {
    let (_reader, writer) = pipe();
    let duplicate = writer.try_clone().unwrap();
    assert_ne!(duplicate.as_raw_fd(), writer.as_raw_fd());
    let input = ExecutionStartPipe::from_owned_writer(duplicate).unwrap();
    let error =
        execution_start::ExecutionStart::capture(input, [writer.as_raw_fd()]).err().unwrap();
    assert!(error.to_string().contains("aliases original scheduling transport"));

    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("actual-gnu-fifo");
    let name = CString::new(path.as_os_str().as_bytes()).unwrap();
    // SAFETY: the fixture creates one new FIFO in its own private directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let scheduler = jobserver_utils::Jobserver::from_fifo(&path).unwrap();
    let originals = scheduler.retain_transport_descriptors().unwrap();
    let writer =
        fs::OpenOptions::new().write(true).custom_flags(libc::O_NONBLOCK).open(&path).unwrap();
    let input = ExecutionStartPipe::from_owned_writer(writer).unwrap();
    // Actual mode drift after the original pipe check must not make the SAME
    // retained GNU FIFO nonalias. This changes real kernel metadata rather
    // than supplying a forged identity or permission tuple.
    execution_start::AFTER_CHECK_MODE.with(|fault| {
        *fault.borrow_mut() = Some(File::from(originals[0].try_clone().unwrap()));
    });
    let error =
        execution_start::ExecutionStart::capture(input, originals.iter().map(AsRawFd::as_raw_fd))
            .err()
            .unwrap();
    assert!(error.to_string().contains("aliases original scheduling transport"));
}

#[test]
fn closed_notification_reader_preserves_default_sigpipe_owner() {
    let (_root, mut group, _input, _) = super::tests::actor("native-observer-closed-reader");
    // actor() requires the real child completion marker: zero selected tests
    // or death by default SIGPIPE cannot masquerade as successful execution.
    assert!(super::tests::finish(&mut group).success());
}

#[derive(Clone, Copy)]
enum LoadedCase {
    Run,
    Produced,
    ProducedFallback,
    ProducedWrongLoader,
    ProducedSdkDrift,
    ClosedReader,
    EarlyExit(PreGoExit),
}

fn loaded(case: LoadedCase) {
    let (root, claim) = super::super::tests::fixture();
    let executable = std::env::current_exe().unwrap();
    let system =
        HeldSystemCommand::open(&executable, Instant::now() + Duration::from_secs(30)).unwrap();
    let mut selected = executable.clone();
    let image = if matches!(
        case,
        LoadedCase::Produced
            | LoadedCase::ProducedFallback
            | LoadedCase::ProducedWrongLoader
            | LoadedCase::ProducedSdkDrift
    ) {
        use trust_resource_provenance::program::HeldProgram;
        use trust_resource_provenance::program::produced::HeldOutputRoot;
        // The existing input owner rejects symlink ancestors. tempfile may
        // return Darwin's /var alias; bind the actual physical fixture root.
        let physical = fs::canonicalize(root.path()).unwrap();
        let sdk = physical.join("sdk");
        let output = physical.join("output");
        fs::create_dir_all(sdk.join("bin")).unwrap();
        fs::create_dir(&output).unwrap();
        // Capture the original output directory before placing any artifact.
        // These fixture copies are actual compiled native bytes, not evidence
        // of compiler provenance, an SDK or a source/runtime grade.
        let original =
            HeldOutputRoot::open(&output, Instant::now() + Duration::from_secs(30)).unwrap();
        let hash = &system.observation().executable.sha256;
        let digest = std::array::from_fn(|index| {
            u8::from_str_radix(&hash[index * 2..index * 2 + 2], 16).unwrap()
        });
        let sdk_program = sdk.join("bin/fixture");
        fs::copy(&executable, &sdk_program).unwrap();
        let sdk = std::sync::Arc::new(
            HeldProgram::open(
                &sdk,
                &sdk_program,
                &digest,
                Instant::now() + Duration::from_secs(30),
            )
            .unwrap(),
        );
        selected = output.join("actual-compiled-fixture");
        fs::copy(&executable, &selected).unwrap();
        let image = std::sync::Arc::new(
            original
                .program(sdk, &selected, &digest, &[], Instant::now() + Duration::from_secs(30))
                .unwrap(),
        );
        let mut expected = image.runtime_environment().unwrap();
        if matches!(case, LoadedCase::ProducedFallback) {
            expected
                .push(("DYLD_FALLBACK_LIBRARY_PATH".into(), output.join("unused-fallback").into()));
        }
        NativeGroupImage::Produced(
            image.execution(&expected, Instant::now() + Duration::from_secs(30)).unwrap(),
        )
    } else {
        NativeGroupImage::System(system)
    };
    let mut scheduler = jobserver_utils::Jobserver::new(1).unwrap();
    scheduler.client().acquire_raw().unwrap();
    assert_eq!(scheduler.client().available().unwrap(), 0);
    let body = root.path().join("actual-body");
    let release = root.path().join("release-body");
    let mut command = Command::new(&selected);
    command.args(["--exact", super::tests::ACTOR, "--nocapture", "--test-threads=1"]);
    command.env(super::tests::MODE, "native-loaded-body");
    command.env(BODY, &body).env(RELEASE, &release);
    command.env(GNU, serde_json::to_string(&gnu_identity(&scheduler)).unwrap());
    // This known fixture image has no non-system imports. Remove only its own
    // test-launcher's ambient loader list; production still refuses overrides.
    for (name, _) in std::env::vars_os() {
        if name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_") {
            command.env_remove(name);
        }
    }
    if matches!(case, LoadedCase::ProducedWrongLoader) {
        command.env("DYLD_LIBRARY_PATH", root.path().join("unheld"));
    }
    if matches!(case, LoadedCase::ProducedFallback) {
        let fallback = fs::canonicalize(root.path()).unwrap().join("output/unused-fallback");
        command.env("DYLD_FALLBACK_LIBRARY_PATH", &fallback).env(FALLBACK, fallback);
    }
    scheduler.enable_descendant_handoff().unwrap();
    scheduler.configure_make(&mut command);
    let prepared = claim.prepare_command(command).unwrap();
    let (mut reader, writer) = pipe();
    let input = ExecutionStartPipe::from_owned_writer(writer).unwrap();
    if matches!(case, LoadedCase::ProducedWrongLoader) {
        // SAFETY: the same original fixture GNU/command contract applies;
        // the mismatched environment must refuse before any child can start.
        let error = unsafe {
            prepared.spawn_loaded_group_checked(
                image,
                scheduler,
                Some(input),
                Instant::now() + Duration::from_secs(10),
                None,
            )
        }
        .err()
        .unwrap();
        assert!(error.to_string().contains("original runtime environment"));
        assert!(!body.exists());
        for path in [root.path().join("worktree.lock"), root.path().join("legacy/slot-0")] {
            assert!(crate::admission::resources::tests::released(&path));
        }
        return;
    }
    if matches!(case, LoadedCase::ClosedReader | LoadedCase::EarlyExit(_)) {
        if let LoadedCase::EarlyExit(point) = case {
            PRE_GO_EXIT.set(Some(point));
        }
        if matches!(case, LoadedCase::ClosedReader) {
            drop(reader);
        }
        // SAFETY: inherited console/cwd, no caller callbacks or env_clear;
        // this same original GNU continuation remains serially paused. The
        // private fixture already owns its actual slot/worktree descriptions.
        let error = unsafe {
            prepared.spawn_loaded_group_checked(
                image,
                scheduler,
                Some(input),
                Instant::now() + Duration::from_secs(10),
                None,
            )
        }
        .err()
        .unwrap();
        match case {
            LoadedCase::ClosedReader => assert_eq!(error.raw_os_error(), Some(libc::EPIPE)),
            LoadedCase::EarlyExit(_) => {
                assert!(error.to_string().contains("awaiting GO"), "{error}")
            }
            LoadedCase::Run
            | LoadedCase::Produced
            | LoadedCase::ProducedFallback
            | LoadedCase::ProducedWrongLoader
            | LoadedCase::ProducedSdkDrift => {
                unreachable!()
            }
        }
        assert!(!body.exists(), "a notification failure let loaded code run");
        // The still-stopped child cannot service ordinary TERM. The same
        // owner must KILL, reap and prove group absence before this release.
        for path in [root.path().join("worktree.lock"), root.path().join("legacy/slot-0")] {
            assert!(crate::admission::resources::tests::released(&path));
        }
        return;
    }
    // SAFETY: the same exact fixture command/original GNU contract above.
    let mut group = unsafe {
        prepared.spawn_loaded_group_checked(
            image,
            scheduler,
            Some(input),
            Instant::now() + Duration::from_secs(10),
            None,
        )
    }
    .unwrap();
    let mut message = [0; 17];
    // This reader is nonblocking: a missing notification fails, never hangs.
    reader.read_exact(&mut message).unwrap();
    assert_eq!(message[0], b'S');
    assert_eq!(u64::from_be_bytes(message[1..9].try_into().unwrap()), u64::from(group.id()));
    assert_ne!(u64::from_be_bytes(message[9..].try_into().unwrap()), 0);
    super::tests::locked(root.path());
    let deadline = Instant::now() + Duration::from_secs(10);
    while !body.exists() {
        assert!(Instant::now() < deadline, "actual loaded body did not run");
        std::thread::sleep(POLL);
    }
    assert_eq!(fs::read(&body).unwrap(), b"actual-loaded-body");
    if matches!(case, LoadedCase::ProducedSdkDrift) {
        let original = root.path().join("sdk/bin/fixture");
        fs::rename(&original, root.path().join("sdk/bin/displaced-original")).unwrap();
        fs::copy(&executable, &original).unwrap();
    }
    fs::write(&release, b"release").unwrap();
    if matches!(case, LoadedCase::ProducedSdkDrift) {
        assert!(group.wait().is_err(), "same-byte SDK path replacement was accepted");
    } else {
        assert!(super::tests::finish(&mut group).success());
    }
    drop(group);
    for path in [root.path().join("worktree.lock"), root.path().join("legacy/slot-0")] {
        assert!(crate::admission::resources::tests::released(&path));
    }
}

#[test]
fn native_loaded_group_notifies_at_go_and_retains_originals_until_exit() {
    loaded(LoadedCase::Run);
}

#[test]
fn produced_native_group_retains_original_output_sdk_and_runtime_until_exit() {
    loaded(LoadedCase::Produced);
}

#[test]
fn produced_native_group_preserves_exact_inert_fallback_through_real_exec() {
    loaded(LoadedCase::ProducedFallback);
}

#[test]
fn produced_native_group_refuses_unheld_loader_environment_before_body() {
    loaded(LoadedCase::ProducedWrongLoader);
}

#[test]
fn produced_native_group_rejects_original_sdk_drift_at_retirement() {
    loaded(LoadedCase::ProducedSdkDrift);
}

#[test]
fn closed_native_observer_retires_unrun_loaded_group_without_body() {
    loaded(LoadedCase::ClosedReader);
}

#[test]
fn pre_go_exit_preserves_the_owning_wait_and_releases_original_claims() {
    for point in [PreGoExit::BeforeIdentity, PreGoExit::BeforeResume] {
        loaded(LoadedCase::EarlyExit(point));
    }
}
