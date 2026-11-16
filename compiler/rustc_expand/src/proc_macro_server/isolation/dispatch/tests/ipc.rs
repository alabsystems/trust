//! Trust (D21): real subprocesses use the exact native Client and B1 bytes.
//! No fixture process is a production launcher, sandbox or readiness proof.
use std::io::{Read, Write};
use std::os::fd::{AsFd, AsRawFd, OwnedFd};
use std::os::unix::net::UnixStream;
use std::process::{Child, Command, ExitStatus, Stdio};

use rustc_proc_macro::bridge::client::Client;
use trust_proc_macro_bridge::unix::UnixTransport;
use trust_proc_macro_bridge::{Transport, Worker};
use trust_process_isolation::{decode, encode};

use super::*;

const MODE: &str = "TRUST_D21_NATIVE_IPC_FIXTURE";
const DSO_PATH: &str = "TRUST_D21_NATIVE_DSO";
const DSO_SYMBOL: &str = "TRUST_D21_NATIVE_DSO_SYMBOL";
const PRIVATE_TMPDIR: &str = "TRUST_D21_PRIVATE_TMPDIR";

#[cfg(target_os = "macos")]
mod darwin;

struct ChildOwner {
    child: Child,
    reaped: bool,
}
impl ChildOwner {
    fn wait(&mut self, budget: &Budget) -> Result<ExitStatus, Error> {
        loop {
            budget.check()?;
            match self.child.try_wait() {
                Ok(Some(status)) => {
                    self.reaped = true;
                    budget.check()?;
                    return Ok(status);
                }
                Ok(None) => std::thread::sleep(Duration::from_millis(1)),
                Err(_) => return Err(Error::InvalidWire("fixture child wait")),
            }
        }
    }
    fn stop(&mut self) {
        if !self.reaped {
            let _ = self.child.kill();
            self.reaped = self.child.wait().is_ok();
        }
    }
}
impl Drop for ChildOwner {
    fn drop(&mut self) {
        self.stop();
    }
}

fn spawn(mode: &str) -> (UnixStream, ChildOwner) {
    let (parent, child) = UnixStream::pair().unwrap();
    let endpoint: OwnedFd = child.into();
    let name = concat!(module_path!(), "::native_ipc_subprocess_entry").split_once("::").unwrap().1;
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", name, "--nocapture"])
        .env_clear()
        .env(MODE, mode)
        .stdin(Stdio::from(endpoint))
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    // These are the test binary's already-selected dynamic runtime paths, not
    // an admitted native closure. The production launcher must seal its own.
    for key in ["LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH", "DYLD_FALLBACK_LIBRARY_PATH"] {
        if let Some(value) = std::env::var_os(key) {
            command.env(key, value);
        }
    }
    if mode.starts_with("dso") {
        for key in [DSO_PATH, DSO_SYMBOL] {
            command.env(key, std::env::var_os(key).expect("explicit native DSO fixture input"));
        }
        // Keep the cleared environment. Only the runner's separately named,
        // validated private directory becomes TMPDIR in the native child.
        if let Some(directory) = std::env::var_os(PRIVATE_TMPDIR) {
            command.env("TMPDIR", darwin_private_tmpdir(&directory));
        }
        if mode == "dso-readonly-sandbox" {
            command.stderr(Stdio::inherit());
        }
    }
    let child = command.spawn().unwrap();
    drop(command); // no parent copy of the child's socket remains here
    (parent, ChildOwner { child, reaped: false })
}

fn darwin_private_tmpdir(directory: &std::ffi::OsStr) -> std::path::PathBuf {
    use std::os::unix::fs::MetadataExt;
    let path = std::path::PathBuf::from(directory);
    assert!(path.is_absolute());
    assert_eq!(path.canonicalize().unwrap(), path, "private TMPDIR must be canonical");
    for candidate in [&path, &path.join(".ubd")] {
        let metadata = candidate.symlink_metadata().unwrap();
        assert!(metadata.is_dir() && !metadata.file_type().is_symlink());
        // SAFETY: query only the current process's effective UID.
        assert_eq!(metadata.uid(), unsafe { libc::geteuid() });
        assert_eq!(metadata.mode() & 0o777, 0o700);
    }
    path
}

#[cfg(target_os = "macos")]
fn private_tmpdir_token(directory: &std::path::Path) -> String {
    use std::fmt::Write;
    use std::os::unix::ffi::OsStrExt;
    let mut result = String::new();
    for byte in directory.as_os_str().as_bytes() {
        write!(&mut result, "{byte:02x}").unwrap();
    }
    result
}

#[test]
fn private_tmpdir_requires_canonical_owned_private_directories() {
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt, symlink};
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let parent = std::env::temp_dir().canonicalize().unwrap().join(".ubd");
    std::fs::create_dir_all(&parent).unwrap();
    let root = parent.join(format!(
        "private-tmpdir-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
    let scratch = root.join(".ubd");
    std::fs::DirBuilder::new().mode(0o700).create(&scratch).unwrap();
    assert_eq!(darwin_private_tmpdir(root.as_os_str()), root);
    for path in [&root, &scratch] {
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(std::panic::catch_unwind(|| darwin_private_tmpdir(root.as_os_str())).is_err());
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
    }
    std::fs::remove_dir(&scratch).unwrap();
    symlink(".", &scratch).unwrap();
    assert!(std::panic::catch_unwind(|| darwin_private_tmpdir(root.as_os_str())).is_err());
    std::fs::remove_file(&scratch).unwrap();
    let alias = root.with_extension("link");
    symlink(&root, &alias).unwrap();
    assert!(std::panic::catch_unwind(|| darwin_private_tmpdir(alias.as_os_str())).is_err());
    std::fs::remove_file(alias).unwrap();
    std::fs::remove_dir(root).unwrap();
}

#[test]
fn native_ipc_subprocess_entry() {
    let Ok(mode) = std::env::var(MODE) else {
        return;
    };
    // stdin was passed as the child endpoint of an unnamed Unix socket pair.
    // Duplicating the borrowed descriptor gives one Rust owner without raw-FD
    // adoption or a path reopen. Shutdown closes the connection for both copies.
    let owned = std::io::stdin().as_fd().try_clone_to_owned().unwrap();
    let stream = UnixStream::from(owned);
    let raw = stream.try_clone().unwrap();
    let budget = Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap();
    let mut transport = UnixTransport::new(stream, budget.clone()).unwrap();
    if mode == "sigpipe" {
        // SAFETY: this isolated fixture process owns its signal disposition;
        // the parent and every production process remain unchanged.
        assert_ne!(unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) }, libc::SIG_ERR);
        // A test-only existing B1 reply coordinates closure after constructor
        // admission. This is not a Ready message or an authority grant.
        let frame = encode(
            &Envelope { binding: binding(), message: Message::Reply { id: 1, value: Value::Unit } },
            &budget,
        )
        .unwrap();
        transport.send(&frame, &budget).unwrap();
        let mut raw = raw;
        loop {
            budget.check().unwrap();
            match raw.read(&mut [0; 1]) {
                Ok(0) => break,
                Ok(_) => panic!("unexpected signal-fixture input"),
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    std::thread::sleep(Duration::from_millis(1))
                }
                Err(e) => panic!("signal-fixture read: {e}"),
            }
        }
        assert!(transport.send(&frame, &budget).is_err());
        return;
    }
    if mode == "no-read" {
        loop {
            std::thread::park();
        }
    }
    let begin = decode(&transport.receive(&budget).unwrap(), &budget).unwrap();
    if mode == "abort" {
        std::process::exit(71);
    }
    if mode == "truncated" {
        let mut raw = raw;
        raw.write_all(&[9, 0, 0, 0, 1, 2]).unwrap();
        return;
    }
    if mode == "oversized" {
        let mut raw = raw;
        raw.write_all(&u32::MAX.to_le_bytes()).unwrap();
        return;
    }
    if mode == "post-finish" {
        let Message::Begin { inputs, .. } = &begin.message else {
            panic!("begin");
        };
        let frame = encode(
            &Envelope {
                binding: begin.binding.clone(),
                message: Message::Finish { output: Some(inputs[0]) },
            },
            &budget,
        )
        .unwrap();
        let mut raw = raw;
        raw.write_all(&frame).unwrap();
        raw.write_all(&[1]).unwrap();
        return;
    }
    let mut worker = Worker::from_begin(begin, budget, transport).unwrap();
    let client = if mode == "hang" {
        Client::expand1(|_input| {
            rustc_proc_macro::tracked::path("ipc-entered");
            loop {
                std::thread::park();
            }
        })
    } else if mode == "native" {
        Client::expand1(super::worker::all_methods)
    } else if mode == "cancel" {
        Client::expand1(|input| {
            rustc_proc_macro::tracked::path("ipc-cancel");
            input
        })
    } else {
        Client::expand1(|input| input)
    };
    let result = if mode.starts_with("dso") {
        #[cfg(target_os = "macos")]
        let image = (mode == "dso-readonly-sandbox").then(darwin::restrict_readonly_fixture);
        #[cfg(target_os = "macos")]
        let retained = image.as_ref().map(|image| image.loader_path());
        #[cfg(not(target_os = "macos"))]
        let retained = None;
        let result = worker
            .run_declared(native_fixture_declarations(mode == "dso-wrong-symbol", retained), false);
        // Retain the admitted descriptor until this disposable process exits,
        // just as its dlopen handle stays loaded for the complete child lifetime.
        #[cfg(target_os = "macos")]
        std::mem::forget(image);
        result
    } else {
        worker.run_declared(&[client], false)
    };
    if mode == "cancel" {
        assert!(result.is_err());
    } else {
        result.unwrap();
    }
    if mode == "finish-live" {
        loop {
            std::thread::park();
        }
    }
}

/// Load only in this disposable test child. Production admission is unchanged.
/// The explicit test runner binds the compiled DSO, native runtime and compiler
/// identities; this fixture does not assert containment or loader authority.
fn native_fixture_declarations(
    wrong_symbol: bool,
    retained: Option<&std::ffi::CStr>,
) -> &'static [Client] {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    let path = match retained {
        Some(path) => path.to_owned(),
        None => {
            let path = std::env::var_os(DSO_PATH).expect("native DSO fixture path");
            CString::new(path.as_bytes()).expect("native DSO path contains no NUL")
        }
    };
    let symbol = std::env::var(DSO_SYMBOL).expect("matching compiler-generated declaration symbol");
    let symbol = if wrong_symbol { format!("{symbol}_absent") } else { symbol };
    let symbol = CString::new(symbol).expect("declaration symbol contains no NUL");
    // SAFETY: this is the explicitly selected native-fixture child, never the
    // compiler parent. The matching compiler generated the declaration slice
    // with its existing proc_macro Client ABI, as in host_dylib::dlsym_proc_macros.
    // No foreign code is admitted into the verifier. The handle is deliberately
    // kept loaded until process exit so Client function pointers cannot dangle.
    unsafe {
        let library = libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
        if library.is_null() {
            let error = libc::dlerror();
            let message = if error.is_null() {
                "unknown".into()
            } else {
                std::ffi::CStr::from_ptr(error).to_string_lossy().into_owned()
            };
            panic!("native fixture DSO must load: {message}");
        }
        let pointer = libc::dlsym(library, symbol.as_ptr());
        assert!(!pointer.is_null(), "matching native declaration symbol must exist");
        let declarations = *pointer.cast::<&'static [Client]>();
        assert_eq!(declarations.len(), 2, "exact two-declaration fixture");
        declarations
    }
}

#[derive(Default)]
struct Observed {
    methods: Vec<Method>,
    finished: bool,
    eof: bool,
    reaped: bool,
    output: Option<String>,
    entered: bool,
}

fn exchange(mode: &str, duration: Duration) -> (Result<(), Error>, Observed) {
    exchange_declaration(mode, duration, 0)
}

fn exchange_declaration(
    mode: &str,
    duration: Duration,
    declaration: u32,
) -> (Result<(), Error>, Observed) {
    let mut observed = Observed::default();
    let mut result = Ok(());
    with_dispatcher_deadline(duration, |d, s, _, _| {
        let budget = s.budget().clone();
        let input = d.server.ts_from_str("alpha beta").unwrap();
        let input = d.store_input(input).unwrap();
        let begin = Envelope {
            binding: s.binding().clone(),
            message: Message::Begin {
                declaration,
                kind: 0,
                inputs: vec![input],
                globals: d.globals,
            },
        };
        let (socket, mut child) = spawn(mode);
        let mut transport = UnixTransport::new(socket, budget.clone()).unwrap();
        result = (|| {
            transport.send(&encode(&begin, &budget)?, &budget)?;
            loop {
                let bytes = match transport.receive_frame(&budget)? {
                    Some(bytes) => bytes,
                    None => {
                        observed.eof = true;
                        break;
                    }
                };
                if observed.finished {
                    return Err(Error::InvalidWire("post-finish bytes"));
                }
                match s.receive(decode(&bytes, &budget)?)? {
                    Admission::Call(call) => {
                        observed.methods.push(call.method);
                        if call.method == Method::TrackPath {
                            observed.entered = true;
                        }
                        if mode == "cancel" {
                            budget.cancel();
                        }
                        let id = call.id;
                        let value = d.dispatch(s, call)?;
                        let reply = s.reply(id, value)?;
                        transport.send(&encode(&reply, &budget)?, &budget)?;
                    }
                    Admission::Finished(handle) => {
                        observed.finished = true;
                        observed.output = Some(match handle {
                            Some(h) => {
                                let stream = d.tokens.stream(h)?;
                                d.server.ts_to_string(&stream)
                            }
                            None => String::new(),
                        });
                    }
                    _ => return Err(Error::Phase),
                }
            }
            if !observed.finished {
                return Err(Error::InvalidWire("missing finish"));
            }
            let status = child.wait(&budget)?;
            if !status.success() {
                return Err(Error::InvalidWire("native fixture exit"));
            }
            budget.check()
        })();
        if let Err(error) = &result {
            budget.refuse(error.clone());
            s.cancel();
            observed.output = None;
        }
        transport.close();
        child.stop();
        observed.reaped = child.reaped;
        d.tokens.values.clear();
        if result.is_ok() {
            assert_eq!(budget.check(), Ok(()));
        } else {
            assert!(budget.check().is_err());
        }
    });
    (result, observed)
}

#[test]
#[ignore = "requires explicitly built matching native_worker_client proc-macro DSO and symbol"]
fn real_proc_macro_dso_preserves_declared_client_and_native_tokens() {
    for (declaration, expected) in [(0, "selected_first_declaration"), (1, "alpha beta")] {
        let (result, observed) = exchange_declaration("dso", Duration::from_secs(30), declaration);
        result.unwrap();
        assert!(observed.finished && observed.eof && observed.reaped);
        assert_eq!(observed.output.as_deref(), Some(expected));
        if declaration == 1 {
            let mut tags = observed.methods.iter().map(|method| method.tag()).collect::<Vec<_>>();
            tags.sort_unstable();
            tags.dedup();
            assert_eq!(tags, Method::ALL.iter().map(|method| method.tag()).collect::<Vec<_>>());
        }
    }
    for (mode, declaration) in [("dso", 2), ("dso", u32::MAX), ("dso-wrong-symbol", 0)] {
        let (result, observed) = exchange_declaration(mode, Duration::from_secs(30), declaration);
        assert!(result.is_err(), "{mode}/{declaration} must refuse");
        assert!(!observed.finished, "a refused declaration cannot send Finish");
        assert!(observed.reaped && observed.output.is_none());
    }
}

#[cfg(target_os = "macos")]
#[test]
#[ignore = "requires exact native DSO in an independently prepared read-only mounted image"]
fn darwin_readonly_image_runs_native_client_after_fixed_restrictions() {
    let (result, observed) =
        exchange_declaration("dso-readonly-sandbox", Duration::from_secs(30), 1);
    result.unwrap();
    assert!(observed.finished && observed.eof && observed.reaped);
    assert_eq!(observed.output.as_deref(), Some("alpha beta"));
    let mut tags = observed.methods.iter().map(|method| method.tag()).collect::<Vec<_>>();
    tags.sort_unstable();
    tags.dedup();
    assert_eq!(tags, Method::ALL.iter().map(|method| method.tag()).collect::<Vec<_>>());
}

#[cfg(target_os = "macos")]
#[test]
#[ignore = "requires the actual constructor DSO and runner-owned private TMPDIR"]
fn darwin_constructor_uses_private_tmpdir_before_client_entry() {
    let directory = darwin_private_tmpdir(&std::env::var_os(PRIVATE_TMPDIR).unwrap());
    let expected = format!("selected_first_declaration_tmp_{}", private_tmpdir_token(&directory));
    for (declaration, expected) in [(0, expected.as_str()), (1, "alpha beta")] {
        let (result, observed) =
            exchange_declaration("dso-readonly-sandbox", Duration::from_secs(30), declaration);
        result.unwrap();
        assert!(observed.finished && observed.eof && observed.reaped);
        assert_eq!(
            observed.output.as_deref(),
            Some(expected),
            "constructor used another temporary directory"
        );
        if declaration == 1 {
            let mut tags = observed.methods.iter().map(|method| method.tag()).collect::<Vec<_>>();
            tags.sort_unstable();
            tags.dedup();
            assert_eq!(tags, Method::ALL.iter().map(|method| method.tag()).collect::<Vec<_>>());
        }
    }
}

#[test]
fn real_subprocess_native_abi_runs_all_methods_and_requires_clean_exit() {
    let (result, observed) = exchange("native", Duration::from_secs(30));
    result.unwrap();
    assert!(observed.finished && observed.eof && observed.reaped);
    assert_eq!(observed.output.as_deref(), Some("alpha beta"));
    let mut tags = observed.methods.iter().map(|m| m.tag()).collect::<Vec<_>>();
    tags.sort_unstable();
    tags.dedup();
    assert_eq!(tags, Method::ALL.iter().map(|m| m.tag()).collect::<Vec<_>>());
}

#[test]
fn child_death_truncation_oversize_and_post_finish_bytes_refuse_and_reap() {
    for mode in ["abort", "truncated", "oversized", "post-finish"] {
        let (result, observed) = exchange(mode, Duration::from_secs(30));
        assert!(result.is_err(), "{mode}");
        assert!(observed.reaped);
        assert!(observed.output.is_none());
    }
}

#[test]
fn original_deadline_and_cancellation_close_and_reap_real_native_children() {
    for mode in ["hang", "finish-live"] {
        let (result, observed) = exchange(mode, Duration::from_secs(3));
        assert_eq!(result, Err(Error::Deadline));
        assert!(observed.reaped);
        assert!(observed.output.is_none());
        if mode == "hang" {
            assert!(observed.entered);
        } else {
            assert!(observed.finished && observed.eof);
        }
    }
    let (result, observed) = exchange("cancel", Duration::from_secs(30));
    assert!(result.is_err());
    assert!(observed.reaped);
    assert!(observed.output.is_none());
}

#[test]
fn broken_peer_cannot_kill_native_child_when_sigpipe_is_default() {
    let (socket, mut child) = spawn("sigpipe");
    let budget = Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap();
    let mut transport = UnixTransport::new(socket, budget.clone()).unwrap();
    let frame = transport.receive(&budget).unwrap();
    assert!(matches!(
        decode(&frame, &budget).unwrap().message,
        Message::Reply { id: 1, value: Value::Unit }
    ));
    transport.close();
    let status = child.wait(&budget).unwrap();
    assert!(status.success(), "signal fixture exited {status}");
    assert!(child.reaped);
}

#[test]
fn stalled_real_peer_causes_bounded_partial_send_and_sticky_refusal() {
    let (socket, mut child) = spawn("no-read");
    let size: libc::c_int = 1024;
    // SAFETY: the live socket and correctly sized initialized scalar remain
    // valid for this test-only socket-buffer setting; it grants no authority.
    assert_eq!(
        unsafe {
            libc::setsockopt(
                socket.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_SNDBUF,
                (&size as *const libc::c_int).cast(),
                std::mem::size_of_val(&size) as libc::socklen_t,
            )
        },
        0
    );
    let mut l = limits();
    l.frame_bytes = 8 << 20;
    l.wire_bytes = 32 << 20;
    l.allocation_bytes = 128 << 20;
    l.work = 128 << 20;
    let budget = Budget::new(l, Instant::now() + Duration::from_secs(1)).unwrap();
    let mut transport = UnixTransport::new(socket, budget.clone()).unwrap();
    let frame = encode(
        &Envelope { binding: binding(), message: Message::Failure { reason: "x".repeat(4 << 20) } },
        &budget,
    )
    .unwrap();
    assert_eq!(transport.send(&frame, &budget), Err(Error::Deadline));
    assert_eq!(transport.send(&frame, &budget), Err(Error::Deadline));
    assert_eq!(budget.check(), Err(Error::Deadline));
    transport.close();
    child.stop();
    assert!(child.reaped);
}

#[test]
fn transport_uses_the_original_budget_and_does_not_charge_wire_twice() {
    let (a, b) = UnixStream::pair().unwrap();
    let budget = Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap();
    let mut sender = UnixTransport::new(a, budget.clone()).unwrap();
    let mut receiver = UnixTransport::new(b, budget.clone()).unwrap();
    let frame = encode(
        &Envelope { binding: binding(), message: Message::Finish { output: None } },
        &budget,
    )
    .unwrap();
    let before = budget.usage().unwrap().wire_bytes;
    sender.send(&frame, &budget).unwrap();
    let received = receiver.receive(&budget).unwrap();
    assert_eq!(received, frame);
    assert_eq!(budget.usage().unwrap().wire_bytes, before);
    let other = Budget::new(limits(), budget.deadline()).unwrap();
    assert_eq!(sender.send(&frame, &other), Err(Error::Identity));
    assert_eq!(budget.check(), Err(Error::Identity));
    assert_eq!(other.check(), Ok(()));
}

#[test]
fn changing_owned_socket_flags_is_detected_before_the_next_operation() {
    let (socket, _peer) = UnixStream::pair().unwrap();
    let alias = socket.try_clone().unwrap();
    let budget = Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap();
    let mut transport = UnixTransport::new(socket, budget.clone()).unwrap();
    // SAFETY: the alias is a live fixture-owned descriptor. F_GETFL has no
    // variadic argument; the scalar is observed solely for this negative test.
    let flags = unsafe { libc::fcntl(alias.as_raw_fd(), libc::F_GETFL) };
    assert!(flags >= 0 && flags & libc::O_NONBLOCK != 0);
    alias.set_nonblocking(false).unwrap();
    let frame = encode(
        &Envelope { binding: binding(), message: Message::Finish { output: None } },
        &budget,
    )
    .unwrap();
    assert_eq!(
        transport.send(&frame, &budget),
        Err(Error::InvalidWire("worker socket is blocking"))
    );
    assert_eq!(budget.check(), Err(Error::InvalidWire("worker socket is blocking")));
    assert_eq!(
        transport.send(&frame, &budget),
        Err(Error::InvalidWire("worker socket is blocking"))
    );
}
