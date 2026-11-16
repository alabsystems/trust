//! Trust (D21): the compiler's side of the isolated proc-macro worker.
//!
//! Under `-Ztrust-proc-macro-isolation` rustc's crate loader does not open a
//! proc-macro dylib. Each expansion is sent to a worker process instead: the
//! compiler's own executable in its worker role (`worker.rs`), which installs
//! the deny-default sandbox and only then opens the dylib. The worker is given
//! this process's environment and working directory, because a macro reads
//! both, but none of its descriptors: its standard input is one end of an
//! unnamed socket pair carrying B1 frames, its standard output and error are
//! `/dev/null`, and it closes everything else before any macro code runs.
//!
//! One worker serves one dylib for the whole session, as the dylib's statics
//! live for the whole session when it is loaded in process. A nested expansion
//! (`TokenStream::expand_expr` reaching a macro of the same dylib while its
//! worker is busy) gets a second worker.
//!
//! Every value the worker sends is checked by the B1 session and the
//! dispatcher before it becomes a compiler token or span. What the worker
//! cannot do is the point: it cannot write to this process's stderr, touch its
//! memory, or change a file outside its private temporary directory.
//!
//! The limits below bound accounting overflow and a silent worker, not memory:
//! in-process expansion has no budget, so a budget small enough to bite would
//! refuse programs that compile today.

use std::path::PathBuf;

use rustc_ast::tokenstream::TokenStream;
use rustc_errors::ErrorGuaranteed;
use rustc_span::Span;
use trust_process_isolation::Limits;

use crate::base::ExtCtxt;
use crate::diagnostics;

/// One proc-macro crate whose dylib only a worker opens. Leaked once per
/// loaded crate, like the dylib handle of an in-process load.
#[derive(Debug)]
pub struct IsolatedDylib {
    pub crate_name: String,
    /// The canonical dylib path the worker opens.
    pub path: PathBuf,
    /// The crate's `__rustc_proc_macro_decls_*__` symbol.
    pub symbol: String,
}

/// One macro of an isolated dylib: the index of its declaration, which the
/// compiler read from the crate's metadata, never from the dylib.
#[derive(Clone, Copy, Debug)]
pub struct IsolatedClient {
    pub dylib: &'static IsolatedDylib,
    pub declaration: u32,
}

/// B1's `Begin.kind`. Only `Attr` carries two input streams.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Shape {
    Bang = 0,
    Attr = 1,
    Derive = 2,
}

pub(crate) enum Failure {
    /// The macro panicked: the same event, with the same message, as a panic
    /// of the macro in process. The caller reports it as it reports that.
    Panicked(Option<String>),
    /// The expansion was refused and the refusal has been reported.
    Refused(ErrorGuaranteed),
}

/// Accounting ceilings shared by both ends. See the module comment.
pub(crate) const LIMITS: Limits = Limits {
    frame_bytes: 1 << 28,
    wire_bytes: 1 << 56,
    allocation_bytes: 1 << 56,
    values: 1 << 56,
    work: 1 << 56,
    calls: 1 << 40,
    live_handles: 1 << 20,
    depth: 128,
};

/// The worker's first argument. The canonical compiler executable checks for it
/// before anything else (`crate::proc_macro::trust_isolated_worker_entry`).
pub(crate) const WORKER_ARGUMENT: &str = "--trust-proc-macro-worker";

/// Expand one macro in its dylib's worker.
pub(crate) fn expand(
    ecx: &mut ExtCtxt<'_>,
    span: Span,
    client: IsolatedClient,
    shape: Shape,
    inputs: Vec<TokenStream>,
) -> Result<TokenStream, Failure> {
    match imp::expand(ecx, client, shape, inputs) {
        Ok(stream) => Ok(stream),
        Err(imp::Stop::Panicked(message)) => Err(Failure::Panicked(message)),
        Err(imp::Stop::Refused(reason)) => {
            Err(Failure::Refused(ecx.dcx().emit_err(diagnostics::IsolatedProcMacroRefused {
                span,
                crate_name: client.dylib.crate_name.clone(),
                dylib: client.dylib.path.display().to_string(),
                reason,
            })))
        }
    }
}

#[cfg(not(target_os = "macos"))]
mod imp {
    use super::*;

    pub(super) enum Stop {
        #[allow(dead_code)]
        Panicked(Option<String>),
        Refused(String),
    }

    /// The driver refuses the option on this host before a session exists
    /// (`rustc_session::trust_proc_macro_isolation_refusal_by_flags`); a driver
    /// that skipped that admission still cannot expand here.
    pub(super) fn expand(
        _: &mut ExtCtxt<'_>,
        _: IsolatedClient,
        _: Shape,
        _: Vec<TokenStream>,
    ) -> Result<TokenStream, Stop> {
        Err(Stop::Refused(
            "this host has no sandbox for the isolated proc-macro worker (it needs the macOS \
             seatbelt policy)"
                .to_owned(),
        ))
    }
}

#[cfg(target_os = "macos")]
pub(crate) use imp::register_worker_executable;

#[cfg(target_os = "macos")]
mod imp {
    use std::hash::Hash;
    use std::os::fd::OwnedFd;
    use std::os::unix::fs::DirBuilderExt;
    use std::os::unix::net::UnixStream;
    use std::path::Path;
    use std::process::{Child, Command, Stdio};
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{Duration, Instant};

    use rustc_data_structures::fingerprint::Fingerprint;
    use rustc_data_structures::stable_hash::StableHasher;
    use rustc_session::Session as CompilerSession;
    use trust_proc_macro_bridge::unix::UnixTransport;
    use trust_proc_macro_bridge::{Transport, parse_panic_reason};
    use trust_process_isolation::{
        Admission, Binding, Budget, Envelope, Error, Message, PROTOCOL_VERSION, Session, decode,
        encode,
    };

    use super::super::dispatch::Dispatcher;
    use super::*;
    use crate::proc_macro_server::Rustc;

    /// How long one expansion may take from `Begin` to `Finish`, nested
    /// expansions included. In-process expansion has no limit; this one exists
    /// so a worker that stops answering ends the compile instead of hanging it.
    const DEADLINE: Duration = Duration::from_secs(600);

    pub(super) enum Stop {
        Panicked(Option<String>),
        Refused(String),
    }

    impl From<Error> for Stop {
        fn from(error: Error) -> Self {
            Stop::Refused(error.to_string())
        }
    }

    /// The session's idle workers. Dropping the session ends them.
    #[derive(Default)]
    struct Pool {
        idle: Vec<Worker>,
    }

    struct Worker {
        dylib: &'static IsolatedDylib,
        executable: PathBuf,
        child: Child,
        /// `None` while an invocation holds it, and for good after a refusal.
        socket: Option<UnixStream>,
        private_tmp: PathBuf,
        /// The kernel has reported the sandbox on this process.
        sandbox_observed: bool,
    }

    impl Drop for Worker {
        fn drop(&mut self) {
            drop(self.socket.take());
            // The child is ours and nothing else waits on it.
            let _ = self.child.kill();
            let _ = self.child.wait();
            let _ = std::fs::remove_dir_all(&self.private_tmp);
        }
    }

    static CANONICAL_EXECUTABLE: OnceLock<PathBuf> = OnceLock::new();

    /// Called by the canonical compiler executable at entry: it is its own
    /// worker. A driver that never calls this (an embedded frontend) uses the
    /// compiler in its sysroot.
    pub(crate) fn register_worker_executable(executable: PathBuf) {
        let _ = CANONICAL_EXECUTABLE.set(executable);
    }

    fn worker_executable(sess: &CompilerSession) -> Result<PathBuf, String> {
        if let Some(executable) = CANONICAL_EXECUTABLE.get() {
            return Ok(executable.clone());
        }
        let bin = sess.opts.sysroot.path().join("bin");
        ["trustc", "rustc"]
            .iter()
            .map(|name| bin.join(name))
            .find(|path| path.is_file())
            .ok_or_else(|| {
                format!(
                    "no compiler executable can run the worker: this driver is not the \
                     compiler itself and `{}` has neither `trustc` nor `rustc`",
                    bin.display()
                )
            })
    }

    /// A new 0700 directory under the canonical temporary directory. `create`
    /// fails on an existing name, so no earlier entry can stand in for it.
    fn private_tmp() -> Result<PathBuf, String> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir();
        let root = root
            .canonicalize()
            .map_err(|e| format!("temporary directory `{}`: {e}", root.display()))?;
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |elapsed| elapsed.subsec_nanos());
        let path = root.join(format!(
            "trust-macro-worker-{}-{}-{stamp:08x}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&path)
            .map_err(|e| format!("private temporary directory `{}`: {e}", path.display()))?;
        Ok(path)
    }

    impl Worker {
        fn spawn(sess: &CompilerSession, dylib: &'static IsolatedDylib) -> Result<Self, String> {
            let executable = worker_executable(sess)?;
            let private_tmp = private_tmp()?;
            let spawned = (|| {
                let (ours, theirs) = UnixStream::pair().map_err(|e| format!("socket pair: {e}"))?;
                let child = Command::new(&executable)
                    .arg(WORKER_ARGUMENT)
                    .arg(&dylib.path)
                    .arg(&dylib.symbol)
                    .env("TMPDIR", &private_tmp)
                    .stdin(Stdio::from(OwnedFd::from(theirs)))
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .spawn()
                    .map_err(|e| format!("starting `{}`: {e}", executable.display()))?;
                Ok::<_, String>((ours, child))
            })();
            match spawned {
                Ok((socket, child)) => Ok(Worker {
                    dylib,
                    executable,
                    child,
                    socket: Some(socket),
                    private_tmp,
                    sandbox_observed: false,
                }),
                Err(error) => {
                    let _ = std::fs::remove_dir_all(&private_tmp);
                    Err(error)
                }
            }
        }

        /// What became of the process, for a refusal's text.
        fn fate(&mut self) -> String {
            match self.child.try_wait() {
                Ok(Some(status)) => format!("; the worker process ended ({status})"),
                _ => String::new(),
            }
        }
    }

    /// 32 bytes naming `parts` under `domain`. These bind one conversation to
    /// the compiler's own view of who it is talking to and about what; they are
    /// identities, not content digests, and the worker's echo of them proves
    /// nothing.
    fn identity(domain: &str, parts: &[&[u8]]) -> [u8; 32] {
        let mut result = [0; 32];
        for (half, chunk) in result.chunks_mut(16).enumerate() {
            let mut hasher = StableHasher::new();
            (domain, half, parts).hash(&mut hasher);
            let fingerprint: Fingerprint = hasher.finish();
            chunk.copy_from_slice(&fingerprint.to_le_bytes());
        }
        // B1 refuses an all-zero field; a hash that is zero is not an identity.
        if result == [0; 32] {
            result[0] = 1;
        }
        result
    }

    fn binding(ecx: &ExtCtxt<'_>, worker: &Worker, invocation: u64) -> Binding {
        let bytes = |path: &Path| path.as_os_str().as_encoded_bytes().to_vec();
        let dylib = bytes(&worker.dylib.path);
        let symbol = worker.dylib.symbol.as_bytes();
        let host = rustc_session::config::host_tuple().as_bytes();
        Binding {
            version: PROTOCOL_VERSION,
            invocation,
            compiler: identity("compiler", &[ecx.sess.cfg_version.as_bytes(), host]),
            worker: identity("worker", &[&bytes(&worker.executable)]),
            artifact: identity("artifact", &[&dylib]),
            metadata: identity("metadata", &[symbol]),
            unit: identity("unit", &[ecx.ecfg.crate_name.as_str().as_bytes()]),
            input_closure: identity("input", &[&dylib, symbol, &bytes(&worker.private_tmp)]),
            host_abi: identity("host-abi", &[host, &PROTOCOL_VERSION.to_le_bytes()]),
        }
    }

    pub(super) fn expand(
        ecx: &mut ExtCtxt<'_>,
        client: IsolatedClient,
        shape: Shape,
        inputs: Vec<TokenStream>,
    ) -> Result<TokenStream, Stop> {
        static INVOCATION: AtomicU64 = AtomicU64::new(1);
        let sess = ecx.sess;
        let idle = sess.with_trust_compiler_state::<Pool, _>(|pool| {
            let index = pool.idle.iter().position(|w| std::ptr::eq(w.dylib, client.dylib))?;
            Some(pool.idle.swap_remove(index))
        });
        let mut worker = match idle {
            Some(worker) => worker,
            None => Worker::spawn(sess, client.dylib).map_err(Stop::Refused)?,
        };
        let invocation = INVOCATION.fetch_add(1, Ordering::Relaxed);
        let binding = binding(ecx, &worker, invocation);
        let result = converse(ecx, &mut worker, binding, client.declaration, shape, inputs);
        match result {
            // A panic is the macro's result and leaves the conversation whole.
            Ok(_) | Err(Stop::Panicked(_)) if worker.socket.is_some() => {
                sess.with_trust_compiler_state::<Pool, _>(|pool| pool.idle.push(worker));
                result
            }
            Err(Stop::Refused(reason)) => Err(Stop::Refused(format!("{reason}{}", worker.fate()))),
            // The socket did not come back: whatever the worker last said, it
            // is not in a state to be believed.
            Ok(_) | Err(Stop::Panicked(_)) => Err(Stop::Refused(format!(
                "the worker's connection closed before its result was complete{}",
                worker.fate()
            ))),
        }
        // A worker not returned to the pool is dropped here: killed, reaped,
        // and its private directory removed.
    }

    fn converse(
        ecx: &mut ExtCtxt<'_>,
        worker: &mut Worker,
        binding: Binding,
        declaration: u32,
        shape: Shape,
        inputs: Vec<TokenStream>,
    ) -> Result<TokenStream, Stop> {
        let socket = worker.socket.take().ok_or(Error::Phase)?;
        let budget = Budget::new(LIMITS, Instant::now() + DEADLINE)?;
        let mut session = Session::new(binding, budget.clone())?;
        let mut dispatcher = Dispatcher::new(Rustc::new(ecx), &session)?;
        let mut handles = Vec::with_capacity(inputs.len());
        for input in inputs {
            handles.push(dispatcher.store_input(input)?);
        }
        let mut transport = UnixTransport::new(socket, budget.clone())?;
        let begin = Envelope {
            binding: session.binding().clone(),
            message: Message::Begin {
                declaration,
                kind: shape as u8,
                inputs: handles,
                globals: dispatcher.globals(),
            },
        };
        transport.send(&encode(&begin, &budget)?, &budget)?;
        let result = loop {
            let Some(frame) = transport.receive_frame(&budget)? else {
                return Err(Stop::Refused(
                    "the worker closed its connection in the middle of an expansion".to_owned(),
                ));
            };
            match session.receive(decode(&frame, &budget)?)? {
                Admission::Ready => {
                    // The worker's word is not evidence. Ask the kernel whether
                    // that process is restricted before serving it one call.
                    if !worker.sandbox_observed {
                        match trust_exec_policy::fork_denied(worker.child.id()) {
                            Ok(true) => worker.sandbox_observed = true,
                            Ok(false) => {
                                return Err(Stop::Refused(
                                    "the worker reported ready but the kernel reports no \
                                     sandbox on it"
                                        .to_owned(),
                                ));
                            }
                            Err(error) => {
                                return Err(Stop::Refused(format!(
                                    "the worker's sandbox could not be observed: {error}"
                                )));
                            }
                        }
                    }
                }
                Admission::Call(call) => {
                    let id = call.id;
                    let value = dispatcher.dispatch(&mut session, call)?;
                    let reply = session.reply(id, value)?;
                    transport.send(&encode(&reply, &budget)?, &budget)?;
                }
                Admission::Finished(output) => break Ok(dispatcher.output(output)?),
                Admission::Failed(reason) => match parse_panic_reason(&reason) {
                    Some(message) => break Err(Stop::Panicked(message.map(str::to_owned))),
                    None => return Err(Stop::Refused(reason)),
                },
            }
        };
        dispatcher.finish();
        budget.check()?;
        // Bytes the worker sends after this belong to no invocation; the next
        // one's first frame would fail its binding check.
        worker.socket = transport.into_stream();
        result
    }
}
