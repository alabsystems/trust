//! Trust (D21): the worker role of the compiler executable.
//!
//! `trustc --trust-proc-macro-worker <dylib> <symbol>` is started only by
//! `launch.rs`, with one end of an unnamed socket pair as standard input,
//! `/dev/null` as standard output and error, and `TMPDIR` naming a private 0700
//! directory. Before any macro code can run, this role
//!
//! 1. closes every descriptor above the three standard ones, so the macro holds
//!    nothing the compiler's parent passed down (a jobserver pipe, a lock file);
//! 2. installs the fixed deny-default policy
//!    (`trust_exec_policy::restrict_current_to_macro_worker`);
//! 3. opens the dylib, whose load-time initializers therefore run restricted.
//!
//! It then serves expansions for that dylib until the compiler closes the
//! socket. It never prints: the socket is its only way to say anything, and the
//! compiler checks every frame.
//!
//! This role is trusted only up to step 3. From then on the process contains
//! macro code and the compiler believes nothing it says without checking.

use std::process::ExitCode;

/// Exit status when the role's arguments or descriptors are not the ones
/// `launch.rs` supplies. Nothing was loaded.
const USAGE: u8 = 64;
/// Exit status when a conversation ended in a refusal. The compiler has the
/// reason, or will find the socket closed.
const REFUSED: u8 = 1;

#[cfg(not(target_os = "macos"))]
pub(crate) fn main(_: Vec<std::ffi::OsString>) -> ExitCode {
    let _ = REFUSED;
    ExitCode::from(USAGE)
}

#[cfg(target_os = "macos")]
pub(crate) use imp::main;

#[cfg(target_os = "macos")]
mod imp {
    use std::cell::RefCell;
    use std::ffi::{CStr, CString, OsString};
    use std::os::fd::AsFd;
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::net::UnixStream;
    use std::path::{Path, PathBuf};
    use std::rc::Rc;
    use std::time::{Duration, Instant};

    use rustc_proc_macro::bridge::client::Client;
    use trust_proc_macro_bridge::unix::UnixTransport;
    use trust_proc_macro_bridge::{Transport, Worker};
    use trust_process_isolation::{Budget, Envelope, Error, Message, decode, encode};

    use super::super::launch::LIMITS;
    use super::*;

    /// The compiler holds the real deadline and kills this process when it
    /// passes. This one only has to be far enough away never to fire first.
    const NEVER: Duration = Duration::from_secs(60 * 60 * 24 * 365);

    pub(crate) fn main(arguments: Vec<OsString>) -> ExitCode {
        let [dylib, symbol] = arguments.as_slice() else {
            return ExitCode::from(USAGE);
        };
        close_inherited_descriptors();
        // Standard input is the socket. A duplicate gives one Rust owner; the
        // original stays open so descriptor 0 is never reused for a file.
        let Ok(socket) = std::io::stdin().as_fd().try_clone_to_owned() else {
            return ExitCode::from(USAGE);
        };
        let socket = UnixStream::from(socket);
        if socket.peer_addr().is_err() {
            return ExitCode::from(USAGE);
        }
        let prepared = prepare(Path::new(dylib), symbol);
        serve(socket, prepared)
    }

    /// Steps 2 and 3. An error is reported to the compiler in answer to its
    /// first `Begin`; after a failed restriction nothing is loaded.
    fn prepare(dylib: &Path, symbol: &OsString) -> Result<&'static [Client], String> {
        let private_tmp = std::env::var_os("TMPDIR")
            .map(PathBuf::from)
            .ok_or("the worker was started without its private TMPDIR")?;
        trust_exec_policy::restrict_current_to_macro_worker(&private_tmp).map_err(|error| {
            format!(
                "this host refused the proc-macro sandbox ({error}); a process that is \
                 already sandboxed cannot install one"
            )
        })?;
        let path = CString::new(dylib.as_os_str().as_bytes())
            .map_err(|_| "the dylib path contains NUL".to_owned())?;
        let symbol = CString::new(symbol.as_bytes())
            .map_err(|_| "the declarations symbol contains NUL".to_owned())?;
        // SAFETY: this is the restricted worker process, never the compiler.
        // `path` and `symbol` are live NUL-terminated strings. The dylib was
        // built by this compiler as a proc-macro crate, whose declarations
        // symbol is a `&'static [Client]` in this compiler's `proc_macro` ABI
        // (as `rustc_metadata::host_dylib::dlsym_proc_macros` reads it in
        // process). The handle is never closed, so the clients' function
        // pointers stay valid until the process exits.
        unsafe {
            let library = libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
            if library.is_null() {
                return Err(format!("the dylib did not load: {}", last_loader_error()));
            }
            let pointer = libc::dlsym(library, symbol.as_ptr());
            if pointer.is_null() {
                return Err(format!(
                    "the dylib has no declarations symbol `{}`: it is not the build of the \
                     crate this compiler read the metadata of",
                    symbol.to_string_lossy()
                ));
            }
            Ok(*pointer.cast::<&'static [Client]>())
        }
    }

    /// # Safety
    /// Call only directly after a failed `dlopen` on this thread.
    unsafe fn last_loader_error() -> String {
        // SAFETY: `dlerror` returns null or a NUL-terminated string valid until
        // the next loader call on this thread; it is copied before returning.
        unsafe {
            let error = libc::dlerror();
            if error.is_null() {
                "unknown loader error".to_owned()
            } else {
                CStr::from_ptr(error).to_string_lossy().into_owned()
            }
        }
    }

    /// Close everything above standard error. The descriptor table is read
    /// from `/dev/fd` first and the directory handle released, so no close
    /// here races the listing itself. No other thread exists yet.
    fn close_inherited_descriptors() {
        let open: Vec<libc::c_int> = match std::fs::read_dir("/dev/fd") {
            Ok(entries) => {
                entries.filter_map(|entry| entry.ok()?.file_name().to_str()?.parse().ok()).collect()
            }
            // Without the listing, sweep the whole table.
            // SAFETY: a query of this process's descriptor table size.
            Err(_) => (0..unsafe { libc::getdtablesize() }).collect(),
        };
        for descriptor in open {
            if descriptor > libc::STDERR_FILENO {
                // SAFETY: this role owns no descriptor above standard error
                // yet (the listing's own was released above), so closing each
                // one drops only what the process inherited. A number that is
                // no longer open fails with EBADF and changes nothing.
                unsafe { libc::close(descriptor) };
            }
        }
    }

    /// Block until the compiler sends something or closes the socket. An idle
    /// worker sleeps here, not in the transport's deadline-sliced wait.
    fn await_compiler(socket: &UnixStream) {
        use std::os::fd::AsRawFd;
        let mut descriptor =
            libc::pollfd { fd: socket.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        loop {
            // SAFETY: one initialized pollfd for the borrowed live socket.
            let ready = unsafe { libc::poll(&mut descriptor, 1, -1) };
            if ready >= 0
                || std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted
            {
                return;
            }
        }
    }

    /// One invocation's use of the socket. The bridge closes its transport when
    /// an invocation ends; here that hands the socket back for the next one,
    /// unless the transport itself refused, which ends the connection.
    struct Lent {
        transport: Option<UnixTransport>,
        returned: Rc<RefCell<Option<UnixStream>>>,
    }

    impl Transport for Lent {
        fn send(&mut self, frame: &[u8], budget: &Budget) -> Result<(), Error> {
            self.transport.as_mut().ok_or(Error::Phase)?.send(frame, budget)
        }
        fn receive(&mut self, budget: &Budget) -> Result<Vec<u8>, Error> {
            self.transport.as_mut().ok_or(Error::Phase)?.receive(budget)
        }
        fn close(&mut self) {
            if let Some(transport) = self.transport.take() {
                *self.returned.borrow_mut() = transport.into_stream();
            }
        }
    }

    fn serve(mut socket: UnixStream, prepared: Result<&'static [Client], String>) -> ExitCode {
        loop {
            await_compiler(&socket);
            let Ok(budget) = Budget::new(LIMITS, Instant::now() + NEVER) else {
                return ExitCode::from(REFUSED);
            };
            let Ok(mut transport) = UnixTransport::new(socket, budget.clone()) else {
                return ExitCode::from(REFUSED);
            };
            let frame = match transport.receive_frame(&budget) {
                Ok(Some(frame)) => frame,
                // The compiler is done with this dylib.
                Ok(None) => return ExitCode::SUCCESS,
                Err(_) => return ExitCode::from(REFUSED),
            };
            let Ok(begin) = decode(&frame, &budget) else {
                return ExitCode::from(REFUSED);
            };
            let answer =
                |message| encode(&Envelope { binding: begin.binding.clone(), message }, &budget);
            let declarations = match &prepared {
                Ok(declarations) => *declarations,
                Err(reason) => {
                    if let Ok(frame) = answer(Message::Failure { reason: reason.clone() }) {
                        let _ = transport.send(&frame, &budget);
                    }
                    return ExitCode::from(REFUSED);
                }
            };
            // Ready says only that steps 1 to 3 are done in this process. The
            // compiler asks the kernel about the sandbox itself.
            let ready = answer(Message::Ready).and_then(|frame| transport.send(&frame, &budget));
            if ready.is_err() {
                return ExitCode::from(REFUSED);
            }
            let returned = Rc::new(RefCell::new(None));
            let lent = Lent { transport: Some(transport), returned: returned.clone() };
            let completed = Worker::from_begin(begin, budget, lent)
                .and_then(|mut worker| worker.run_reported(declarations, false));
            // Finished or panicked, the conversation is whole and the next
            // `Begin` is served by the same loaded dylib. A refusal is not.
            if completed.is_err() {
                return ExitCode::from(REFUSED);
            }
            socket = match returned.borrow_mut().take() {
                Some(socket) => socket,
                None => return ExitCode::from(REFUSED),
            };
        }
    }
}
