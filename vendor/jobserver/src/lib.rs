//! An implementation of the GNU make jobserver.
//!
//! This crate is an implementation, in Rust, of the GNU `make` jobserver for
//! CLI tools that are interoperating with make or otherwise require some form
//! of parallelism limiting across process boundaries. This was originally
//! written for usage in Cargo to both (a) work when `cargo` is invoked from
//! `make` (using `make`'s jobserver) and (b) work when `cargo` invokes build
//! scripts, exporting a jobserver implementation for `make` processes to
//! transitively use.
//!
//! The jobserver implementation can be found in [detail online][docs] but
//! basically boils down to a cross-process semaphore. On Unix this is
//! implemented with the `pipe` syscall and read/write ends of a pipe and on
//! Windows this is implemented literally with IPC semaphores. Starting from
//! GNU `make` version 4.4, named pipe becomes the default way in communication
//! on Unix. This crate also supports that feature in the sense of inheriting
//! and forwarding the correct environment.
//!
//! The jobserver protocol in `make` also dictates when tokens are acquired to
//! run child work, and clients using this crate should take care to implement
//! such details to ensure correct interoperation with `make` itself.
//!
//! ## Examples
//!
//! Connect to a jobserver that was set up by `make` or a different process:
//!
//! ```no_run
//! use jobserver::Client;
//!
//! // See API documentation for why this is `unsafe`
//! let client = match unsafe { Client::from_env() } {
//!     Some(client) => client,
//!     None => panic!("client not configured"),
//! };
//! ```
//!
//! Acquire and release token from a jobserver:
//!
//! ```no_run
//! use jobserver::Client;
//!
//! let client = unsafe { Client::from_env().unwrap() };
//! let token = client.acquire().unwrap(); // blocks until it is available
//! drop(token); // releases the token when the work is done
//! ```
//!
//! Create a new jobserver and configure a child process to have access:
//!
//! ```
//! use std::process::Command;
//! use jobserver::Client;
//!
//! let client = Client::new(4).expect("failed to create jobserver");
//! let mut cmd = Command::new("make");
//! client.configure(&mut cmd);
//! ```
//!
//! ## Caveats
//!
//! This crate makes no attempt to release tokens back to a jobserver on
//! abnormal exit of a process. If a process which acquires a token is killed
//! with ctrl-c or some similar signal then tokens will not be released and the
//! jobserver may be in a corrupt state.
//!
//! Note that this is typically ok as ctrl-c means that an entire build process
//! is being torn down, but it's worth being aware of at least!
//!
//! ## Windows caveats
//!
//! There appear to be two implementations of `make` on Windows. On MSYS2 one
//! typically comes as `mingw32-make` and the other as `make` itself. I'm not
//! personally too familiar with what's going on here, but for jobserver-related
//! information the `mingw32-make` implementation uses Windows semaphores
//! whereas the `make` program does not. The `make` program appears to use file
//! descriptors and I'm not really sure how it works, so this crate is not
//! compatible with `make` on Windows. It is, however, compatible with
//! `mingw32-make`.
//!
//! [docs]: https://make.mad-scientist.net/papers/jobserver-implementation/

#![deny(missing_docs, missing_debug_implementations)]
#![doc(html_root_url = "https://docs.rs/jobserver/0.1")]

use std::env;
use std::ffi::OsString;
use std::io;
use std::process::Command;
use std::sync::{Arc, Condvar, Mutex, MutexGuard};

mod error;
#[cfg(unix)]
#[path = "unix.rs"]
mod imp;
#[cfg(windows)]
#[path = "windows.rs"]
mod imp;
#[cfg(not(any(unix, windows)))]
#[path = "wasm.rs"]
mod imp;

/// A client of a jobserver
///
/// This structure is the main type exposed by this library, and is where
/// interaction to a jobserver is configured through. Clients are either created
/// from scratch in which case the internal semphore is initialied on the spot,
/// or a client is created from the environment to connect to a jobserver
/// already created.
///
/// Some usage examples can be found in the crate documentation for using a
/// client.
///
/// Note that a [`Client`] implements the [`Clone`] trait, and all instances of
/// a [`Client`] refer to the same jobserver instance.
#[derive(Clone, Debug)]
pub struct Client {
    inner: Arc<imp::Client>,
}

/// Existing scheduling descriptions for an authenticated child handoff.
/// Cloning them neither acquires nor creates scheduling tokens.
#[cfg(unix)]
#[derive(Debug)]
pub enum TransportWitnesses {
    /// Anonymous read/write pipe descriptions.
    NumericPipe {
        /// Existing read description, cloned close-on-exec.
        read: std::os::fd::OwnedFd,
        /// Existing write description, cloned close-on-exec.
        write: std::os::fd::OwnedFd,
    },
    /// Named FIFO and the actual retained descriptions for its original node.
    NamedFifo {
        /// Original GNU locator, never an independently authenticated grant.
        path: std::path::PathBuf,
        /// Existing read witness, cloned close-on-exec.
        read: std::os::fd::OwnedFd,
        /// Existing write witness, cloned close-on-exec.
        write: std::os::fd::OwnedFd,
    },
}

/// An acquired token from a jobserver.
///
/// This token will be released back to the jobserver when it is dropped and
/// otherwise represents the ability to spawn off another thread of work.
#[derive(Debug)]
pub struct Acquired {
    client: Arc<imp::Client>,
    data: imp::Acquired,
    disabled: bool,
}

impl Acquired {
    /// Whether this acquired credit belongs to this same original client.
    ///
    /// Clones of the originating [`Client`] match. Reopening or importing the
    /// same transport does not reconstruct this identity. This observation
    /// neither acquires nor transfers a credit or any execution authority.
    pub fn belongs_to(&self, client: &Client) -> bool {
        Arc::ptr_eq(&self.client, &client.inner)
    }

    /// Trust: explicitly return this same original credit and report an I/O
    /// failure. Success consumes the guard; failure returns the SAME still-armed
    /// guard with its error. There is no released guard to reuse as authority.
    /// Like ordinary Drop, a blocking original transport may block.
    pub fn return_to_server(mut self) -> Result<(), (Self, io::Error)> {
        match self.client.release(Some(&self.data)) {
            Ok(()) => {
                self.disabled = true;
                Ok(())
            }
            Err(error) => Err((self, error)),
        }
    }

    /// This drops the [`Acquired`] token without releasing the associated token.
    ///
    /// This is not generally useful, but can be helpful if you do not have the
    /// ability to store an Acquired token but need to not yet release it.
    ///
    /// You'll typically want to follow this up with a call to
    /// [`Client::release_raw`] or similar to actually release the token later on.
    pub fn drop_without_releasing(mut self) {
        self.disabled = true;
    }
}

#[derive(Default, Debug)]
struct HelperState {
    lock: Mutex<HelperInner>,
    cvar: Condvar,
}

#[derive(Default, Debug)]
struct HelperInner {
    requests: usize,
    producer_done: bool,
    consumer_done: bool,
}

use error::FromEnvErrorInner;
pub use error::{FromEnvError, FromEnvErrorKind};

/// Return type for [`Client::from_env_ext`] function.
#[derive(Debug)]
pub struct FromEnv {
    /// Result of trying to get jobserver client from env.
    pub client: Result<Client, FromEnvError>,
    /// Name and value of the environment variable.
    /// `None` if no relevant environment variable is found.
    pub var: Option<(&'static str, OsString)>,
}

impl FromEnv {
    fn new_ok(client: Client, var_name: &'static str, var_value: OsString) -> FromEnv {
        FromEnv {
            client: Ok(client),
            var: Some((var_name, var_value)),
        }
    }
    fn new_err(kind: FromEnvErrorInner, var_name: &'static str, var_value: OsString) -> FromEnv {
        FromEnv {
            client: Err(FromEnvError { inner: kind }),
            var: Some((var_name, var_value)),
        }
    }
}

impl Client {
    /// Whether these clients retain the same original imported client.
    ///
    /// Clones match. Independently importing even the same kernel pipe does
    /// not establish this ownership identity or create scheduling credit.
    pub fn same_origin(&self, other: &Client) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    /// Trust: open an existing named FIFO without importing environment state
    /// or creating scheduling tokens.
    ///
    /// The independently opened read and write descriptions are nonblocking,
    /// so [`Client::try_acquire`] and [`Client::release_raw`] cannot wait for
    /// FIFO capacity. A full FIFO makes `release_raw` return `WouldBlock`.
    /// [`Client::acquire`] retains its blocking contract by polling readiness.
    /// Ordinary acquired guards may wait for writable capacity when returning
    /// a token. Bounded owner steps reclaim with [`Acquired::drop_without_releasing`]
    /// and issue with `release_raw` instead of relying on a guard's destructor.
    /// Other clients' descriptor flags are not changed.
    ///
    /// The path must be absolute, UTF-8 and contain no whitespace, so GNU
    /// jobserver metadata names exactly this path. It must name a FIFO rather
    /// than a symlink, and both opened descriptions must name the same node.
    /// The caller owns the namespace and must keep the path bound to that FIFO
    /// while configured descendants can open it. This authenticates no caller
    /// or CPU grant and does not create or unlink the FIFO.
    ///
    /// # Errors
    ///
    /// Rejects an unadvertisable path, a non-FIFO or symlink, a node replaced
    /// between opens, or an operating-system I/O failure.
    #[cfg(unix)]
    pub fn from_fifo(path: &std::path::Path) -> io::Result<Client> {
        Ok(Client {
            inner: Arc::new(imp::Client::open_fifo(path)?),
        })
    }

    /// Open a named FIFO and compare the actual opened node with retained
    /// descriptor witnesses before exposing any scheduling operation. No tokens
    /// are minted and the named transport is preserved for descendants.
    #[cfg(unix)]
    pub fn from_fifo_with_witnesses(
        path: &std::path::Path,
        read: std::os::fd::BorrowedFd<'_>,
        write: std::os::fd::BorrowedFd<'_>,
    ) -> io::Result<Client> {
        Ok(Client {
            inner: Arc::new(imp::Client::open_fifo_with_witnesses(path, read, write)?),
        })
    }

    /// Clone this client's actual transport, preserving named/numeric kind.
    /// These are existing descriptions, not additional scheduling credits.
    #[cfg(unix)]
    pub fn transport_witnesses(&self) -> io::Result<TransportWitnesses> {
        self.inner.transport_witnesses()
    }

    /// Trust: import an already owned, checked scheduling pipe without reading
    /// or changing this process's environment or acquiring any tokens.
    ///
    /// Both descriptors are borrowed for the call and cloned into the client.
    /// They must name the ordered read/write endpoints of the intended pool;
    /// this constructor checks their file types and access directions, while
    /// the caller authenticates which scheduling pool those endpoints name.
    #[cfg(unix)]
    pub fn from_pipe(
        read: std::os::unix::io::BorrowedFd<'_>,
        write: std::os::unix::io::BorrowedFd<'_>,
    ) -> io::Result<Client> {
        use std::os::unix::io::AsRawFd;

        for (fd, reading) in [(read.as_raw_fd(), true), (write.as_raw_fd(), false)] {
            // SAFETY: BorrowedFd keeps each descriptor live throughout this
            // call. These queries neither close descriptors nor read tokens.
            let mode = unsafe { libc::fcntl(fd, libc::F_GETFL) };
            if mode < 0 {
                return Err(io::Error::last_os_error());
            }
            let access = mode & libc::O_ACCMODE;
            if (reading && access == libc::O_WRONLY) || (!reading && access == libc::O_RDONLY) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "jobserver requires ordered readable/writable pipe endpoints",
                ));
            }
        }
        let auth = format!("{},{}", read.as_raw_fd(), write.as_raw_fd());
        // SAFETY: both numbers remain borrowed and live. The existing checked
        // Unix import validates pipe types and owns CLOEXEC copies, never the
        // borrowed descriptors. It preserves the original pipe's token bytes.
        let inner = unsafe { imp::Client::open(&auth, true) }
            .map_err(|inner| io::Error::new(io::ErrorKind::InvalidInput, FromEnvError { inner }))?;
        Ok(Client {
            inner: Arc::new(inner),
        })
    }

    /// Creates a new jobserver initialized with the given parallelism limit.
    ///
    /// A client to the jobserver created will be returned. This client will
    /// allow at most `limit` tokens to be acquired from it in parallel. More
    /// calls to [`Client::acquire`] will cause the calling thread to block.
    ///
    /// Note that the created [`Client`] is not automatically inherited into
    /// spawned child processes from this program. Manual usage of the
    /// [`Client::configure`] function is required for a child process to have
    /// access to a job server.
    ///
    /// # Examples
    ///
    /// ```
    /// use jobserver::Client;
    ///
    /// let client = Client::new(4).expect("failed to create jobserver");
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if any I/O error happens when attempting to create the
    /// jobserver client.
    pub fn new(limit: usize) -> io::Result<Client> {
        Ok(Client {
            inner: Arc::new(imp::Client::new(limit)?),
        })
    }

    /// Attempts to connect to the jobserver specified in this process's
    /// environment.
    ///
    /// When the a `make` executable calls a child process it will configure the
    /// environment of the child to ensure that it has handles to the jobserver
    /// it's passing down. This function will attempt to look for these details
    /// and connect to the jobserver.
    ///
    /// Note that the created [`Client`] is not automatically inherited into
    /// spawned child processes from this program. Manual usage of the
    /// [`Client::configure`] function is required for a child process to have
    /// access to a job server.
    ///
    /// # Return value
    ///
    /// [`FromEnv`] contains result and relevant environment variable.
    /// If a jobserver was found in the environment and it looks correct then
    /// result with the connected client will be returned. In other cases
    /// result will contain `Err(FromEnvErr)`.
    ///
    /// Additionally on Unix this function will configure the file descriptors
    /// with `CLOEXEC` so they're not automatically inherited by spawned
    /// children.
    ///
    /// On unix if `check_pipe` enabled this function will check if provided
    /// files are actually pipes.
    ///
    /// # Safety
    ///
    /// This function is `unsafe` to call on Unix specifically as it
    /// transitively requires usage of the `from_raw_fd` function, which is
    /// itself unsafe in some circumstances.
    ///
    /// It's recommended to call this function very early in the lifetime of a
    /// program before any other file descriptors are opened. That way you can
    /// make sure to take ownership properly of the file descriptors passed
    /// down, if any.
    ///
    /// It is ok to call this function any number of times.
    pub unsafe fn from_env_ext(check_pipe: bool) -> FromEnv {
        let (env, var_os) = match ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"]
            .iter()
            .map(|&env| env::var_os(env).map(|var| (env, var)))
            .find_map(|p| p)
        {
            Some((env, var_os)) => (env, var_os),
            None => return FromEnv::new_err(FromEnvErrorInner::NoEnvVar, "", Default::default()),
        };

        let var = match var_os.to_str() {
            Some(var) => var,
            None => {
                let err = FromEnvErrorInner::CannotParse("not valid UTF-8".to_string());
                return FromEnv::new_err(err, env, var_os);
            }
        };

        let s = match find_jobserver_auth(var) {
            Some(s) => s,
            None => return FromEnv::new_err(FromEnvErrorInner::NoJobserver, env, var_os),
        };
        match imp::Client::open(s, check_pipe) {
            Ok(c) => FromEnv::new_ok(Client { inner: Arc::new(c) }, env, var_os),
            Err(err) => FromEnv::new_err(err, env, var_os),
        }
    }

    /// Read the selected named FIFO locator without opening any descriptor.
    /// This uses the same environment precedence and authentication parser as
    /// `from_env_ext`, allowing an owner to authenticate retained witnesses
    /// before opening an otherwise untrusted pathname.
    #[cfg(unix)]
    pub fn fifo_path_from_env() -> io::Result<Option<std::path::PathBuf>> {
        let Some(value) = ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"]
            .iter()
            .find_map(|name| env::var_os(name))
        else {
            return Ok(None);
        };
        let value = value.to_str().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "jobserver flags are not UTF-8")
        })?;
        Ok(find_jobserver_auth(value)
            .and_then(|auth| auth.strip_prefix("fifo:"))
            .map(std::path::PathBuf::from))
    }

    /// Attempts to connect to the jobserver specified in this process's
    /// environment.
    ///
    /// Wraps [`Client::from_env_ext`] and discards error details.
    ///
    /// # Safety
    ///
    /// This function is `unsafe` to call on Unix specifically as it
    /// transitively requires usage of the `from_raw_fd` function, which is
    /// itself unsafe in some circumstances.
    ///
    /// It's recommended to call this function very early in the lifetime of a
    /// program before any other file descriptors are opened. That way you can
    /// make sure to take ownership properly of the file descriptors passed
    /// down, if any.
    ///
    /// It is ok to call this function any number of times.
    pub unsafe fn from_env() -> Option<Client> {
        Self::from_env_ext(false).client.ok()
    }

    /// Acquires a token from this jobserver client.
    ///
    /// This function will block the calling thread until a new token can be
    /// acquired from the jobserver.
    ///
    /// # Return value
    ///
    /// On successful acquisition of a token an instance of [`Acquired`] is
    /// returned. This structure, when dropped, will release the token back to
    /// the jobserver. It's recommended to avoid leaking this value.
    ///
    /// # Errors
    ///
    /// If an I/O error happens while acquiring a token then this function will
    /// return immediately with the error. If an error is returned then a token
    /// was not acquired.
    pub fn acquire(&self) -> io::Result<Acquired> {
        let data = self.inner.acquire()?;
        Ok(Acquired {
            client: self.inner.clone(),
            data,
            disabled: false,
        })
    }

    /// Acquires a token from this jobserver client in a non-blocking way.
    ///
    /// # Return value
    ///
    /// On successful acquisition of a token an instance of [`Acquired`] is
    /// returned. This structure, when dropped, will release the token back to
    /// the jobserver. It's recommended to avoid leaking this value.
    ///
    /// # Errors
    ///
    /// If an I/O error happens while acquiring a token then this function will
    /// return immediately with the error. If an error is returned then a token
    /// was not acquired.
    ///
    /// If non-blocking acquire is not supported, the return error will have its `kind()`
    /// set to [`io::ErrorKind::Unsupported`].
    pub fn try_acquire(&self) -> io::Result<Option<Acquired>> {
        let ret = self.inner.try_acquire()?;

        Ok(ret.map(|data| Acquired {
            client: self.inner.clone(),
            data,
            disabled: false,
        }))
    }

    /// Returns amount of tokens in the read-side pipe.
    ///
    /// # Return value
    ///
    /// Number of bytes available to be read from the jobserver pipe
    ///
    /// # Errors
    ///
    /// Underlying errors from the ioctl will be passed up.
    pub fn available(&self) -> io::Result<usize> {
        self.inner.available()
    }

    /// Configures a child process to have access to this client's jobserver as
    /// well.
    ///
    /// This function is required to be called to ensure that a jobserver is
    /// properly inherited to a child process. If this function is *not* called
    /// then this [`Client`] will not be accessible in the child process. In
    /// other words, if not called, then [`Client::from_env`] will return `None`
    /// in the child process (or the equivalent of [`Client::from_env`] that
    /// `make` uses).
    ///
    /// ## Platform-specific behavior
    ///
    /// On Unix and Windows this will clobber the `CARGO_MAKEFLAGS` environment
    /// variables for the child process, and on Unix this will also allow the
    /// two file descriptors for this client to be inherited to the child.
    ///
    /// On platforms other than Unix and Windows this panics.
    pub fn configure(&self, cmd: &mut Command) {
        cmd.env("CARGO_MAKEFLAGS", &self.mflags_env());
        self.inner.configure(cmd);
    }

    /// Configures a child process to have access to this client's jobserver as
    /// well.
    ///
    /// This function is required to be called to ensure that a jobserver is
    /// properly inherited to a child process. If this function is *not* called
    /// then this [`Client`] will not be accessible in the child process. In
    /// other words, if not called, then [`Client::from_env`] will return `None`
    /// in the child process (or the equivalent of [`Client::from_env`] that
    /// `make` uses).
    ///
    /// ## Platform-specific behavior
    ///
    /// On Unix and Windows this will clobber the `CARGO_MAKEFLAGS`,
    /// `MAKEFLAGS` and `MFLAGS` environment variables for the child process,
    /// and on Unix this will also allow the two file descriptors for
    /// this client to be inherited to the child.
    ///
    /// On platforms other than Unix and Windows this panics.
    pub fn configure_make(&self, cmd: &mut Command) {
        let value = self.mflags_env();
        cmd.env("CARGO_MAKEFLAGS", &value);
        cmd.env("MAKEFLAGS", &value);
        cmd.env("MFLAGS", &value);
        self.inner.configure(cmd);
    }

    fn mflags_env(&self) -> String {
        let arg = self.inner.string_arg();
        // Older implementations of make use `--jobserver-fds` and newer
        // implementations use `--jobserver-auth`, pass both to try to catch
        // both implementations.
        format!("-j --jobserver-fds={0} --jobserver-auth={0}", arg)
    }

    /// Converts this [`Client`] into a helper thread to deal with a blocking
    /// [`Client::acquire`] function a little more easily.
    ///
    /// The fact that the [`Client::acquire`] isn't always the easiest to work
    /// with. Typically you're using a jobserver to manage running other events
    /// in parallel! This means that you need to either (a) wait for an existing
    /// job to finish or (b) wait for a new token to become available.
    ///
    /// Unfortunately the blocking in [`Client::acquire`] happens at the
    /// implementation layer of jobservers. On Unix this requires a blocking
    /// call to `read` and on Windows this requires one of the `WaitFor*`
    /// functions. Both of these situations aren't the easiest to deal with:
    ///
    /// * On Unix there's basically only one way to wake up a `read` early, and
    ///   that's through a signal. This is what the `make` implementation
    ///   itself uses, relying on `SIGCHLD` to wake up a blocking acquisition
    ///   of a new job token. Unfortunately nonblocking I/O is not an option
    ///   here, so it means that "waiting for one of two events" means that
    ///   the latter event must generate a signal! This is not always the case
    ///   on unix for all jobservers.
    ///
    /// * On Windows you'd have to basically use the `WaitForMultipleObjects`
    ///   which means that you've got to canonicalize all your event sources
    ///   into a `HANDLE` which also isn't the easiest thing to do
    ///   unfortunately.
    ///
    /// This function essentially attempts to ease these limitations by
    /// converting this [`Client`] into a helper thread spawned into this
    /// process. The application can then request that the helper thread
    /// acquires tokens and the provided closure will be invoked for each token
    /// acquired.
    ///
    /// The intention is that this function can be used to translate the event
    /// of a token acquisition into an arbitrary user-defined event.
    ///
    /// # Arguments
    ///
    /// This function will consume the [`Client`] provided to be transferred to
    /// the helper thread that is spawned. Additionally a closure `f` is
    /// provided to be invoked whenever a token is acquired.
    ///
    /// This closure is only invoked after calls to
    /// [`HelperThread::request_token`] have been made and a token itself has
    /// been acquired. If an error happens while acquiring the token then
    /// an error will be yielded to the closure as well.
    ///
    /// # Return Value
    ///
    /// This function will return an instance of the [`HelperThread`] structure
    /// which is used to manage the helper thread associated with this client.
    /// Through the [`HelperThread`] you'll request that tokens are acquired.
    /// When acquired, the closure provided here is invoked.
    ///
    /// When the [`HelperThread`] structure is returned it will be gracefully
    /// torn down, and the calling thread will be blocked until the thread is
    /// torn down (which should be prompt).
    ///
    /// # Errors
    ///
    /// This function may fail due to creation of the helper thread or
    /// auxiliary I/O objects to manage the helper thread. In any of these
    /// situations the error is propagated upwards.
    ///
    /// # Platform-specific behavior
    ///
    /// On Windows this function behaves pretty normally as expected, but on
    /// Unix the implementation is... a little heinous. As mentioned above
    /// we're forced into blocking I/O for token acquisition, namely a blocking
    /// call to `read`. We must be able to unblock this, however, to tear down
    /// the helper thread gracefully!
    ///
    /// Essentially what happens is that we'll send a signal to the helper
    /// thread spawned and rely on `EINTR` being returned to wake up the helper
    /// thread. This involves installing a global `SIGUSR1` handler that does
    /// nothing along with sending signals to that thread. This may cause
    /// odd behavior in some applications, so it's recommended to review and
    /// test thoroughly before using this.
    pub fn into_helper_thread<F>(self, f: F) -> io::Result<HelperThread>
    where
        F: FnMut(io::Result<Acquired>) + Send + 'static,
    {
        let state = Arc::new(HelperState::default());
        Ok(HelperThread {
            inner: Some(imp::spawn_helper(self, state.clone(), Box::new(f))?),
            state,
        })
    }

    /// Blocks the current thread until a token is acquired.
    ///
    /// This is the same as [`Client::acquire`], except that it doesn't return
    /// an RAII helper. If successful the process will need to guarantee that
    /// [`Client::release_raw`] is called in the future.
    pub fn acquire_raw(&self) -> io::Result<()> {
        self.inner.acquire()?;
        Ok(())
    }

    /// Releases a jobserver token back to the original jobserver.
    ///
    /// This is intended to be paired with [`Client::acquire_raw`] if it was
    /// called, but in some situations it could also be called to relinquish a
    /// process's implicit token temporarily which is then re-acquired later.
    pub fn release_raw(&self) -> io::Result<()> {
        self.inner.release(None)?;
        Ok(())
    }
}

impl Drop for Acquired {
    fn drop(&mut self) {
        if !self.disabled {
            drop(self.client.release(Some(&self.data)));
        }
    }
}

/// Structure returned from [`Client::into_helper_thread`] to manage the lifetime
/// of the helper thread returned, see those associated docs for more info.
#[derive(Debug)]
pub struct HelperThread {
    inner: Option<imp::Helper>,
    state: Arc<HelperState>,
}

impl HelperThread {
    /// Trust: stop the original acquisition helper and require positive thread
    /// retirement. Ordinary Drop retains its existing best-effort behavior.
    pub fn shutdown(mut self) -> io::Result<()> {
        self.stop();
        if self.state.lock().consumer_done {
            Ok(())
        } else {
            Err(io::Error::new(io::ErrorKind::Other, "original jobserver helper retirement is unknown"))
        }
    }

    /// Trust: retire the helper thread with no bound on the wait, and report
    /// whether it was joined. `Drop` and [`HelperThread::shutdown`] give up
    /// after about a second; a helper that outlives them can hold a token it
    /// has read and not yet passed to the callback, and process exit then
    /// destroys that token. `Ok` is returned only once the thread has been
    /// joined after finishing its request loop. `Err` means either that the
    /// thread was joined but ended without finishing its loop, which is a
    /// panicked callback, or that it could not be told to stop and was not
    /// joined (a failed `SetEvent` on Windows; any blocked helper under Miri,
    /// which cannot send the signal); the message says which. A token the
    /// helper acquires while this runs is still passed to the callback before
    /// the thread exits, so the callback decides where it goes.
    ///
    /// The caller must not hold a lock the callback takes.
    pub fn shutdown_blocking(mut self) -> io::Result<()> {
        if let Some(helper) = self.inner.take() {
            self.state.lock().producer_done = true;
            self.state.cvar.notify_one();
            helper.join_blocking()?;
        }
        if self.state.lock().consumer_done {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                "jobserver helper thread ended without finishing its request loop",
            ))
        }
    }

    /// Trust: withdraw one request made by [`HelperThread::request_token`]
    /// that the helper has not started to serve. Returns whether one was
    /// withdrawn. A request the helper is already serving (it may be blocked
    /// reading the pool) is not interrupted: its token, if one arrives, is
    /// still passed to the callback.
    pub fn cancel_request(&self) -> bool {
        let mut state = self.state.lock();
        if state.requests == 0 {
            return false;
        }
        state.requests -= 1;
        true
    }

    /// Trust: the number of requests the helper has not started to serve.
    pub fn queued_requests(&self) -> usize {
        self.state.lock().requests
    }

    fn stop(&mut self) {
        if let Some(helper) = self.inner.take() {
            self.state.lock().producer_done = true;
            self.state.cvar.notify_one();
            helper.join();
        }
    }

    /// Request that the helper thread acquires a token, eventually calling the
    /// original closure with a token when it's available.
    ///
    /// For more information, see the docs on [`Client::into_helper_thread`].
    pub fn request_token(&self) {
        // Indicate that there's one more request for a token and then wake up
        // the helper thread if it's sleeping.
        self.state.lock().requests += 1;
        self.state.cvar.notify_one();
    }
}

impl Drop for HelperThread {
    fn drop(&mut self) {
        // Flag that the producer half is done so the helper thread should exit
        // quickly if it's waiting. Wake it up if it's actually waiting
        self.stop();
    }
}

impl HelperState {
    fn lock(&self) -> MutexGuard<'_, HelperInner> {
        self.lock.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Executes `f` for each request for a token, where `f` is expected to
    /// block and then provide the original closure with a token once it's
    /// acquired.
    ///
    /// This is an infinite loop until the helper thread is dropped, at which
    /// point everything should get interrupted.
    fn for_each_request(&self, mut f: impl FnMut(&HelperState)) {
        let mut lock = self.lock();

        // We only execute while we could receive requests, but as soon as
        // that's `false` we're out of here.
        while !lock.producer_done {
            // If no one's requested a token then we wait for someone to
            // request a token.
            if lock.requests == 0 {
                lock = self.cvar.wait(lock).unwrap_or_else(|e| e.into_inner());
                continue;
            }

            // Consume the request for a token, and then actually acquire a
            // token after unlocking our lock (not that acquisition happens in
            // `f`). This ensures that we don't actually hold the lock if we
            // wait for a long time for a token.
            lock.requests -= 1;
            drop(lock);
            f(self);
            lock = self.lock();
        }
        lock.consumer_done = true;
        self.cvar.notify_one();
    }
}

/// Finds and returns the value of `--jobserver-auth=<VALUE>` in the given
/// environment variable.
///
/// Precedence rules:
///
/// * The last instance wins [^1].
/// * `--jobserver-fds=` as a fallback when no `--jobserver-auth=` is present [^2].
///
/// [^1]: See ["GNU `make` manual: Sharing Job Slots with GNU `make`"](https://www.gnu.org/software/make/manual/make.html#Job-Slots)
/// _"Be aware that the `MAKEFLAGS` variable may contain multiple instances of
/// the `--jobserver-auth=` option. Only the last instance is relevant."_
///
/// [^2]: Refer to [the release announcement](https://git.savannah.gnu.org/cgit/make.git/tree/NEWS?h=4.2#n31)
/// of GNU Make 4.2, which states that `--jobserver-fds` was initially an
/// internal-only flag and was later renamed to `--jobserver-auth`.
fn find_jobserver_auth(var: &str) -> Option<&str> {
    ["--jobserver-auth=", "--jobserver-fds="]
        .iter()
        .find_map(|&arg| var.rsplit_once(arg).map(|(_, s)| s))
        .and_then(|s| s.split(' ').next())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn explicit_original_return_and_helper_shutdown_preserve_credit_inventory() {
        let server = Client::new(1).unwrap();
        let (send, receive) = std::sync::mpsc::channel();
        let helper = server.clone().into_helper_thread(move |result| send.send(result).unwrap()).unwrap();
        helper.request_token();
        let original = receive.recv_timeout(std::time::Duration::from_secs(10)).unwrap().unwrap();
        assert_eq!(server.available().unwrap(), 0);
        helper.shutdown().unwrap();
        original.return_to_server().unwrap();
        assert_eq!(server.available().unwrap(), 1);
    }

    #[cfg(unix)]
    #[test]
    fn explicit_return_error_retains_the_same_armed_original_guard() {
        use std::os::fd::AsRawFd;
        let server = Client::new(1).unwrap();
        let original = server.acquire().unwrap();
        let raw = server.inner.string_arg();
        let read = raw.split(',').next().unwrap().parse::<i32>().unwrap();
        let replacement = std::fs::File::open("/dev/null").unwrap();
        // SAFETY: replace only this test-owned client's actual read descriptor
        // with another valid descriptor. Its owner still has exactly one close;
        // the original pipe now has no reader, causing a real failed refund.
        assert_eq!(unsafe { libc::dup2(replacement.as_raw_fd(), read) }, read);
        let (original, error) = original.return_to_server().unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert!(!original.disabled);
        assert!(Arc::ptr_eq(&original.client, &server.inner));
        original.drop_without_releasing();
    }

    #[cfg(unix)]
    #[test]
    fn existing_transport_witnesses_preserve_kind_and_token_inventory() {
        use std::os::fd::AsFd;
        use std::os::unix::ffi::OsStrExt;
        let numeric = Client::new(1).unwrap();
        let TransportWitnesses::NumericPipe { read, write } =
            numeric.transport_witnesses().unwrap()
        else {
            panic!("anonymous pipe changed transport kind");
        };
        let imported = Client::from_pipe(read.as_fd(), write.as_fd()).unwrap();
        let token = imported.acquire().unwrap();
        // Darwin cannot safely enable nonblocking mode on a shared anonymous
        // pipe. Inventory inspection does not change those shared flags.
        assert_eq!(numeric.available().unwrap(), 0);
        drop(token);
        assert_eq!(numeric.available().unwrap(), 1);

        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("credits");
        let name = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
        // SAFETY: create only a new FIFO inside this owned private directory.
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        let named = Client::from_fifo(&path).unwrap();
        named.release_raw().unwrap();
        let TransportWitnesses::NamedFifo { path: locator, read, write } =
            named.transport_witnesses().unwrap()
        else {
            panic!("named FIFO changed transport kind");
        };
        assert_eq!(locator, path);
        let imported = Client::from_fifo_with_witnesses(
            &locator, read.as_fd(), write.as_fd(),
        ).unwrap();
        assert_eq!(named.available().unwrap(), 1);
        let token = imported.acquire().unwrap();
        assert!(named.try_acquire().unwrap().is_none());
        drop(token);
        assert_eq!(named.available().unwrap(), 1);
    }

    pub(super) fn run_named_fifo_try_acquire_tests(client: &Client) {
        assert!(client.try_acquire().unwrap().is_none());
        client.release_raw().unwrap();

        let acquired = client.try_acquire().unwrap().unwrap();
        assert!(client.try_acquire().unwrap().is_none());

        drop(acquired);
        client.try_acquire().unwrap().unwrap();
    }

    #[cfg(windows)]
    #[test]
    fn test_try_acquire() {
        let client = Client::new(0).unwrap();

        run_named_fifo_try_acquire_tests(&client);
    }

    #[test]
    fn no_helper_deadlock() {
        let x = crate::Client::new(32).unwrap();
        let _y = x.clone();
        std::mem::drop(x.into_helper_thread(|_| {}).unwrap());
    }

    #[test]
    fn test_find_jobserver_auth() {
        let cases = [
            ("", None),
            ("-j2", None),
            ("-j2 --jobserver-auth=3,4", Some("3,4")),
            ("--jobserver-auth=3,4 -j2", Some("3,4")),
            ("--jobserver-auth=3,4", Some("3,4")),
            ("--jobserver-auth=fifo:/myfifo", Some("fifo:/myfifo")),
            ("--jobserver-auth=", Some("")),
            ("--jobserver-auth", None),
            ("--jobserver-fds=3,4", Some("3,4")),
            ("--jobserver-fds=fifo:/myfifo", Some("fifo:/myfifo")),
            ("--jobserver-fds=", Some("")),
            ("--jobserver-fds", None),
            (
                "--jobserver-auth=auth-a --jobserver-auth=auth-b",
                Some("auth-b"),
            ),
            (
                "--jobserver-auth=auth-b --jobserver-auth=auth-a",
                Some("auth-a"),
            ),
            ("--jobserver-fds=fds-a --jobserver-fds=fds-b", Some("fds-b")),
            ("--jobserver-fds=fds-b --jobserver-fds=fds-a", Some("fds-a")),
            (
                "--jobserver-auth=auth-a --jobserver-fds=fds-a --jobserver-auth=auth-b",
                Some("auth-b"),
            ),
            (
                "--jobserver-fds=fds-a --jobserver-auth=auth-a --jobserver-fds=fds-b",
                Some("auth-a"),
            ),
        ];
        for (var, expected) in cases {
            let actual = find_jobserver_auth(var);
            assert_eq!(
                actual, expected,
                "expect {expected:?}, got {actual:?}, input `{var:?}`"
            );
        }
    }
}
