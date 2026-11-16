//! Shared owned scheduling transport for Trust shims, Targo and custodians.
//!
//! The default `client` feature includes GNU token scheduling. Disable default
//! features to transfer existing CPU/GNU descriptors through the same checked
//! handoff protocol without linking or constructing a token client.

#[cfg(feature = "client")]
use std::io;
#[cfg(all(unix, feature = "client"))]
use std::os::fd::{AsRawFd, OwnedFd};
#[cfg(feature = "client")]
use std::process::Command;
#[cfg(all(unix, feature = "client"))]
use std::sync::Arc;

#[cfg(feature = "client")]
use jobserver::{Client, FromEnvErrorKind};

#[cfg(feature = "client")]
mod idle_escrow;
#[cfg(feature = "client")]
pub use idle_escrow::IdleTokenEscrow;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod descriptor_transfer;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod fork_custody;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod handoff;
#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
// Trust: original GNU quiescence restrictions; no CPU/native authority.
pub mod quiescence;
// One ready-only request on the actual original GNU client; no CPU/native grant.
#[cfg(feature = "client")]
pub mod ready;

/// Scheduling-only advertisement installed by the owner of a chosen pool.
/// Its pathname and environment never grant proof or compiler authority.
pub const DESCENDANT_HANDOFF_ENV: &str = "CARGO_JOBSERVER_HANDOFF";

/// Inert advertisement for recovering an actual ancestor-owned implicit CPU lease.
pub const CPU_HANDOFF_ENV: &str = "TRUST_CPU_HANDOFF";

/// Inert routing for a complete original fixed claim, a separate role from
/// GNU transport and implicit CPU leases. The receiver still checks the claim.
pub const FIXED_CLAIM_HANDOFF_ENV: &str = "TRUST_FIXED_CLAIM_HANDOFF_V1";

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use handoff::{
    CpuLeaseHandoff, FixedClaimHandoff, ScopedHandoff, recover_cpu_lease, recover_cpu_resources,
    recover_fixed_claim, recover_named_fifo_resources, remove_endpoint_directories,
};

/// The caller's checked scheduling authority, retained through the child wait.
///
/// Trust std closes unrelated descriptors when spawning. Imported jobserver
/// clients keep private copies of their pipe descriptors, but version 0.1.35
/// still advertises the original numbers when configuring a child. Own a fresh
/// pair and advertise exactly the descriptors our spawn hook hands over.
#[derive(Clone, Debug)]
#[must_use]
#[cfg(feature = "client")]
pub struct Jobserver {
    client: Client,
    // Trust: a restricted descendant pool must also replace inherited GNU
    // aliases, so unaware make children cannot reopen the larger ancestor.
    propagate_make_flags: bool,
    #[cfg(unix)]
    pipe: Option<Arc<[OwnedFd; 2]>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    handoff: Option<Arc<handoff::Endpoint>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    named_scope: Option<Arc<NamedScope>>,
}

#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
struct NamedScope(std::ffi::OsString);

#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
impl std::fmt::Debug for NamedScope {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("NamedScope(<redacted>)")
    }
}

#[cfg(feature = "client")]
impl Jobserver {
    /// Create the build scheduler chosen by the caller, preserving its tokens
    /// and transport together. Importing never calls this constructor.
    pub fn new(limit: usize) -> io::Result<Self> {
        Self::with_client(Client::new(limit)?)
    }

    /// Adopt an owned named scheduling FIFO without creating any credits.
    /// The caller retains its private namespace through every child wait.
    #[cfg(unix)]
    pub fn from_fifo(path: &std::path::Path) -> io::Result<Self> {
        Self::with_client(Client::from_fifo(path)?)
    }

    /// Adopt a named pool only after the newly opened node matches retained
    /// descriptor witnesses. The namespace remains caller-owned.
    #[cfg(unix)]
    pub fn from_fifo_with_witnesses(
        path: &std::path::Path,
        read: std::os::fd::BorrowedFd<'_>,
        write: std::os::fd::BorrowedFd<'_>,
    ) -> io::Result<Self> {
        Self::with_client(Client::from_fifo_with_witnesses(path, read, write)?)
    }

    /// Authenticate a scoped named FIFO witness handoff before freshly opening
    /// the untrusted locator. No ambient import or private-token fallback.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn from_fifo_handoff(
        path: &std::path::Path,
        advertisement: &std::ffi::OsStr,
    ) -> io::Result<Self> {
        use std::os::fd::AsFd;
        let [read, write] = recover_named_fifo_resources(advertisement)?;
        let mut server = Self::from_fifo_with_witnesses(path, read.as_fd(), write.as_fd())?;
        // Keep the authenticated scoped witness route through a shim exec.
        // A pathname alone cannot bind a later opener to this original FIFO.
        server.named_scope = Some(Arc::new(NamedScope(advertisement.to_owned())));
        Ok(server)
    }

    /// Access this same server for in-process scheduling; do not re-import its
    /// advertised descriptor numbers after startup.
    pub fn client(&self) -> &Client {
        &self.client
    }

    /// The exact owned pipe advertised by [`Self::configure`], when this
    /// server uses numeric Unix descriptors. Authenticated native launchers
    /// retain the server and explicitly inherit these descriptors instead of
    /// interpreting environment strings as scheduling authority. A named FIFO
    /// has no inherited descriptor transport.
    #[cfg(unix)]
    pub fn pipe_descriptors(&self) -> Option<&[OwnedFd; 2]> {
        self.pipe.as_deref()
    }

    /// Allow unaware build scripts to hand this same pipe to Bootstrap shims.
    /// The caller must retain this owner through every relevant child wait.
    /// No tokens are acquired, created, replenished or proxied by this service.
    pub fn enable_descendant_handoff(&mut self) -> io::Result<()> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        self.enable_descendant_handoff_in(&std::env::temp_dir())?;
        // Named FIFOs and Windows semaphores already survive an unaware spawn.
        // Other Unix platforms retain their existing explicit-fd behavior;
        // this recovery protocol is implemented only on Linux and macOS.
        Ok(())
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn enable_descendant_handoff_in(&mut self, directory: &std::path::Path) -> io::Result<()> {
        if self.handoff.is_none()
            && let Some(pipe) = &self.pipe
        {
            self.handoff = Some(Arc::new(handoff::Endpoint::new(Arc::clone(pipe), directory)?));
        }
        Ok(())
    }

    /// Trust: retain the same scheduler and a recovery endpoint for an unaware
    /// descendant. The returned owner must outlive that descendant's wait;
    /// replacing the owning process with exec would destroy its endpoint.
    /// This clones existing transport only: no token or resource credit is made.
    pub fn for_descendant(&self) -> io::Result<Self> {
        let mut selected = self.clone();
        selected.enable_descendant_handoff()?;
        Ok(selected)
    }

    /// Recover only an authenticated ancestor-owned numeric scheduler.
    ///
    /// Unlike startup import, this never takes authority from ambient descriptor
    /// numbers. The advertisement must bind the exact flags and a live ancestor;
    /// both advertised slots must still be closed. Reused slots refuse. No tokens
    /// are created or acquired. Retain the owner through the descendant wait.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn from_authenticated_handoff(
        advertisement: &std::ffi::OsStr,
        cargo_flags: &std::ffi::OsStr,
    ) -> io::Result<Self> {
        use std::os::fd::AsFd;
        let pipe = handoff::recover(advertisement, cargo_flags)?;
        Self::with_client(Client::from_pipe(pipe[0].as_fd(), pipe[1].as_fd())?)
    }

    /// Recover an advertised ancestor scheduler without importing ambient FDs.
    /// Named FIFO locators are opened only after authenticating scoped original
    /// witnesses; numeric transport retains the closed-slot recovery rule.
    /// Absence returns None. An invalid advertisement never falls back.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn from_authenticated_env_handoff() -> io::Result<Option<Self>> {
        let Some(advertisement) = std::env::var_os(DESCENDANT_HANDOFF_ENV) else {
            return Ok(None);
        };
        if let Some(path) = Client::fifo_path_from_env()? {
            return Self::from_fifo_handoff(&path, &advertisement).map(Some);
        }
        let flags = std::env::var_os("CARGO_MAKEFLAGS").unwrap_or_default();
        Self::from_authenticated_handoff(&advertisement, &flags).map(Some)
    }

    /// Capture an inherited server without acquiring or creating any tokens.
    /// An advertised but invalid server is an error, never a private budget.
    ///
    /// # Safety
    ///
    /// Call at process startup, before opening argument files, sidecars or other
    /// descriptors. Checking for pipes cannot identify an unrelated pipe that
    /// has already reused an advertised descriptor number.
    pub unsafe fn from_env() -> io::Result<Option<Self>> {
        // SAFETY: the caller guarantees the early-import precondition above.
        unsafe { Self::from_env_policy(false) }
    }

    // One importer owns both policies. Missing auth is not malformed auth:
    // ordinary MAKEFLAGS such as -j8/-k legitimately contain no jobserver.
    unsafe fn from_env_policy(checked_auth: bool) -> io::Result<Option<Self>> {
        // SAFETY: the caller guarantees the early-import precondition above.
        let inherited = unsafe { Client::from_env_ext(true) };
        let client = match inherited.client {
            Ok(client) => client,
            Err(error)
                if matches!(
                    error.kind(),
                    FromEnvErrorKind::NoEnvVar | FromEnvErrorKind::NoJobserver
                ) =>
            {
                return Ok(None);
            }
            Err(error)
                if !checked_auth
                    && matches!(
                        error.kind(),
                        FromEnvErrorKind::NegativeFd | FromEnvErrorKind::Unsupported
                    ) =>
            {
                return Ok(None);
            }
            Err(error) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("invalid advertised jobserver: {error}"),
                ));
            }
        };
        Self::with_client(client).map(Some)
    }

    /// Import a scheduler for a native build driver, recovering only an
    /// authenticated ancestral pipe after an unaware descendant closed both
    /// advertised descriptors. No ambient environment bytes are changed.
    ///
    /// # Safety
    ///
    /// The early-startup requirement of [`Jobserver::from_env`] applies.
    pub unsafe fn from_env_with_handoff() -> io::Result<Option<Self>> {
        // SAFETY: the caller guarantees the documented early capture.
        unsafe { Self::from_env_with_handoff_policy(false) }
    }

    /// Capture real inherited transport while retaining errors for actual
    /// disabled/unsupported auth. Ordinary MAKEFLAGS without an auth option
    /// still yields None. No tokens are created and no environment is changed.
    ///
    /// # Safety
    /// The early-startup requirement of [`Jobserver::from_env`] applies.
    pub unsafe fn from_env_with_handoff_checked() -> io::Result<Option<Self>> {
        // SAFETY: the caller guarantees the documented early capture.
        unsafe { Self::from_env_with_handoff_policy(true) }
    }

    unsafe fn from_env_with_handoff_policy(checked_auth: bool) -> io::Result<Option<Self>> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(advertisement) = std::env::var_os(DESCENDANT_HANDOFF_ENV)
            && let Some(path) = Client::fifo_path_from_env()?
        {
            // Authenticate the actual original FIFO witnesses BEFORE any
            // pathname open. A malformed or mismatched role must not fall
            // back to importing an unchecked ambient FIFO.
            return Self::from_fifo_handoff(&path, &advertisement).map(Some);
        }
        // SAFETY: the caller guarantees capture before descriptor reuse.
        match unsafe { Self::from_env_policy(checked_auth) } {
            Ok(server) => Ok(server),
            Err(original) => {
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                if let Some(advertisement) = std::env::var_os(DESCENDANT_HANDOFF_ENV) {
                    // Trust (JOBSERVER-STALE-MAKEFLAGS-1): bind the handoff to the
                    // variable the failed import read. The client reads these in
                    // this order, and a harness between the scheduler and this
                    // process may have removed CARGO_MAKEFLAGS alone.
                    let flags = ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"]
                        .into_iter()
                        .find_map(std::env::var_os)
                        .unwrap_or_default();
                    let recovered = Self::from_authenticated_handoff(&advertisement, &flags);
                    return recovered.map(Some).map_err(|error| {
                        io::Error::new(
                            error.kind(),
                            format!("{original}; cannot recover inherited jobserver: {error}"),
                        )
                    });
                }
                Err(original)
            }
        }
    }

    /// Retain an already-owned scheduler without importing ambient descriptors
    /// or creating tokens. Keep its owner alive through every configured wait.
    pub fn from_owned_client(client: Client) -> io::Result<Self> {
        Self::with_client(client)
    }

    fn with_client(client: Client) -> io::Result<Self> {
        #[cfg(unix)]
        let pipe = Self::own_pipe(&client)?;
        Ok(Self {
            client,
            propagate_make_flags: false,
            #[cfg(unix)]
            pipe,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            handoff: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            named_scope: None,
        })
    }

    #[cfg(unix)]
    fn own_pipe(client: &Client) -> io::Result<Option<Arc<[OwnedFd; 2]>>> {
        // Clone actual original descriptions from their native owner, never
        // parse configured environment strings back into descriptor authority.
        match client.transport_witnesses()? {
            jobserver::TransportWitnesses::NumericPipe { read, write } => {
                Ok(Some(Arc::new([read, write])))
            }
            jobserver::TransportWitnesses::NamedFifo { path, read, write } => {
                use std::os::unix::fs::{FileTypeExt as _, MetadataExt as _};
                let selected = std::fs::metadata(path)?;
                let read = std::fs::File::from(read).metadata()?;
                let write = std::fs::File::from(write).metadata()?;
                if !selected.file_type().is_fifo()
                    || !read.file_type().is_fifo()
                    || !write.file_type().is_fifo()
                    || (selected.dev(), selected.ino()) != (read.dev(), read.ino())
                    || (selected.dev(), selected.ino()) != (write.dev(), write.ino())
                {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "original named GNU witnesses or selected FIFO changed",
                    ));
                }
                Ok(None)
            }
        }
    }

    /// Configure the final child after all other environment/argv processing.
    /// Explicitly hand over only the checked jobserver's endpoints.
    pub fn configure(&self, command: &mut Command) {
        // An ambient endpoint must never become a different pool's handoff.
        command.env_remove(DESCENDANT_HANDOFF_ENV);
        #[cfg(unix)]
        if let Some(pipe) = &self.pipe {
            configure_pipe(pipe, command);
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(handoff) = &self.handoff {
                handoff.configure(command);
            }
            if self.propagate_make_flags {
                Self::configure_make_variables(command);
            }
            return;
        }
        // FIFO paths and Windows semaphores use the library's transport.
        self.client.configure(command);
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(scope) = &self.named_scope {
            command.env(DESCENDANT_HANDOFF_ENV, &scope.0);
        }
        if self.propagate_make_flags {
            Self::configure_make_variables(command);
        }
    }

    /// Carry this actual server in every GNU variable for each configured
    /// descendant, including unaware make clients. Clones retain the policy.
    /// This grants no credits and changes no process-wide environment.
    pub fn propagate_make_flags(&mut self) {
        self.propagate_make_flags = true;
    }

    /// Configure GNU make with the same owned transport as other children.
    /// Derive all three variables from the final descriptor pair, never from
    /// the imported flags whose original descriptors may already be closed.
    pub fn configure_make(&self, command: &mut Command) {
        self.configure(command);
        Self::configure_make_variables(command);
    }

    /// Configure an actual GNU make program. A numeric pipe is configured as
    /// by [`Self::configure_make`]. A named FIFO is handed over as this
    /// server's own retained read/write descriptions, advertised as a numeric
    /// pair in all three variables: GNU make before 4.4 stops on the `fifo:`
    /// spelling (`invalid --jobserver-auth string`), and every GNU make reads
    /// `R,W`. The pair is the same FIFO: no token or pool is created. Only the
    /// make program gets this spelling; [`Self::configure_make`] still hands
    /// other children the path, which survives a descriptor-stripping spawn.
    pub fn configure_gnu_make(&self, command: &mut Command) -> io::Result<()> {
        #[cfg(unix)]
        if self.pipe.is_none()
            && let jobserver::TransportWitnesses::NamedFifo { read, write, .. } =
                self.client.transport_witnesses()?
        {
            // Make inherits these descriptors itself; a scoped named handoff
            // would name a path this advertisement no longer carries.
            command.env_remove(DESCENDANT_HANDOFF_ENV);
            configure_pipe(&Arc::new([read, write]), command);
            Self::configure_make_variables(command);
            return Ok(());
        }
        self.configure_make(command);
        Ok(())
    }

    fn configure_make_variables(command: &mut Command) {
        let flags = command
            .get_envs()
            .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten())
            .expect("jobserver configured no make flags")
            .to_owned();
        command.env("MAKEFLAGS", &flags).env("MFLAGS", flags);
    }
}

#[cfg(all(unix, feature = "client"))]
fn configure_pipe(pipe: &Arc<[OwnedFd; 2]>, command: &mut Command) {
    use std::os::unix::process::CommandExt;

    let pipe = Arc::clone(pipe);
    let auth = format!("{},{}", pipe[0].as_raw_fd(), pipe[1].as_raw_fd());
    command.env("CARGO_MAKEFLAGS", format!("-j --jobserver-fds={auth} --jobserver-auth={auth}"));
    rebind_make_variables(command, &auth);
    // SAFETY: only async-signal-safe fcntl calls run after fork. The captured
    // owners keep the exact advertised descriptors live through spawn; Trust
    // std strips descriptors before running this explicit handoff hook.
    unsafe {
        command.pre_exec(move || {
            for fd in pipe.iter() {
                let flags = libc::fcntl(fd.as_raw_fd(), libc::F_GETFD);
                if flags < 0
                    || libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
                {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
}

/// Trust (JOBSERVER-STALE-MAKEFLAGS-1): the child gets this pool at freshly owned
/// descriptor numbers, and the numbers an inherited `MAKEFLAGS` or `MFLAGS`
/// names are closed in it or name another file. Left alone, a descendant that
/// reads those variables (one whose `CARGO_MAKEFLAGS` a harness removed, or a
/// make started with a plain spawn) imports a dead advertisement and a native
/// Targo below it refuses to start. Name the pair actually handed over in every
/// numeric advertisement the child will see; a variable with none is left as it
/// is, so a child that was told of no jobserver is still told of none.
#[cfg(all(unix, feature = "client"))]
fn rebind_make_variables(command: &mut Command, auth: &str) {
    for name in ["MAKEFLAGS", "MFLAGS"] {
        let explicit = command.get_envs().find(|(key, _)| *key == name).map(|(_, value)| value);
        let current = match explicit {
            Some(value) => value.map(std::ffi::OsStr::to_owned),
            None => std::env::var_os(name),
        };
        let Some(current) = current else { continue };
        match current.to_str().map(|flags| rebind_numeric_auth(flags, auth)) {
            Some(Some(rebound)) => {
                command.env(name, rebound);
            }
            Some(None) => {}
            // Flags that are not text cannot be read for an advertisement.
            None => {
                command.env_remove(name);
            }
        }
    }
}

/// `flags` with each numeric `--jobserver-auth=R,W` and `--jobserver-fds=R,W`
/// naming `auth`, or `None` when it names that pair already or names no numeric
/// pair. A `fifo:` path stays valid in the child and is never rewritten.
#[cfg(all(unix, feature = "client"))]
fn rebind_numeric_auth(flags: &str, auth: &str) -> Option<String> {
    let mut changed = false;
    let rebound = flags
        .split(' ')
        .map(|word| {
            for option in ["--jobserver-auth=", "--jobserver-fds="] {
                if let Some(pair) = word.strip_prefix(option)
                    && pair != auth
                    && pair.split_once(',').is_some_and(|(read, write)| {
                        read.parse::<i32>().is_ok() && write.parse::<i32>().is_ok()
                    })
                {
                    changed = true;
                    return format!("{option}{auth}");
                }
            }
            word.to_owned()
        })
        .collect::<Vec<_>>()
        .join(" ");
    changed.then_some(rebound)
}

/// An optional inherited scheduler, used by compiler/doc shims that do not
/// create a scheduler when none was passed by their caller.
#[derive(Debug)]
#[must_use]
#[cfg(feature = "client")]
pub struct InheritedJobserver(Option<Jobserver>);

#[cfg(all(test, unix, feature = "client"))]
#[path = "tests/transport_witnesses.rs"]
mod transport_witness_tests;

#[cfg(all(test, unix, feature = "client"))]
#[path = "tests/make_variables.rs"]
mod make_variable_tests;

#[cfg(feature = "client")]
impl InheritedJobserver {
    /// Capture the inherited scheduler before opening sidecars/argument files.
    ///
    /// # Safety
    ///
    /// The early-startup requirement of [`Jobserver::from_env`] applies.
    pub unsafe fn from_env() -> io::Result<Self> {
        // SAFETY: the caller guarantees the documented early capture. The
        // checked importer authenticates scoped named witnesses before opening
        // their locator and preserves numeric recovery's closed-target rule.
        unsafe { Jobserver::from_env_with_handoff() }.map(Self)
    }

    /// Whether startup validated an actual inherited scheduler transport.
    /// This observation grants no additional tokens or scheduling authority.
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }

    /// Hand the same scheduler to this child, without creating a private one.
    pub fn configure(&self, command: &mut Command) {
        if let Some(jobserver) = &self.0 {
            jobserver.configure(command);
        }
        // Numeric transport has freshly owned descriptor numbers; its original
        // binding cannot be reused. Named transport retains its checked scope
        // so the next opener must authenticate the original FIFO witnesses.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if self.0.as_ref().is_some_and(|server| server.named_scope.is_some()) {
            return;
        }
        command.env_remove(DESCENDANT_HANDOFF_ENV);
    }
}
