use std::sync::{Arc, OnceLock};

use parking_lot::{Condvar, Mutex};

#[path = "jobserver/early.rs"]
mod early;
#[doc(hidden)]
pub use early::BoundedQueryGrant;
pub use early::{LentCompile, capture as capture_early};

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): the native entry of a libtest binary
/// whose tests run the compiler in process (rustc_driver_impl's unit tests,
/// trust-mir-extract's). The binary is the admitted process and waits on each
/// compile it runs. Under `build-slot` protocol 1 nothing hands it a scheduler,
/// so a compile refuses ("native compiler work has no captured inherited GNU
/// scheduler"). When it is owed one ([`own_execution_owed`]) and its command
/// line chose no thread count other than one ([`test_threads_admit_one`]), it
/// lends the compiler its own execution: an owned pool holding ZERO tokens, and
/// `RUST_TEST_THREADS=1`, narrowing any inherited default (Bootstrap sets its
/// `-j` there) as the rustdoc shim's loan does. A compile then runs only on the
/// execution its waiting test thread hands it, one compile at a time
/// ([`enter_lent_compile`]), and gains no parallelism nobody admitted. When it
/// is owed one but its command line chose another thread count, it refuses and
/// says so. In every other case this is exactly [`capture_early`]: any
/// advertisement is captured and judged, and a strict run with no scheduler
/// still refuses.
///
/// # Safety
/// As [`capture_early`]: the generated test main's first operation, before
/// libtest reads its arguments, opens a file or starts a thread.
pub unsafe fn capture_early_for_test_harness() -> Result<(), String> {
    if !own_execution_owed() {
        // SAFETY: forwarded; our caller guarantees genuine native entry.
        return unsafe { early::capture() };
    }
    let args: Vec<std::ffi::OsString> = std::env::args_os().skip(1).collect();
    if !test_threads_admit_one(args.iter().cloned()) {
        let chosen: Vec<_> = args
            .iter()
            .filter(|arg| arg.as_encoded_bytes().starts_with(b"--test-threads"))
            .map(|arg| arg.to_string_lossy())
            .collect();
        return Err(format!(
            "native compiler work has no captured inherited GNU scheduler, and this test run \
             cannot lend its compiler its own execution: its command line chose a thread count \
             other than one ({})",
            chosen.join(" ")
        ));
    }
    let inherited = std::env::var_os("RUST_TEST_THREADS").filter(|value| value != "1");
    // SAFETY: the native entry is single-threaded (only the checks above have
    // read the environment) and libtest reads this variable afterwards. A
    // blessed mutation, before any thread exists.
    #[cfg_attr(not(bootstrap), allow(unknown_lints, env_mutation))]
    unsafe {
        std::env::set_var("RUST_TEST_THREADS", "1")
    };
    // SAFETY: forwarded; our caller guarantees genuine native entry.
    unsafe { early::capture_lending_own_execution() }?;
    if let Some(inherited) = inherited {
        eprintln!(
            "note: build-slot protocol 1 handed this test run no compiler scheduler; it lent \
             its compiler its own execution and runs one test at a time \
             (RUST_TEST_THREADS={} narrowed to 1)",
            inherited.to_string_lossy()
        );
    }
    Ok(())
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): whether this process is owed a loan
/// of its own execution: a bare `build-slot` protocol-1 admission with nothing
/// advertised to it (see `early::own_execution_owed`).
pub fn own_execution_owed() -> bool {
    early::own_execution_owed(|name| std::env::var_os(name))
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): whether this process runs its compiles
/// on a loan of its own execution ([`capture_early_for_test_harness`]).
pub fn lends_own_execution() -> bool {
    early::lent_own_execution()
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): held for one whole compile. `None`
/// unless this process runs on a loan of its own execution; on a loan, a
/// compile that would overlap another refuses rather than waits.
pub fn enter_lent_compile() -> Result<Option<LentCompile>, String> {
    early::enter_lent_compile()
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): whether a libtest run with these
/// arguments (program name excluded) can be bound to one test at a time
/// without overriding a count its command line chose. libtest prefers
/// `--test-threads` to `RUST_TEST_THREADS`, so a loan can narrow the variable,
/// an inherited default, but not the argument. Any thread count other than
/// exactly `--test-threads=1`, in any spelling (including the separated
/// `--test-threads N`), is a choice the loan cannot honor, so no loan is made.
pub fn test_threads_admit_one(args: impl IntoIterator<Item = std::ffi::OsString>) -> bool {
    args.into_iter().all(|arg| {
        !arg.as_encoded_bytes().starts_with(b"--test-threads") || arg == "--test-threads=1"
    })
}

/// Fixed compiler member protocol data, never execution or proof authority.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub const WORKLOAD_MEMBER_PROTOCOL_MARKER: [u8; 64] =
    trust_resource_controller::workload::WORKLOAD_MEMBER_PROTOCOL_MARKER;
// Trust: DATA support only for the distinct private Fixed compiler protocol.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub const BOOTSTRAP_FIXED_COMPILER_PROTOCOL_MARKER:[u8;64]=
    trust_resource_controller::bootstrap_graph::compilation::compiler::BOOTSTRAP_FIXED_COMPILER_PROTOCOL_MARKER;

// Trust: all compiler phases use the same owned credit type.
#[path = "jobserver/admission.rs"]
mod admission;
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "jobserver/runtime.rs"]
mod runtime;
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "jobserver/runtime_v3.rs"]
mod runtime_v3;
pub use admission::{Acquired, Client, HelperThread};
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use runtime_v3::NativeV3;
// Trust: separately issued private Fixed compiler, never a NativeV3 upgrade.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "jobserver/bootstrap_fixed.rs"]
mod bootstrap_fixed;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use bootstrap_fixed::BootstrapFixed;
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "jobserver/native_park.rs"]
mod native_park;
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "jobserver/workload_proxy.rs"]
mod workload_proxy;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use native_park::{BootstrapCompilerPause, CompilerPause};
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "jobserver/child.rs"]
mod child;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use child::ChildResources;

// We stick the jobserver client into a global and initialize it once, because there could be
// multiple compiler instances in this process, and the jobserver is per-process.
static CLIENT: OnceLock<Result<Client, String>> = OnceLock::new();

/// Initializes a jobserver client for the current rustc process.
/// Reuses descriptors captured at native process entry. Invalid inherited native
/// custody refuses; only a truly no-context invocation creates a private server.
/// The reporting callback remains for embedding API compatibility; inherited
/// capture failures are returned rather than replaced by private tokens.
pub fn initialize(
    limit: usize,
    worker_v2: bool,
    _report: impl FnOnce(String),
) -> Result<(), String> {
    let result = CLIENT.get_or_init(|| {
        let local = early::local(limit, worker_v2)?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if worker_v2 {
            return runtime::activate(local).map_err(|error| error.to_string());
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        if worker_v2 {
            return Err("native CPU worker protocol is unsupported on this host".into());
        }
        Ok(Client::from_local(local))
    });
    result.as_ref().map(|_| ()).map_err(Clone::clone)
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): the refusal recorded in place of
/// a scheduler for the session of a process admitted only as a bounded query.
const BOUNDED_QUERY_HAS_NO_SCHEDULER: &str =
    "a bounded metadata query compiles nothing and was given no compiler scheduler";

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): for the compiler driver only,
/// for a session it will only answer with a bounded metadata query and then
/// stop: no input, and nothing but such a print. If native entry admitted this
/// process (strict, no GNU scheduler captured, its complete argv one fixed
/// query), that session may be answered on no scheduler. One grant per
/// process. The driver holds it for the session; when it is dropped, used or
/// not (also when the session ends in a fatal error before scheduler setup),
/// the grant is spent and no later session can use it.
#[doc(hidden)]
pub fn grant_bounded_query_session() -> Option<BoundedQueryGrant> {
    early::grant_bounded_query_session()
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): the grant, taken by the session
/// it was made for. Only `take_bounded_query_session` creates one.
#[must_use]
pub struct BoundedQuerySession(());

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): every session that reaches
/// scheduler setup spends the process's one grant there; only the first, and
/// only while a driver holds the grant, receives it.
pub fn take_bounded_query_session() -> Option<BoundedQuerySession> {
    early::take_bounded_query_session().then_some(BoundedQuerySession(()))
}

impl BoundedQuerySession {
    /// Record the scheduler as refused instead of initializing one; true if
    /// this did so. A later session's initialization returns that refusal.
    pub fn withhold_scheduler(self) -> bool {
        let mut withheld = false;
        CLIENT.get_or_init(|| {
            withheld = true;
            Err(BOUNDED_QUERY_HAS_NO_SCHEDULER.into())
        });
        withheld
    }
}

/// Activate only an authenticated borrowed native compiler member. Existing
/// legacy clients and stored failures can never be upgraded or replaced.
pub fn initialize_v3(limit: usize) -> Result<(), String> {
    let result = CLIENT.get_or_init(|| {
        let local = early::local(limit, true)?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            runtime_v3::activate(local).map_err(|error| error.to_string())
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            let _ = local;
            Err("native v3 compiler is unsupported on this host".into())
        }
    });
    match result {
        Ok(client) if client.is_native_v3() => Ok(()),
        Ok(_) => Err("compiler jobserver was already initialized without native v3 custody".into()),
        Err(error) => Err(error.clone()),
    }
}

// Trust: only the actual private native issuer can initialize this distinct
// original-Root Fixed member. Existing clients/failures cannot be promoted.
pub fn initialize_bootstrap_fixed(limit: usize) -> Result<(), String> {
    let result = CLIENT.get_or_init(|| {
        let local = early::local(limit, true)?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            bootstrap_fixed::activate(local).map_err(|error| error.to_string())
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            let _ = local;
            Err("private Fixed compiler is unavailable on this host".into())
        }
    });
    match result {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        Ok(client) if client.bootstrap_fixed_context().is_some() => Ok(()),
        Ok(_) => Err("compiler scheduler already has a different original owner".into()),
        Err(error) => Err(error.clone()),
    }
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub fn bootstrap_fixed_context() -> Option<Arc<BootstrapFixed>> {
    CLIENT.get()?.as_ref().ok()?.bootstrap_fixed_context()
}

/// Observe already-initialized native custody without importing or allocating
/// scheduler resources at a late child/plugin boundary.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub fn native_v3_context() -> Option<Arc<NativeV3>> {
    CLIENT.get()?.as_ref().ok()?.native_context()
}

/// Trust: retain the scheduler for a child compiler even when rustdoc has not
/// initialized a global compiler session. Reuse native-entry custody; never
/// reimport ambient descriptor numbers here. A truly unscoped caller uses the
/// existing local policy with one permanently held execution and no extra GNU
/// credit. The caller must serialize loans and retain the owner through wait.
pub fn for_compiler_descendant() -> Result<jobserver_utils::Jobserver, String> {
    if let Some(client) = CLIENT.get() {
        return client.as_ref().map_err(Clone::clone)?.for_compiler_descendant();
    }
    let local = early::local(1, false)?;
    early::for_compiler_descendant(&local)
}

/// Returns the jobserver client previously initialized by `initialize_checked`.
///
/// # Assumptions about holding jobserver tokens
///
/// Rustc process must always hold a single token to avoid being permanently starved and blocked.
/// - If the jobserver is inherited from a higher level build tool, the assumption is that the tool
///   will hold the token and not release it until the rustc process exits.
/// - If the jobserver is owned by the current rustc, the token is acquired by `default_client`.
///
/// To avoid releasing the last token, users of the client returned by this function must ensure
/// that they never release more tokens than was previously explicitly acquired.
/// Example of a sequence that can accidentally release the last token:
/// `release_raw` -> `wait` -> `acquire_raw`.
/// To avoid situations like this use the `jobserver::Proxy` wrapper instead,
/// it will ensure that the last token is never released.
pub fn client() -> Client {
    CLIENT
        .get()
        .expect("uninitialized jobserver client")
        .as_ref()
        .expect("failed jobserver initialization")
        .clone()
}

struct ProxyData {
    /// The number of tokens assigned to actively working threads,
    /// possibly including the single permanently held token.
    /// If this number is 0, the single token is still held by the process,
    /// but is not currently used for active CPU work.
    /// This can happen, for example, if the main thread is waiting for something,
    /// in that case some other thread can start using this token to do work.
    used: u16,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    active: Option<std::collections::HashMap<std::thread::ThreadId, u16>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    workload: Option<workload_proxy::Assignments>,
    /// The number of threads currently requesting a token and waiting.
    /// If the proxy releases a token it can immediately give it to one of these threads
    /// without going through the real jobserver.
    pending: u16,
    // Trust: owning these guards keeps global worker leases paired with the
    // local tokens, including when a proxy is dropped during unwinding.
    tokens: Vec<Acquired>,
    // Trust: a failed admission helper must wake waiters instead of stranding them.
    error: Option<String>,
}

/// A wrapper around jobserver client used for two purposes:
/// - Ensuring that the single token that must be permanently held by the rustc process
///   cannot be accidentally released.
/// - "Token buffering", immediately acquiring freshly released tokens if necessary,
///   without going through the real jobserver.
pub struct Proxy {
    /// The wrapped jobserver client.
    _client: Client,
    /// Helper thread associated with the wrapped client.
    // Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): `None` once `shutdown` has retired
    // it. Lock order: `ProxyData`, then this, then the helper's own state. It
    // is never held while the helper is joined, because the helper's callback
    // takes `ProxyData`.
    helper: Mutex<Option<HelperThread>>,
    // Trust: the callback shares token state, never the owner of its helper.
    // Capturing Arc<Proxy> creates a cycle that leaks one thread per compiler.
    shared: Arc<ProxyShared>,
}

struct ProxyShared {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    workload: bool,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    registry: Option<Arc<native_park::Registry>>,
    /// The proxy's own data.
    data: Mutex<ProxyData>,
    /// Threads which are currently waiting for a token will wait on this condvar.
    wake_pending: Condvar,
}

impl ProxyShared {
    fn failed(&self, error: String) {
        let mut data = self.data.lock();
        data.error = Some(error);
        self.wake_pending.notify_all();
    }
}

impl Proxy {
    pub fn new() -> Arc<Self> {
        Self::with_client(client())
    }

    fn with_client(client: Client) -> Arc<Self> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let registry = client
            .native_context()
            .map(|context| context.registry().clone())
            .or_else(|| client.bootstrap_fixed_context().map(|context| context.registry().clone()));
        Self::build_client(
            client,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            registry,
        )
    }

    fn build_client(
        client: Client,
        #[cfg(any(target_os = "linux", target_os = "macos"))] registry: Option<
            Arc<native_park::Registry>,
        >,
    ) -> Arc<Self> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let workload = client.native_context().is_some_and(|context| context.is_workload());
        Self::build_with_ownership(
            client,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            registry,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            workload,
        )
    }

    fn build_with_ownership(
        client: Client,
        #[cfg(any(target_os = "linux", target_os = "macos"))] registry: Option<
            Arc<native_park::Registry>,
        >,
        #[cfg(any(target_os = "linux", target_os = "macos"))] workload: bool,
    ) -> Arc<Self> {
        let shared = Arc::new(ProxyShared {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            workload,
            // Assume that the main thread is actively doing work when it creates the proxy.
            data: Mutex::new(ProxyData {
                used: 1,
                pending: 0,
                tokens: Vec::new(),
                error: None,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                active: registry
                    .as_ref()
                    .map(|_| std::collections::HashMap::from([(std::thread::current().id(), 1)])),
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                workload: workload
                    .then(|| workload_proxy::Assignments::new(std::thread::current().id())),
            }),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            registry: registry.clone(),
            wake_pending: Condvar::new(),
        });
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(registry) = &registry {
            registry.register(&shared).expect("native proxy registration refused");
        }
        let callback_state = Arc::clone(&shared);
        let helper = client
            .clone()
            .into_helper_thread(move |token| {
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                let _admission = if let Some(registry) = &callback_state.registry {
                    match registry.callback(token.is_err()) {
                        Some(admission) => Some(admission),
                        None => {
                            if let Ok(token) = token {
                                token
                                    .retire_unused()
                                    .expect("unpublished proxy offer settlement failed");
                            }
                            return; // poisoned waiters were notified
                        }
                    }
                } else {
                    None
                };
                // Reminder: this callback runs when the helper acquires a token.
                if let Err(error) = &token {
                    callback_state.failed(error.to_string());
                    return;
                }
                if let Ok(token) = token {
                    let mut data = callback_state.data.lock();
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    if callback_state.workload {
                        let free_primary = usize::from(
                            data.workload
                                .as_ref()
                                .expect("workload assignments absent")
                                .implicit_available(),
                        );
                        if usize::from(data.pending) > data.tokens.len() + free_primary {
                            data.tokens.push(token);
                            data.used =
                                data.used.checked_add(1).expect("workload reservation overflow");
                            callback_state.wake_pending.notify_one();
                        } else {
                            callback_state.wake_pending.notify_all();
                            drop(data);
                            token
                                .retire_unused()
                                .expect("unused workload proxy offer settlement failed");
                        }
                        return;
                    }
                    if data.pending > 0 {
                        // The token is still needed, give it to one of the waiting threads.
                        data.tokens.push(token);
                        assert!(data.used > 0);
                        data.used += 1;
                        data.pending -= 1;
                        callback_state.wake_pending.notify_one();
                    } else {
                        // The token is no longer needed, release it by dropping.
                        drop(data);
                        token.retire_unused().expect("unused proxy offer settlement failed");
                    }
                }
            })
            .expect("failed to spawn helper thread");
        Arc::new(Proxy { _client: client, helper: Mutex::new(Some(helper)), shared })
    }

    // Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): the one way a waiter files a helper
    // request. A thread that needs a token after the helper was retired would
    // otherwise wait for a token nobody will fetch.
    fn request_token(&self) {
        self.helper
            .lock()
            .as_ref()
            .expect("jobserver proxy asked for a token after its helper was retired")
            .request_token();
    }

    /// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): the requests the helper has not
    /// started to serve.
    #[cfg(test)]
    fn queued_helper_requests(&self) -> usize {
        self.helper.lock().as_ref().map_or(0, HelperThread::queued_requests)
    }

    /// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): retire the helper thread, then
    /// check that this proxy holds nothing but the process's own token.
    ///
    /// Call it on the thread that created the proxy, once every thread that
    /// used it has been joined and that thread holds its token again. Dropping
    /// the proxy is not enough: the pipe helper's `Drop` stops waiting after
    /// about a second, and the drop runs wherever the last owner is, which can
    /// be a detached thread racing process exit. A helper alive at exit can
    /// have read a token and not yet handed it over; that token is lost and the
    /// exit status does not say so. This waits for the join with no bound, so
    /// when it returns the helper holds nothing, and a token it read meanwhile
    /// went through the callback, which returns it when nobody waits for it.
    ///
    /// `Err` means the accounting is not settled: the helper could not be
    /// retired or its callback panicked, the helper reported a failed
    /// admission that no waiter was there to see, a thread still waits for a
    /// token, or tokens beyond the process's own are still held. Held tokens
    /// are given back before the error is reported: an offer no thread
    /// committed is retired as unused, any other is dropped as
    /// `release_thread` drops it, and a failed settlement joins the error.
    /// A second call finds no helper and checks the accounting again.
    pub fn shutdown(&self) -> Result<(), String> {
        // Take the helper out and release its lock before joining: the
        // callback takes `ProxyData`, and a thread holding `ProxyData` takes
        // this lock to file a request.
        let helper = self.helper.lock().take();
        let mut problems = Vec::new();
        if let Some(helper) = helper
            && let Err(error) = helper.shutdown_blocking()
        {
            problems.push(format!("jobserver helper was not retired cleanly: {error}"));
        }
        let mut data = self.shared.data.lock();
        let (used, pending) = (data.used, data.pending);
        let stray = std::mem::take(&mut data.tokens);
        // Each held token is counted in `used`, in every mode. They leave
        // together, so a second call does not report them again.
        data.used = used.saturating_sub(u16::try_from(stray.len()).unwrap_or(u16::MAX));
        let admission_error = data.error.take();
        drop(data);
        if let Some(error) = admission_error {
            problems.push(format!("jobserver admission failed with nobody waiting: {error}"));
        }
        if pending != 0 || !stray.is_empty() || used > 1 {
            problems.push(format!(
                "jobserver proxy accounting is unsettled at shutdown: {used} threads counted as \
                 working, {pending} waiting for a token, {} pool tokens held",
                stray.len()
            ));
        }
        // Giving a token back writes to the pool or talks to the host, so it
        // is done without the lock.
        for token in stray {
            if token.was_committed() {
                // Its thread is gone. Dropping is how `release_thread` returns
                // a committed credit; a workload loan is never committed while
                // it sits here (`workload_proxy::acquire` pops it first).
                drop(token);
            } else if let Err(error) = token.retire_unused() {
                problems.push(format!("a held jobserver offer was not settled: {error}"));
            }
        }
        if problems.is_empty() { Ok(()) } else { Err(problems.join("; ")) }
    }

    /// Acquires a token, possibly using some buffered tokens as an optimization.
    /// May block and wait until the token is available.
    pub fn acquire_thread(&self) {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(registry) = &self.shared.registry {
            self.acquire_native(registry);
            return;
        }
        let mut data = self.shared.data.lock();
        assert!(data.error.is_none(), "worker admission failed: {:?}", data.error);

        if data.used == 0 {
            // No threads are doing any active work, but we are still holding the last token.
            // Give that token to the current thread.
            assert_eq!(data.pending, 0);
            data.used += 1;
        } else {
            // Request a token from the helper thread, this is a non-blocking operation.
            // Then wait until this or some other request succeeds.
            self.request_token();
            data.pending += 1;
            self.shared.wake_pending.wait(&mut data);
            assert!(data.error.is_none(), "worker admission failed: {:?}", data.error);
            // Trust: the helper only offers a global credit. The runnable
            // thread commits it here, rather than while it sits in a queue.
            if let Some(token) = data.tokens.iter_mut().find(|token| !token.was_committed()) {
                assert!(token.commit(), "worker credit cancelled before dispatch");
            }
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn acquire_native(&self, registry: &Arc<native_park::Registry>) {
        if self.shared.workload {
            workload_proxy::acquire(self, registry);
            return;
        }
        let mut requested = false;
        loop {
            let admission = registry.enter().expect("native dispatch is parked or poisoned");
            let mut data = self.shared.data.lock();
            assert!(data.error.is_none(), "worker admission failed: {:?}", data.error);
            if !requested && data.used == 0 {
                assert_eq!(data.pending, 0);
                data.used = 1;
            } else if requested
                && native_park::reserved(&data).expect("native proxy accounting") > 0
            {
                if let Some(token) = data.tokens.iter_mut().find(|token| !token.was_committed()) {
                    assert!(token.commit(), "native worker credit cancelled before dispatch");
                }
            } else {
                if !requested {
                    self.request_token();
                    data.pending = data.pending.checked_add(1).expect("native pending overflow");
                    requested = true;
                }
                // Never reacquire the registry while holding ProxyData, and
                // never dispatch merely because a condvar woke spuriously.
                drop(admission);
                self.shared.wake_pending.wait(&mut data);
                drop(data);
                continue;
            }
            let active = data.active.as_mut().expect("native proxy tracking absent");
            let count = active.entry(std::thread::current().id()).or_default();
            *count = count.checked_add(1).expect("native active count overflow");
            return;
        }
    }

    /// Releases a token, possibly immediately giving it to some other thread as an optimization.
    /// Makes sure that the last token is never actually released to the wrapped jobserver.
    pub fn release_thread(&self) {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if self.shared.workload {
            workload_proxy::release(self);
            return;
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let _admission = self
            .shared
            .registry
            .as_ref()
            .map(|registry| registry.enter().expect("native release after unresolved loan"));
        let mut data = self.shared.data.lock();
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(active) = &mut data.active {
            let id = std::thread::current().id();
            let count = active.get_mut(&id).expect("native thread released without admission");
            *count = count.checked_sub(1).expect("native active count underflow");
            if *count == 0 {
                active.remove(&id);
            }
        }

        // Trust: do not perpetually hand a global credit between pending
        // workers. Returning it forces the next worker through live policy.
        if self._client.is_global() && data.used > 1 {
            data.used -= 1;
            let token = data.tokens.pop();
            drop(data);
            drop(token);
            return;
        }

        if data.pending > 0 {
            // Immediately give the released token to one of the waiting threads.
            data.pending -= 1;
            // Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): that thread's helper request
            // is now one more than anybody waits for. Left queued, the helper
            // would take a token out of the pool only to put it back, and
            // between the two the token exists nowhere but in that thread.
            // Every waiter files one request and every delivery or handoff
            // removes one waiter, so queued and in-flight requests never drop
            // below the number of waiters. A request the pipe helper is
            // already reading the pool for cannot be withdrawn; its token
            // comes back through the callback's "no longer needed" branch.
            if let Some(helper) = self.helper.lock().as_ref() {
                helper.cancel_request();
            }
            self.shared.wake_pending.notify_one();
        } else {
            data.used -= 1;

            // Release the token to the wrapped jobserver, unless it's the last one in the process.
            if data.used > 0 {
                let token = data.tokens.pop();
                drop(data);
                drop(token);
            }
        }
    }
}

#[cfg(test)]
#[path = "jobserver/tests.rs"]
mod tests;
