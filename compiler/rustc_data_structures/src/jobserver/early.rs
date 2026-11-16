//! Capture inherited custody at the official native entry, never at a late
//! embedding boundary where advertised descriptor numbers may have been reused.

#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::sync::Mutex;
use std::sync::OnceLock;

use jobserver_crate::Client as LocalClient;

struct Captured {
    client: Option<LocalClient>,
    // Refusal condition captured at FIRST entry, never downgraded by later env changes.
    strict: bool,
    // Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): `client` is this process's own
    // execution, lent to its in-process compiles, not inherited transport.
    lent: bool,
}
static CAPTURED: OnceLock<Result<Captured, String>> = OnceLock::new();
// A captured GNU client is not usable until the immediately following SDK
// capture completed too. In particular an SDK capture error poisons startup.
static COMPLETE: OnceLock<Result<(), String>> = OnceLock::new();
// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): set only when native entry admitted
// a strict process with no GNU scheduler as a bounded metadata query.
static ADMITTED_QUERY: OnceLock<()> = OnceLock::new();
// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): the one session such a process may
// answer on no scheduler. NOT_GRANTED, then GRANTED by the driver, then SPENT
// by the first session that reaches scheduler initialization, granted or not.
static BOUNDED_QUERY_SESSION: std::sync::atomic::AtomicU8 =
    std::sync::atomic::AtomicU8::new(QUERY_NOT_GRANTED);
const QUERY_NOT_GRANTED: u8 = 0;
const QUERY_GRANTED: u8 = 1;
const QUERY_SPENT: u8 = 2;

#[cfg(any(target_os = "linux", target_os = "macos"))]
struct WorkloadCpu {
    selected: bool,
    original: Mutex<Option<trust_resource_controller::client::workload::EarlyCpuSet>>,
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
static WORKLOAD_CPU: OnceLock<WorkloadCpu> = OnceLock::new();
#[cfg(any(target_os = "linux", target_os = "macos"))]
static HOST_STORE: OnceLock<
    Mutex<Option<trust_resource_controller::client::workload::EarlyHostStore>>,
> = OnceLock::new();
#[cfg(any(target_os = "linux", target_os = "macos"))]
static HOST_CONTROL: OnceLock<
    Mutex<Option<trust_resource_controller::client::workload::control_pin::EarlyHostControl>>,
> = OnceLock::new();

fn strict_context() -> bool {
    [
        jobserver_utils::DESCENDANT_HANDOFF_ENV,
        jobserver_utils::CPU_HANDOFF_ENV,
        "BUILD_SLOT_CPU_PROTOCOL",
        "TRUST_CPU_IMPLICIT_FD",
        "ATERM_SDK_LEASE_V3",
        "ATERM_WORKLOAD_CPU_FDS_V1",
        "ATERM_WORKLOAD_HOST_STORE_FD_V1",
        "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
    ]
    .iter()
    .any(|name| std::env::var_os(name).is_some())
}

/// FIRST official native-main operation, before logging, probes or callbacks.
/// This captures descriptors only; it confers no native Context/grant authority.
///
/// # Safety
/// No descriptor-opening operation or arbitrary callback may precede this call.
/// Only this fixed checked GNU importer may run between the SDK snapshot and
/// capture. The importer may allocate descriptors but must never close/reuse
/// the original SDK source; the maintained launcher maps it outside GNU targets.
pub unsafe fn capture() -> Result<(), String> {
    // SAFETY: forwarded; our caller guarantees genuine native entry.
    unsafe { capture_with(false) }
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): [`capture`] for a process that runs
/// the compiler in process and waits on each compile, such as a libtest binary
/// whose tests embed the driver. When [`own_execution_owed`] holds, nothing of
/// any kind was advertised to import, so the process lends the compiler its own
/// execution: an owned GNU pool holding ZERO tokens, so a compile runs only on
/// the implicit execution that the waiting test thread hands it. Otherwise this
/// is exactly [`capture`], refusals included. The caller must also bound its
/// own test threads to one; [`enter_lent_compile`] refuses a second compile
/// that overlaps another, and [`local`] refuses native worker custody on a loan.
///
/// # Safety
/// As [`capture`].
pub(super) unsafe fn capture_lending_own_execution() -> Result<(), String> {
    // SAFETY: forwarded; our caller guarantees genuine native entry.
    unsafe { capture_with(true) }
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): whether a process is owed a loan of
/// its own execution. It is when `build-slot` admitted it on protocol 1, the
/// fixed-width route that carries no GNU pool, and nothing else was advertised
/// to it: no GNU variable, no descendant handoff and no CPU, fixed-claim, SDK,
/// workload or Host control/store locator. Any of those is transport (or a dangling
/// claim to it) that [`capture`] must judge, never replace.
pub(super) fn own_execution_owed(var: impl Fn(&str) -> Option<std::ffi::OsString>) -> bool {
    let is_one = |name: &str| var(name).is_some_and(|value| value == "1");
    is_one("BUILD_SLOT_CPU_PROTOCOL")
        && is_one("BUILD_SLOT_HELD")
        && [
            jobserver_utils::DESCENDANT_HANDOFF_ENV,
            jobserver_utils::CPU_HANDOFF_ENV,
            jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            "TRUST_CPU_IMPLICIT_FD",
            "ATERM_SDK_LEASE_V3",
            "ATERM_WORKLOAD_CPU_FDS_V1",
            "ATERM_WORKLOAD_HOST_STORE_FD_V1",
            "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
        ]
        .iter()
        .all(|name| var(name).is_none())
}

unsafe fn capture_with(lend_own_execution: bool) -> Result<(), String> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let sdk = trust_resource_controller::client::sdk::snapshot_sdk_lease()
        .map_err(|error| error.to_string())?;
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let cpu = trust_resource_controller::client::workload::snapshot_cpu_set()
        .map_err(|error| error.to_string())?;
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let store = trust_resource_controller::client::workload::snapshot_host_store()
        .map_err(|error| error.to_string())?;
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let control = trust_resource_controller::client::workload::control_pin::snapshot_host_control()
        .map_err(|error| error.to_string())?;

    if CAPTURED.get().is_some() {
        return Err("compiler inherited custody was already captured".into());
    }
    // These environment observations open no descriptors. They are refusal
    // conditions only; none authenticates scheduling or memory authority.
    let strict = strict_context();
    let gnu_advertised = std::env::var_os(jobserver_utils::DESCENDANT_HANDOFF_ENV).is_some()
        || ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"]
            .iter()
            .any(|name| std::env::var_os(name).is_some());
    // Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): with nothing advertised there is
    // nothing to import. The loan is created where the importer would run: it
    // allocates descriptors, and closes or reuses none.
    let imported = if lend_own_execution && own_execution_owed(|name| std::env::var_os(name)) {
        LocalClient::new(0)
            .map(|client| Captured { client: Some(client), strict, lent: true })
            .map_err(|error| error.to_string())
    } else {
        // SAFETY: the official entry calls us first and only this fixed importer
        // executes after the SDK metadata snapshot, before SDK descriptor capture.
        unsafe { jobserver_utils::Jobserver::from_env_with_handoff() }
            .map(|server| server.map(|server| server.client().clone()))
            .map_err(|error| error.to_string())
            .and_then(|client| {
                if strict && gnu_advertised && client.is_none() {
                    Err("native/scoped compiler custody has no inherited GNU scheduler".into())
                } else {
                    Ok(Captured { client, strict, lent: false })
                }
            })
    };
    CAPTURED
        .set(imported)
        .map_err(|_| "compiler inherited custody was already captured".to_string())?;

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let completed = (|| {
        // SAFETY: since the no-allocation snapshots only the fixed checked GNU
        // importer and OnceLock publication ran. The native launcher maps SDK,
        // GNU and workload CPU sources disjointly; no callback can close/reuse
        // them. These operations run before threads or environment readers.
        unsafe { trust_resource_controller::client::sdk::capture_sdk_lease(sdk) }
            .map_err(|error| error.to_string())?;
        let original = unsafe { trust_resource_controller::client::workload::capture_cpu_set(cpu) }
            .map_err(|error| error.to_string())?;
        let store =
            unsafe { trust_resource_controller::client::workload::capture_host_store(store) }
                .map_err(|error| error.to_string())?;
        let control = unsafe {
            trust_resource_controller::client::workload::control_pin::capture_host_control(control)
        }
        .map_err(|error| error.to_string())?;
        let selected = original.is_present();
        WORKLOAD_CPU
            .set(WorkloadCpu { selected, original: Mutex::new(selected.then_some(original)) })
            .map_err(|_| "compiler workload custody was already captured".to_string())?;
        HOST_STORE
            .set(Mutex::new(Some(store)))
            .map_err(|_| "compiler host discovery was already captured".to_string())?;
        HOST_CONTROL
            .set(Mutex::new(Some(control)))
            .map_err(|_| "compiler host control originals were already captured".to_string())
    })();
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    let completed = Ok(());
    COMPLETE
        .set(completed)
        .map_err(|_| "compiler inherited custody completion was already recorded".to_string())?;
    COMPLETE
        .get()
        .ok_or("compiler custody capture did not finish")?
        .as_ref()
        .map_err(Clone::clone)?;
    let captured = CAPTURED
        .get()
        .ok_or("compiler custody capture is absent")?
        .as_ref()
        .map_err(Clone::clone)?;
    if captured.strict && captured.client.is_none() {
        if !bounded_metadata_args() {
            return Err("native compiler work has no captured inherited GNU scheduler".into());
        }
        // Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): recorded at FIRST entry,
        // from the process's own argv, and never set later.
        ADMITTED_QUERY
            .set(())
            .map_err(|_| "compiler bounded query admission was already recorded".to_string())?;
    }
    Ok(())
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): whether native entry admitted
/// this strict process, which captured no GNU scheduler, only because its
/// complete argv is a bounded metadata query. Such a process compiles nothing
/// and is owed no scheduler; it never gets one.
pub(super) fn admitted_bounded_query() -> bool {
    ADMITTED_QUERY.get().is_some()
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): grant the one session of an
/// admitted process that may be answered on no scheduler. Refused in any other
/// process, and once a grant was made or a session spent it.
pub(super) fn grant_bounded_query_session() -> Option<BoundedQueryGrant> {
    use std::sync::atomic::Ordering::SeqCst;
    (admitted_bounded_query()
        && BOUNDED_QUERY_SESSION
            .compare_exchange(QUERY_NOT_GRANTED, QUERY_GRANTED, SeqCst, SeqCst)
            .is_ok())
    // Lazily: a guard built and dropped for a refused grant would spend it.
    .then(|| BoundedQueryGrant(()))
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): a driver's grant, held for the
/// one session it was made for. Dropping it spends the grant, used or not, so
/// it cannot outlive its session, not even one that ended in a fatal error.
#[must_use = "dropping the grant spends it before the session can take it"]
pub struct BoundedQueryGrant(());

impl Drop for BoundedQueryGrant {
    fn drop(&mut self) {
        take_bounded_query_session();
    }
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): spend the process's one grant.
/// True only for the first caller, and only if the grant was made before it.
pub(super) fn take_bounded_query_session() -> bool {
    BOUNDED_QUERY_SESSION.swap(QUERY_SPENT, std::sync::atomic::Ordering::SeqCst) == QUERY_GRANTED
}

/// Consume only the FIRST-entry owned CPU set. Presence selects a route; it
/// grants nothing until the live registered-member SCM exchange authenticates
/// and transfers the original host descriptions. Never reread a late locator.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn take_workload_cpu()
-> Result<Option<trust_resource_controller::client::workload::EarlyCpuSet>, String> {
    COMPLETE
        .get()
        .ok_or("compiler early custody capture is incomplete")?
        .as_ref()
        .map_err(Clone::clone)?;
    let workload = WORKLOAD_CPU.get().ok_or("compiler workload capture is absent")?;
    if !workload.selected {
        return Ok(None);
    }
    workload
        .original
        .lock()
        .map_err(|_| "compiler workload custody is poisoned".to_string())?
        .take()
        .map(Some)
        .ok_or_else(|| "compiler original workload custody was already consumed".into())
}

/// Original independently configured host-store selection, consumed once.
/// The captured directory grants no resource; discovery still authenticates
/// the actual native ancestor and its retained backing. Never use invocation
/// metadata or a late environment lookup to select another host.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn take_host_store()
-> Result<trust_resource_controller::client::workload::EarlyHostStore, String> {
    COMPLETE
        .get()
        .ok_or("compiler early custody capture is incomplete")?
        .as_ref()
        .map_err(Clone::clone)?;
    HOST_STORE
        .get()
        .ok_or("compiler original host selection is absent")?
        .lock()
        .map_err(|_| "compiler original host selection is poisoned".to_string())?
        .take()
        .ok_or_else(|| "compiler original host selection was already consumed".into())
}

/// Actual workload members require the complete native control transfer. A
/// legacy directory alone must not reopen control state inside a closed child.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn take_host_controller(
    deadline: std::time::Instant,
) -> Result<trust_resource_controller::client::Client, String> {
    let store = take_host_store()?;
    let control = HOST_CONTROL
        .get()
        .ok_or("compiler control capture is absent")?
        .lock()
        .map_err(|_| "compiler control capture is poisoned".to_string())?
        .take()
        .ok_or("compiler control originals were already consumed")?;
    if WORKLOAD_CPU.get().is_some_and(|cpu| cpu.selected) && !control.is_present() {
        return Err("admitted compiler has no inherited original Host control pin".into());
    }
    store.discover_with_control(control, deadline).map_err(|error| error.to_string())
}

fn bounded_metadata_args() -> bool {
    // Native argv observation only, AFTER original SDK/GNU capture. Never
    // expand an argfile or accept extra flags as a metadata capability.
    bounded_metadata_query(std::env::args_os().skip(1))
}

/// Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): the complete argv (program name
/// excluded) of a query that prints fixed compiler metadata and compiles
/// nothing. getopts reads `-V` as the short spelling of `--version` and
/// `--print sysroot` as the separated spelling of `--print=sysroot`: one
/// option, the same printed line. Cargo's `#[cargo_test]` macro asks `rustc -V`;
/// toolchain discovery asks `rustc --print sysroot`. Nothing else is admitted:
/// no second query, no input, no flag, no argfile, no combined short options.
pub(super) fn bounded_metadata_query(args: impl IntoIterator<Item = std::ffi::OsString>) -> bool {
    let args: Vec<_> = args.into_iter().take(3).collect();
    let args: Vec<_> = args.iter().map(|arg| arg.to_str()).collect();
    matches!(
        args.as_slice(),
        [Some(
            "-V" | "-vV"
                | "--version"
                | "--print=sysroot"
                | "--print=target-list"
                | "--resource-capabilities"
        )] | [Some("--print"), Some("sysroot" | "target-list")]
    )
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): whether this process captured a loan
/// of its own execution rather than inherited transport.
pub(super) fn lent_own_execution() -> bool {
    CAPTURED.get().and_then(|captured| captured.as_ref().ok()).is_some_and(|captured| captured.lent)
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): held for one whole compile while this
/// process runs on a loan of its own execution.
#[must_use = "dropping it ends the compile's hold on the lent execution"]
pub struct LentCompile {
    _one: std::sync::MutexGuard<'static, ()>,
}

/// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): enter a compile. Without a loan this
/// is `None`. On a loan only one compile may run at a time, since every compile
/// would run on its own implicit execution and the loan has only the one the
/// waiting test thread hands over: an overlapping compile (another thread's, or
/// one nested inside a compile) refuses rather than waits, which could deadlock.
pub(super) fn enter_lent_compile() -> Result<Option<LentCompile>, String> {
    static ONE_LENT_COMPILE: std::sync::Mutex<()> = std::sync::Mutex::new(());
    if !lent_own_execution() {
        return Ok(None);
    }
    match ONE_LENT_COMPILE.try_lock() {
        Ok(one) => Ok(Some(LentCompile { _one: one })),
        // A compile that unwound released the execution it held.
        Err(std::sync::TryLockError::Poisoned(one)) => {
            Ok(Some(LentCompile { _one: one.into_inner() }))
        }
        Err(std::sync::TryLockError::WouldBlock) => {
            Err("a lent test execution runs one compile at a time, and another compile in this \
             process holds it"
                .into())
        }
    }
}

pub(super) fn local(limit: usize, worker_v2: bool) -> Result<LocalClient, String> {
    let mut original_strict = false;
    if let Some(captured) = CAPTURED.get() {
        COMPLETE
            .get()
            .ok_or("compiler early custody capture is incomplete")?
            .as_ref()
            .map_err(Clone::clone)?;
        match captured {
            Ok(captured) => {
                if let Some(client) = &captured.client {
                    // Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): a loan of one
                    // waiting execution carries no native worker custody.
                    if captured.lent && worker_v2 {
                        return Err("a lent test execution carries no native worker custody".into());
                    }
                    return Ok(client.clone());
                }
                original_strict = captured.strict;
            }
            Err(error) => return Err(error.clone()),
        }
    } else if strict_context()
        || ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"]
            .iter()
            .any(|name| std::env::var_os(name).is_some())
    {
        // Embeddings can enter after arbitrary descriptor activity. Never
        // assert the native early-capture precondition or reimport raw numbers.
        return Err("inherited compiler scheduler requires capture at native process entry".into());
    }
    if worker_v2 || original_strict || strict_context() {
        return Err("native compiler worker has no captured inherited GNU scheduler".into());
    }
    if limit == 0 {
        return Err("private compiler scheduler requires a nonzero limit".into());
    }
    // Ordinary truly no-context compiler/embedding retains its CLI-sized
    // private scheduler and the existing permanently held implicit token.
    let client = LocalClient::new(limit).map_err(|error| error.to_string())?;
    client.acquire_raw().map_err(|error| error.to_string())?;
    Ok(client)
}
