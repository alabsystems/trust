use cargo_util::{ProcessBuilder, ProcessError};
use cargo_util_schemas::manifest::StringOrVec;
use cargo_util_terminal::Shell;
use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitStatus;
use targo::util::{self, CargoResult, closest_msg, command_prelude};
use targo::workspace::features;

mod cli;
mod commands;
// Trust: the toolchain owns native invocation admission policy.
mod resource_capabilities;
// Trust: build-tree administration is part of this program, before aliases.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod repo_lock;
// Trust: the maintained Bootstrap engine stays inside this SAME managed image.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod bootstrap_runtime;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_fixed;
// Trust: manual cache cleanup runs the existing native Bootstrap judge.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_prune;

use crate::command_prelude::*;
use targo::util::file_identity::{
    OpenedFileIdentity, metadata_is_plain_file, opened_file_identity,
};

// A support declaration only. Host pre-GO reads this original image section;
// native loaded-image/no-fork and authenticated live Ready remain mandatory.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct ResolverProtocolDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_resolve")]
static RESOLVER_PROTOCOL_DECLARATION: ResolverProtocolDeclaration =
    ResolverProtocolDeclaration(targo::resolver_service::PROTOCOL_MARKER);

// Separate support declaration only; no saved marker/field grants custody.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct WorkloadProtocolDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_workload")]
static WORKLOAD_PROTOCOL_DECLARATION: WorkloadProtocolDeclaration =
    WorkloadProtocolDeclaration(targo::workload_service::PROTOCOL_MARKER);

// Support declaration only. V1 startup remains full-width; partial return
// additionally requires the original live Host/SDK, retained bank and SAME
// GNU escrow. Reading these bytes creates no admission or capacity owner.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct PartialCpuProtocolDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_partial")]
static PARTIAL_CPU_PROTOCOL_DECLARATION: PartialCpuProtocolDeclaration =
    PartialCpuProtocolDeclaration(trust_resource_controller::workload::PARTIAL_CPU_PROTOCOL_MARKER);

// Distinct paired protocol declaration only. Actual original root/SDK/all-N
// startup and live Ready48/v2 remain mandatory before project configuration.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct PairedProtocolDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_pairqual")]
static PAIRED_PROTOCOL_DECLARATION: PairedProtocolDeclaration =
    PairedProtocolDeclaration(targo::paired_service::PROTOCOL_MARKER);

// Trust: a distinct full general-DAG declaration. Actual live original SDK,
// all-N resources, input/output owners and Ready48/v3 remain mandatory.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct NativeJobProtocolDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_jobroot")]
static NATIVE_JOB_PROTOCOL_DECLARATION: NativeJobProtocolDeclaration =
    NativeJobProtocolDeclaration(targo::native_job_service::PROTOCOL_MARKER);

// Support for the exact original-root graph transport and first native object
// leaf only. The compiled entry still requires live Host/GNU/SDK/Manager/output
// owners and rejects every other producing selection before Steps. This image
// declaration grants no SDK provenance, Ready, CPU, input or release authority.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct BootstrapGraphProtocolDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_bgraph")]
static BOOTSTRAP_GRAPH_PROTOCOL_DECLARATION: BootstrapGraphProtocolDeclaration =
    BootstrapGraphProtocolDeclaration(
        trust_resource_controller::bootstrap_graph::BOOTSTRAP_GRAPH_PROTOCOL_MARKER,
    );

fn main() {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    std::hint::black_box(&PARTIAL_CPU_PROTOCOL_DECLARATION);
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if let Some(code) =
        trust_build_tree::admission::cache_probe::private_entry(std::env::args_os().skip(1))
    {
        std::process::exit(code);
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if bootstrap_runtime::selected_at_entry(std::env::args_os().skip(1)) {
        // SAFETY: original native entry, before descriptor imports, file
        // creation or threads. Argument inspection allocates no descriptors.
        // Frontend/Host authentication remains mandatory before engine entry.
        unsafe { bootstrap::native_entry::clamp_creation_mask_at_entry() };
    }
    // Store7 is independent original Host discovery data. Snapshot before ANY
    // GNU/SDK import can allocate/reuse a closed advertised slot.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    let bootstrap_store_capture =
        match bootstrap_runtime::snapshot_original_store_at_entry(std::env::args_os().skip(1)) {
            Ok(capture) => capture,
            Err(error) => {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
        };
    // Trust: observation only, before GNU/SDK allocation can reuse a closed
    // fixed packet/original slot. The actual checked importer runs later.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let fixed_exec_capture =
        match resource_fixed::snapshot_exec(&std::env::args_os().skip(1).collect::<Vec<_>>()) {
            Ok(capture) => capture,
            Err(error) => {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
        };
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let nested_fixed_capture =
        match resource_fixed::snapshot_nested(&std::env::args_os().skip(1).collect::<Vec<_>>()) {
            Ok(capture) => capture,
            Err(error) => {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
        };
    // Snapshot only native metadata: no descriptor allocation before the GNU
    // import can validate its original numeric slots. The host maps SDK and
    // scheduler/bootstrap targets disjointly before GO.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let sdk_capture = match targo::snapshot_sdk_lease() {
        Ok(capture) => capture,
        Err(error) => {
            let mut shell = Shell::new();
            targo::exit_with_error(error.into(), &mut shell);
        }
    };
    #[cfg(unix)]
    let workload_capture =
        match targo::workload_service::snapshot_bootstrap(std::env::args_os().nth(1).as_deref()) {
            Ok(capture) => capture,
            Err(error) => {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
        };
    // Trust: checked descriptor ownership must precede logging and frontend /
    // proxy authentication, which open files and sockets. Do not rewrite the
    // original environment: incoming fix-proxy claims authenticate its bytes.
    // SAFETY: this is the native CLI's first descriptor-import operation;
    // the preceding SDK snapshot allocates no descriptors.
    if let Err(error) = unsafe { targo::context::initialize_jobserver() } {
        let mut shell = Shell::new();
        targo::exit_with_error(error.into(), &mut shell);
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    // SAFETY: only the fixed early scheduler importer ran after the snapshot;
    // no logger, callback, configuration or probe can have reused the SDK slot.
    if let Err(error) = unsafe { targo::capture_sdk_lease(sdk_capture) } {
        let mut shell = Shell::new();
        targo::exit_with_error(error.into(), &mut shell);
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    // SAFETY: all sources were snapshotted first. Only disjoint GNU3/4 and
    // SDK5 importers ran; no logger/config/callback/thread can have reused7.
    let bootstrap_store = match unsafe {
        trust_resource_controller::client::bootstrap_graph::capture_host_store(
            bootstrap_store_capture,
        )
    } {
        Ok(original) => original,
        Err(error) => {
            let mut shell = Shell::new();
            targo::exit_with_error(error.into(), &mut shell);
        }
    };
    #[cfg(unix)]
    // SAFETY: original SDK/workload locators were snapshotted before any FD
    // allocation; only the fixed GNU/SDK importers ran. Their mapped sources
    // are disjoint, and no config/logger/callback/thread can have reused them.
    let workload_bootstrap =
        match unsafe { targo::workload_service::capture_bootstrap(workload_capture) } {
            Ok(capture) => capture,
            Err(error) => {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
        };
    targo::initialize_build_metadata();
    let _guard = setup_logger();

    // Trust: this binary is installed under two names with different authority.
    // Which one was invoked has to be settled before anything reads argv or
    // configuration, because every later decision keys off it.
    if let Err(error) = targo::validate_frontend_invocation() {
        let mut shell = Shell::new();
        targo::exit_with_error(
            anyhow::format_err!("could not authenticate Cargo/Targo frontend identity: {error}")
                .into(),
            &mut shell,
        );
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if bootstrap_runtime::selected_at_entry(std::env::args_os().skip(1))
        && !targo::is_targo_invocation()
    {
        let mut shell = Shell::new();
        targo::exit_with_error(
            anyhow::anyhow!("original Bootstrap graph requires the actual Targo frontend").into(),
            &mut shell,
        );
    }

    // Distinct live cooperative workload entry before aliases, project
    // configuration, completion handling or compiler queries. Older images
    // have no declaration; supported images still require actual48/49, same
    // original SDK/full canonical CPU set/output and the mandatory executor.
    #[cfg(unix)]
    {
        let args = std::env::args_os().skip(1).collect::<Vec<_>>();
        let requested = targo::is_targo_invocation() && targo::workload_service::requested(&args);
        let paired_requested =
            targo::is_targo_invocation() && targo::paired_service::requested(&args);
        let native_job_requested =
            targo::is_targo_invocation() && targo::native_job_service::requested(&args);
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let coordinator_requested = targo::is_targo_invocation()
            && targo::compiler::candidate_coordinator::requested(&args);
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let coordinator_requested = false;
        if workload_bootstrap.is_present()
            && !requested
            && !paired_requested
            && !native_job_requested
            && !coordinator_requested
        {
            let mut shell = Shell::new();
            targo::exit_with_error(
                anyhow::anyhow!(
                    "original workload bootstrap cannot enter another frontend purpose"
                )
                .into(),
                &mut shell,
            );
        }
        if native_job_requested {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            std::hint::black_box(&NATIVE_JOB_PROTOCOL_DECLARATION);
            if let Err(error) = targo::native_job_service::run(&args, workload_bootstrap, || {
                configure_trust_execution_policy("build", false, true)
            }) {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            return;
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if coordinator_requested {
            if let Err(error) =
                targo::compiler::candidate_coordinator::run(&args, workload_bootstrap, || {
                    configure_trust_execution_policy("build", false, true)
                })
            {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            return;
        }
        if paired_requested {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            std::hint::black_box(&PAIRED_PROTOCOL_DECLARATION);
            if let Err(error) = targo::paired_service::run(&args, workload_bootstrap, || {
                configure_trust_execution_policy("test", false, true)
            }) {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            return;
        }
        if requested {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            std::hint::black_box(&WORKLOAD_PROTOCOL_DECLARATION);
            if let Err(error) = targo::workload_service::run(&args, workload_bootstrap, || {
                configure_trust_execution_policy("test", false, true)
            }) {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            return;
        }
    }

    // Trust: this closed in-process producer route precedes aliases/project
    // configuration. It never executes a standalone Bootstrap image.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if targo::is_targo_invocation() {
        let args = std::env::args_os().skip(1).collect::<Vec<_>>();
        if let Some(result) = bootstrap_runtime::dispatch(&args, bootstrap_store) {
            if let Err(error) = result {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            return;
        }
    }

    // Trust: standalone native fixed admission precedes project configuration.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    if targo::is_targo_invocation() {
        let args = std::env::args_os().skip(1).collect::<Vec<_>>();
        if let Some(result) =
            resource_fixed::dispatch(&args, fixed_exec_capture, nested_fixed_capture)
        {
            match result {
                Ok(code) => std::process::exit(code),
                Err(error) => {
                    let mut shell = Shell::new();
                    targo::exit_with_error(error.into(), &mut shell);
                }
            }
        }
    }

    // Trust: exact read-only capability query. Keep it before configuration,
    // private root sockets, aliases and any build/proof operation.
    if targo::is_targo_invocation()
        && resource_capabilities::respond(&std::env::args_os().skip(1).collect::<Vec<_>>())
    {
        return;
    }

    // Distinct native full resolver entry before project/config/lane parsing.
    #[cfg(unix)]
    if targo::is_targo_invocation()
        && targo::resolver_service::requested(&std::env::args_os().skip(1).collect::<Vec<_>>())
    {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        std::hint::black_box(&RESOLVER_PROTOCOL_DECLARATION);
        if let Err(error) =
            targo::resolver_service::run(&std::env::args_os().skip(1).collect::<Vec<_>>(), || {
                configure_trust_execution_policy("metadata", false, false)
            })
        {
            let mut shell = Shell::new();
            targo::exit_with_error(error.into(), &mut shell);
        }
        return;
    }

    // Trust: closed metadata requests use the already captured SDK/GNU owners.
    #[cfg(unix)]
    if targo::is_targo_invocation()
        && targo::metadata_service::requested(&std::env::args_os().skip(1).collect::<Vec<_>>())
    {
        if let Err(error) =
            targo::metadata_service::run(&std::env::args_os().skip(1).collect::<Vec<_>>())
        {
            let mut shell = Shell::new();
            targo::exit_with_error(error.into(), &mut shell);
        }
        return;
    }

    // Retain the original verified compiler child before any project code or
    // configuration can run. The private argv selector is not authority: the
    // protocol must capture the actual socket and authenticate its session.
    let retained_test = match capture_retained_test() {
        Ok(endpoint) => endpoint,
        Err(error) => {
            let mut shell = Shell::new();
            targo::exit_with_error(error.into(), &mut shell);
        }
    };

    // Trust: own and contain the actual private root socket before aliases,
    // project configuration, completion handling or any configured child exec.
    let root_control = match capture_root_control() {
        Ok(control) => control,
        Err(error) => {
            let mut shell = Shell::new();
            targo::exit_with_error(error.into(), &mut shell);
        }
    };

    // Trust: `cargo fix` re-enters this executable as a rustc proxy. An ambient
    // `__CARGO_FIX_PLZ` used to bypass CLI lane selection entirely. Authenticate
    // the branded parent handoff before configuration, completion handling, or
    // argv-selected compiler parsing. Ordinary Cargo retains its upstream
    // marker behavior.
    let fix_proxy_lock_addr = targo::ops::prepare_fix_proxy_dispatch().unwrap_or_else(|error| {
        let mut shell = Shell::new();
        targo::exit_with_error(error.into(), &mut shell)
    });

    // Trust: `$CARGO` descendants of an explicitly unverified Targo build
    // re-enter this binary without the ancestor's CLI arguments. Authenticate
    // a live exchange with that exact ancestor before project/user
    // configuration can influence command parsing. The socket address is
    // inert: one that does not authenticate grants nothing, and only a compile
    // verb naming no lane is then refused (T14c, T14-EXPORT-1). What stops
    // startup here is an internal invariant, never the endpoint.
    if let Err(error) = targo::prepare_nested_unverified_targo_handoff() {
        let mut shell = Shell::new();
        targo::exit_with_error(
            anyhow::format_err!(
                "could not authenticate nested-unverified Targo authority: {error}"
            )
            .into(),
            &mut shell,
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    if targo::is_targo_invocation() {
        let args = std::env::args_os().skip(1).collect::<Vec<_>>();
        if repo_lock::requested(&args) {
            if retained_test.is_some() || root_control.is_some() || fix_proxy_lock_addr.is_some() {
                let mut shell = Shell::new();
                targo::exit_with_error(
                    anyhow::anyhow!(
                        "native build-tree administration cannot replace an original retained, root-control or fix-proxy purpose"
                    )
                    .into(),
                    &mut shell,
                );
            }
            std::process::exit(i32::from(repo_lock::run(&args)));
        }
    }

    let mut gctx = match GlobalContext::default() {
        Ok(gctx) => gctx,
        Err(e) => {
            let mut shell = Shell::new();
            targo::exit_with_error(e.into(), &mut shell)
        }
    };
    #[cfg(unix)]
    if let Some(endpoint) = retained_test {
        if fix_proxy_lock_addr.is_some() {
            targo::exit_with_error(
                anyhow::anyhow!("retained tests cannot enter a fix proxy").into(),
                &mut *gctx.shell(),
            );
        }
        if let Err(error) = gctx.install_retained_test(endpoint) {
            targo::exit_with_error(error.into(), &mut *gctx.shell());
        }
    }
    if let Some(control) = root_control {
        if fix_proxy_lock_addr.is_some() {
            targo::exit_with_error(
                anyhow::anyhow!("private root control cannot enter a fix proxy").into(),
                &mut *gctx.shell(),
            );
        }
        if let Err(error) = gctx.install_root_control(control) {
            targo::exit_with_error(error.into(), &mut *gctx.shell());
        }
    }

    let nightly_features_allowed =
        features::nightly_features_allowed_on_channel(&features::channel());
    if nightly_features_allowed {
        let _span = tracing::span!(tracing::Level::TRACE, "completions").entered();
        let args = std::env::args_os();
        let current_dir = std::env::current_dir().ok();
        let completer = clap_complete::CompleteEnv::with_factory(|| {
            let mut gctx = GlobalContext::default().expect("already loaded without errors");
            cli::cli(&mut gctx)
        })
        .var("CARGO_COMPLETE");
        if completer
            .try_complete(args, current_dir.as_deref())
            .unwrap_or_else(|e| {
                let mut shell = Shell::new();
                targo::exit_with_error(e.into(), &mut shell)
            })
        {
            return;
        }
    }

    let result = if let Some(lock_addr) = fix_proxy_lock_addr {
        targo::ops::fix_exec_rustc(&gctx, &lock_addr).map_err(|e| CliError::from(e))
    } else {
        let _token = targo::util::job::setup();
        cli::main(&mut gctx)
    };

    #[cfg(unix)]
    {
        let completed = match gctx.take_completed_retained_test_endpoint() {
            Ok(endpoint) => endpoint,
            Err(error) if result.is_ok() => {
                targo::exit_with_error(error.into(), &mut *gctx.shell());
            }
            // A startup/compiler failure retains the initial endpoint in gctx
            // and follows its original error path without a completion claim.
            Err(_) => None,
        };
        if let Some(mut endpoint) = completed {
            if !endpoint.was_granted() {
                match result {
                    Err(error) => targo::exit_with_error(error, &mut *gctx.shell()),
                    Ok(()) => targo::exit_with_error(
                        anyhow::anyhow!("retained command succeeded without execution authority")
                            .into(),
                        &mut *gctx.shell(),
                    ),
                }
            }
            match endpoint.poll_parent_closed() {
                Ok(false) => {}
                result => {
                    let error = match result {
                        Ok(true) => std::io::Error::other(
                            "retained controller closed before command completion",
                        ),
                        Err(error) => error,
                        Ok(false) => unreachable!(),
                    };
                    targo::exit_with_error(error.into(), &mut *gctx.shell());
                }
            }
            let exit_code = match result {
                Ok(()) => 0,
                Err(error) => targo::report_cli_error(error, &mut *gctx.shell()),
            };
            // Keep original endpoint custody through all normal destructors
            // and reporting, including a settled failing harness. Only kernel
            // process exit closes it; no Rust cleanup emits an early EOF.
            drop(gctx);
            drop(_guard);
            use std::io::Write as _;
            if let Err(error) = std::io::stdout()
                .flush()
                .and_then(|()| std::io::stderr().flush())
            {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            // This reports settlement, never an ExitStatus or favorable proof.
            // The parent still observes this original child's actual code.
            if let Err(error) = endpoint.publish_drained(endpoint.deadline()) {
                let mut shell = Shell::new();
                targo::exit_with_error(error.into(), &mut shell);
            }
            let _endpoint_through_os_exit = endpoint;
            std::process::exit(exit_code);
        }
    }
    match result {
        Err(error) => targo::exit_with_error(error, &mut *gctx.shell()),
        Ok(()) => {}
    }
}

fn retained_test_requested(
    args: impl IntoIterator<Item = std::ffi::OsString>,
) -> std::io::Result<bool> {
    let args: Vec<_> = args.into_iter().take_while(|arg| arg != "--").collect();
    let count = args
        .iter()
        .filter(|arg| *arg == "--__retained-test-session")
        .count();
    if count == 0 {
        return Ok(false);
    }
    if count != 1
        || args.first().is_none_or(|arg| arg != "test")
        || !args.iter().any(|arg| arg == "--no-run")
        || args
            .iter()
            .any(|arg| arg == "--__resource-root-control" || arg == "--unverified")
    {
        return Err(std::io::Error::other(
            "retained tests require the original verified test --no-run command and exclusive stdin custody",
        ));
    }
    Ok(true)
}

#[cfg(unix)]
#[expect(
    clippy::disallowed_methods,
    reason = "retained-test stdin custody must reject the live proxy selector before project configuration or an environment snapshot can replace that authorization input"
)]
fn capture_retained_test() -> std::io::Result<Option<trust_test_execution::retained::RetainedChild>>
{
    if !retained_test_requested(std::env::args_os().skip(1))? {
        return Ok(None);
    }
    if !targo::is_targo_invocation() || std::env::var_os("__CARGO_FIX_PLZ").is_some() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "retained tests require genuine Targo and exclusive non-proxy stdin",
        ));
    }
    // This captures inert socket custody only. The ordinary CLI dispatcher
    // remains the single owner of verified loader/policy initialization before
    // configuration; the retained route is checked there after authentication.
    trust_test_execution::retained::RetainedChild::capture_stdin(
        std::time::Instant::now() + std::time::Duration::from_secs(10),
    )
    .map(Some)
}

/// Capturing stdin never grants a lane. Rebind that original custody to the
/// actual native command only after the one ordinary policy initializer ran.
pub(crate) fn validate_retained_test_dispatch(
    captured: bool,
    verified: bool,
    command: &str,
    private_compile_route: bool,
    original_unverified: bool,
) -> CargoResult<()> {
    if captured {
        anyhow::ensure!(
            verified && command == "test" && private_compile_route && !original_unverified,
            "retained endpoint requires authenticated verified native test --no-run dispatch"
        );
    }
    Ok(())
}

#[cfg(not(unix))]
fn capture_retained_test() -> std::io::Result<Option<()>> {
    if retained_test_requested(std::env::args_os().skip(1))? {
        return Err(std::io::Error::other(
            "retained verified tests require Unix socket custody",
        ));
    }
    Ok(None)
}

// Trust: this is a narrow original-argv selector for the helper's fixed command,
// not a second Cargo parser. It neither follows aliases nor reads configuration.
fn root_control_requested(
    args: impl IntoIterator<Item = std::ffi::OsString>,
) -> std::io::Result<bool> {
    let args: Vec<_> = args.into_iter().take_while(|arg| arg != "--").collect();
    let count = args
        .iter()
        .filter(|arg| *arg == "--__resource-root-control")
        .count();
    if count == 0 {
        return Ok(false);
    }
    if count != 1
        || args.first().is_none_or(|arg| arg != "--unverified")
        || args.get(1).is_none_or(|arg| arg != "build")
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "private root control requires the original --unverified build command",
        ));
    }
    Ok(true)
}

fn capture_root_control() -> std::io::Result<Option<targo::context::root_control::RootControl>> {
    if !root_control_requested(std::env::args_os().skip(1))? {
        return Ok(None);
    }
    if !targo::is_targo_invocation() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "private root control requires genuine Targo",
        ));
    }
    targo::context::root_control::RootControl::capture_stdin().map(Some)
}

#[cfg(test)]
mod root_control_argv_tests {
    use super::{retained_test_requested, root_control_requested, validate_retained_test_dispatch};

    fn args(args: &[&str]) -> Vec<std::ffi::OsString> {
        args.iter()
            .map(|arg| std::ffi::OsString::from(*arg))
            .collect()
    }

    #[test]
    fn captured_endpoint_is_inert_until_the_single_dispatch_policy_authenticates() {
        assert!(validate_retained_test_dispatch(true, true, "test", true, false).is_ok());
        // A real endpoint or a private CLI spelling cannot replace verified
        // loader authentication, change command, or select an unverified lane.
        for (verified, command, private_route, unverified) in [
            (false, "test", true, false),
            (true, "build", true, false),
            (true, "test", false, false),
            (true, "test", true, true),
        ] {
            assert!(
                validate_retained_test_dispatch(true, verified, command, private_route, unverified)
                    .is_err()
            );
        }
        assert!(validate_retained_test_dispatch(false, false, "build", false, true).is_ok());
    }

    #[test]
    fn retained_test_custody_requires_original_verified_compile_route() {
        assert!(
            retained_test_requested(args(&["test", "--no-run", "--__retained-test-session"]))
                .unwrap()
        );
        for input in [
            vec![
                "--unverified",
                "test",
                "--no-run",
                "--__retained-test-session",
            ],
            vec!["test", "--__retained-test-session"],
            vec!["build", "--no-run", "--__retained-test-session"],
            vec![
                "test",
                "--no-run",
                "--__retained-test-session",
                "--__resource-root-control",
            ],
            vec![
                "test",
                "--no-run",
                "--__retained-test-session",
                "--__retained-test-session",
            ],
        ] {
            assert!(retained_test_requested(args(&input)).is_err(), "{input:?}");
        }
        assert!(
            !retained_test_requested(args(&["test", "--", "--__retained-test-session"])).unwrap()
        );
    }

    #[test]
    fn private_socket_selectors_treat_libtest_passthrough_as_opaque() {
        let tail = [
            "--",
            "--skip",
            "--__retained-test-session",
            "--skip",
            "--__resource-root-control",
        ];
        let mut ordinary = vec!["test", "--no-run"];
        ordinary.extend(tail);
        assert!(!retained_test_requested(args(&ordinary)).unwrap());
        assert!(!root_control_requested(args(&ordinary)).unwrap());
        let mut retained = vec!["test", "--no-run", "--__retained-test-session"];
        retained.extend(tail);
        assert!(retained_test_requested(args(&retained)).unwrap());
        assert!(!root_control_requested(args(&retained)).unwrap());
        let mut controlled = vec!["--unverified", "build", "--__resource-root-control"];
        controlled.extend(tail);
        assert!(root_control_requested(args(&controlled)).unwrap());
        assert!(!retained_test_requested(args(&controlled)).unwrap());
    }

    #[test]
    fn root_control_requires_original_build_and_stops_at_the_delimiter() {
        assert!(
            root_control_requested(args(&[
                "--unverified",
                "build",
                "--offline",
                "--__resource-root-control"
            ]))
            .unwrap()
        );
        assert!(
            !root_control_requested(args(&[
                "--unverified",
                "build",
                "--",
                "--__resource-root-control"
            ]))
            .unwrap()
        );
        assert!(!root_control_requested(args(&["build", "--offline"])).unwrap());
        assert!(
            root_control_requested(args(&[
                "--unverified",
                "check",
                "--__resource-root-control"
            ]))
            .is_err()
        );
        assert!(root_control_requested(args(&["build", "--__resource-root-control"])).is_err());
        assert!(
            root_control_requested(args(&[
                "--unverified",
                "build",
                "--__resource-root-control",
                "--__resource-root-control"
            ]))
            .is_err()
        );
    }
}

fn setup_logger() -> Option<ChromeFlushGuard> {
    use tracing_subscriber::prelude::*;

    let env = tracing_subscriber::EnvFilter::from_env("CARGO_LOG");
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_timer(tracing_subscriber::fmt::time::Uptime::default())
        .with_ansi(std::io::IsTerminal::is_terminal(&std::io::stderr()))
        .with_writer(std::io::stderr)
        .with_filter(env);

    let (profile_layer, profile_guard) = chrome_layer();

    let registry = tracing_subscriber::registry()
        .with(fmt_layer)
        .with(profile_layer);
    registry.init();
    tracing::trace!(start = jiff::Timestamp::now().to_string());
    profile_guard
}

#[cfg(target_has_atomic = "64")]
type ChromeFlushGuard = tracing_chrome::FlushGuard;
#[cfg(target_has_atomic = "64")]
fn chrome_layer<S>() -> (
    Option<tracing_chrome::ChromeLayer<S>>,
    Option<ChromeFlushGuard>,
)
where
    S: tracing::Subscriber
        + for<'span> tracing_subscriber::registry::LookupSpan<'span>
        + Send
        + Sync,
{
    #![expect(clippy::disallowed_methods, reason = "runs before config is loaded")]
    if env_to_bool(std::env::var_os("CARGO_LOG_PROFILE").as_deref()) {
        let capture_args =
            env_to_bool(std::env::var_os("CARGO_LOG_PROFILE_CAPTURE_ARGS").as_deref());
        let (layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
            .include_args(capture_args)
            .build();
        (Some(layer), Some(guard))
    } else {
        (None, None)
    }
}

#[cfg(not(target_has_atomic = "64"))]
type ChromeFlushGuard = ();
#[cfg(not(target_has_atomic = "64"))]
fn chrome_layer() -> (
    Option<tracing_subscriber::layer::Identity>,
    Option<ChromeFlushGuard>,
) {
    (None, None)
}

fn env_to_bool(os: Option<&OsStr>) -> bool {
    match os.and_then(|os| os.to_str()) {
        Some("1") | Some("true") => true,
        _ => false,
    }
}

/// Table for defining the aliases which come builtin in `Cargo`.
/// The contents are structured as: `(alias, aliased_command, description)`.
const BUILTIN_ALIASES: [(&str, &str, &str); 6] = [
    ("b", "build", "alias: build"),
    ("c", "check", "alias: check"),
    ("d", "doc", "alias: doc"),
    ("r", "run", "alias: run"),
    ("t", "test", "alias: test"),
    ("rm", "remove", "alias: remove"),
];

/// Function which contains the list of all of the builtin aliases and it's
/// corresponding execs represented as &str.
fn builtin_aliases_execs(cmd: &str) -> Option<&(&str, &str, &str)> {
    BUILTIN_ALIASES.iter().find(|alias| alias.0 == cmd)
}

/// Resolve the aliased command from the [`GlobalContext`] with a given command string.
///
/// The search fallback chain is:
///
/// 1. Get the aliased command as a string.
/// 2. If an `Err` occurs (missing key, type mismatch, or any possible error),
///    try to get it as an array again.
/// 3. If still cannot find any, finds one insides [`BUILTIN_ALIASES`].
fn aliased_command(gctx: &GlobalContext, command: &str) -> CargoResult<Option<Vec<String>>> {
    // Trust: these names are security boundaries in the branded frontend, so
    // upstream's "user alias wins" rule is inverted for them. They must resolve
    // to the tool shipped beside the selected `targo`, never to a
    // workspace/CARGO_HOME alias an untrusted checkout can supply.
    if !user_alias_allowed_for_invocation(targo::is_targo_invocation(), command) {
        return Ok(None);
    }
    let alias_name = format!("alias.{}", command);
    let user_alias = match gctx.get_string(["alias", command]) {
        Ok(Some(record)) => Some(
            record
                .val
                .split_whitespace()
                .map(|s| s.to_string())
                .collect(),
        ),
        Ok(None) => None,
        Err(_) => gctx.get::<Option<Vec<String>>>(["alias", command])?,
    };

    let result = user_alias.or_else(|| {
        builtin_aliases_execs(command).map(|command_str| vec![command_str.1.to_string()])
    });
    if result
        .as_ref()
        .map(|alias| alias.is_empty())
        .unwrap_or_default()
    {
        anyhow::bail!("subcommand is required, but `{alias_name}` is empty");
    }
    Ok(result)
}

/// List all runnable commands
fn list_commands(gctx: &GlobalContext) -> BTreeMap<String, CommandInfo> {
    let mut commands = third_party_subcommands(gctx);

    for cmd in commands::builtin() {
        commands.insert(
            cmd.get_name().to_string(),
            CommandInfo::BuiltIn {
                about: cmd.get_about().map(|s| s.to_string()),
            },
        );
    }

    // Add the builtin_aliases and them descriptions to the
    // `commands` `BTreeMap`.
    for command in &BUILTIN_ALIASES {
        commands.insert(
            command.0.to_string(),
            CommandInfo::BuiltIn {
                about: Some(command.2.to_string()),
            },
        );
    }

    // Add the user-defined aliases
    let alias_commands = user_defined_aliases(gctx);
    commands.extend(alias_commands);

    // `help` is special, so it needs to be inserted separately.
    commands.insert(
        "help".to_string(),
        CommandInfo::BuiltIn {
            about: Some(
                if targo::is_targo_invocation() {
                    "Displays help for a targo command"
                } else {
                    "Displays help for a cargo command"
                }
                .to_string(),
            ),
        },
    );

    commands
}

/// Warn when branded Targo is explicitly pointed at a non-Trust compiler.
/// This cosmetic warning may be suppressed; execution-lane authorization and
/// the explicit unverified banner cannot be suppressed.
// This runs before `configure_gctx`, so the configured environment API is not
// available yet. The messages are intentionally direct CLI stderr output.
#[allow(clippy::disallowed_methods, clippy::print_stderr)]
pub(crate) fn maybe_warn_trust_compiler() {
    // Only nudge for the real targo frontend, never plain `cargo`.
    if !targo::is_targo_invocation() {
        return;
    }
    if env_to_bool(env::var_os("TRUST_NO_MIGRATE_WARN").as_deref()) {
        return;
    }
    // Warn when RUSTC is explicitly a non-trustc compiler.
    if let Some(rustc) = env::var_os("RUSTC") {
        let rustc = PathBuf::from(&rustc);
        // The Trust compiler ships as `trustc` and as a `rustc`-named compat alias
        // (same binary; libc-compatible --version banner). Both are fine.
        if !trust_compiler_override_name(&rustc) {
            eprintln!(
                "warning: RUSTC={} is not the Trust compiler (trustc); Trust verification \
                 needs the Trust toolchain (set TRUST_NO_MIGRATE_WARN=1 to silence)",
                rustc.display()
            );
        }
    }
}

fn trust_compiler_override_name(path: &Path) -> bool {
    ["trustc", "rustc"]
        .iter()
        .any(|expected| targo::trust_executable_path_matches(path, expected))
}

/// Trust: the branded frontend never produces an artifact whose verification
/// status is implicit. A compilation command must arrive here either inside an
/// authenticated verified session or with an explicit `--unverified`
/// authorization; there is deliberately no third, silent outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustExecutionAuthorization {
    NotApplicable,
    Verified,
    ExplicitUnverified,
    InheritedExplicitUnverified,
}

fn authorize_trust_execution(
    is_targo: bool,
    cmd: &str,
    is_manifest_command: bool,
    explicit_unverified: bool,
    inherited_unverified: bool,
    verified_marker: bool,
    legacy_bootstrap_marker: bool,
) -> CargoResult<TrustExecutionAuthorization> {
    if is_targo && legacy_bootstrap_marker {
        anyhow::bail!(
            "legacy TRUST_BOOTSTRAP_NO_VERIFY markers do not authorize branded Targo; bootstrap must invoke the sibling `cargo` compatibility entrypoint"
        );
    }
    if !is_targo || !(is_manifest_command || is_native_compilation_command(cmd)) {
        if is_targo && explicit_unverified {
            // Trust: this branch also takes commands that do compile (`tippy`,
            // `trust`, an external subcommand), so the reason names only what is
            // true of all of them: none is in `is_native_compilation_command`.
            let what = if cmd == "trust" {
                "`targo trust` is the verified lane".to_string()
            } else {
                format!("`targo {cmd}` is not one")
            };
            anyhow::bail!(
                "`--unverified` is valid only for a Targo compilation command (build, check, \
                 test, run, ...); {what}, so run it without `--unverified`"
            );
        }
        return Ok(TrustExecutionAuthorization::NotApplicable);
    }

    if verified_marker && explicit_unverified {
        anyhow::bail!(
            "explicit-unverified Targo authority conflicts with the authenticated verified lane"
        );
    }
    // Trust (T14c, DECISION_QUEUE T14-EXPORT-1): an explicit lane beats an
    // inherited one. A tool or test under `targo --unverified` that runs
    // `targo trust check` keeps its verified lane; the inherited authority is
    // not re-exposed to that lane's children (`configure_nested_unverified_
    // targo_child` exports it only from the unverified lane).
    if verified_marker {
        return Ok(TrustExecutionAuthorization::Verified);
    }
    if explicit_unverified && inherited_unverified {
        // A nested invocation already has a live root broker. Reuse that
        // authenticated authority rather than allowing the child to mint a
        // replacement broker merely because it also received `--unverified`.
        return Ok(TrustExecutionAuthorization::InheritedExplicitUnverified);
    }
    if explicit_unverified {
        return Ok(TrustExecutionAuthorization::ExplicitUnverified);
    }
    if inherited_unverified {
        return Ok(TrustExecutionAuthorization::InheritedExplicitUnverified);
    }

    // A REFUSAL MUST BE ABLE TO STEER. When `cmd` has a verified counterpart, refusing is
    // the whole point: it puts `targo trust <lane>` in front of someone who was about to
    // produce an unverified artifact, and the message names both lanes and their claims.
    //
    // When there is NO verified counterpart the refusal cannot steer anyone. `run` has no
    // `targo trust run`, so the message's own text — "This is the only lane for `run`" —
    // concedes that the only way forward is to retype the command with `--unverified`. A
    // prompt with one button is not a decision; it is a toll. And it is a HARMFUL toll: the
    // habit it builds is exactly the reflex this authorization exists to prevent, because
    // someone who types `--unverified` daily to run a tool will type it without reading on
    // the day they are building something whose proof status is a real choice.
    //
    // Worse, it makes the flag say something false about the command. "Verified" and
    // "unverified" describe whether an ARTIFACT carries a proof claim. Applied to
    // `ship provision` — mint this machine's publishing identity — there is no artifact
    // whose proof status is in question, so the flag answers a question nobody asked.
    //
    // So: proceed, and SAY the lane instead of demanding it be typed. Nothing about what
    // gets built changes — this is the same lane the flag would have selected, chosen for
    // the user because it is the only one on offer.
    //
    // The awareness the refusal exists to create is preserved by the `UNVERIFIED:` warning
    // the match arm below prints. It is NOT preserved by the "runs with the proof pipeline
    // off" wording this comment used to cite: that text lives only in
    // `unauthorized_lane_message`, whose sole production caller is the `bail!` two lines
    // down — the line this early return exists to skip. Citing a string on the path you
    // just bypassed is how a comment ends up defending a guarantee nobody makes.
    // …but the one-button argument stops where the artifact's audience begins.
    // "Proceed on a single-lane verb" was argued for `run` and `ship provision`,
    // where no proof-bearing artifact is in question — and implemented for every
    // verb without a verified counterpart, which also covered `install`,
    // `package` and `publish` (output that LEAVES the machine: a binary on a
    // PATH, a crate at a registry) and `miri` (a pass/fail verdict someone will
    // read as checked). For those, "does this artifact carry a proof claim" is
    // exactly the question the flag answers, so the refusal is restored: it
    // cannot steer to a verified lane, but it can make a human own the choice
    // the artifact's consumers will inherit. The width-vs-argument gap is
    // documented in docs/2026-09-01-targo-single-lane-selection-blast-radius.md;
    // this is that document's disposition 1, and it is what the integration
    // suite (`cargo_command.rs` — miri exits 101, no UNVERIFIED line) had
    // pinned all along.
    if verified_trust_lane_for(cmd).is_none()
        && !is_manifest_command
        && !requires_explicit_lane(cmd)
    {
        return Ok(TrustExecutionAuthorization::ExplicitUnverified);
    }

    anyhow::bail!(unauthorized_lane_message(cmd, is_manifest_command))
}

/// Trust: the single-lane verbs that still demand a typed `--unverified`,
/// because their output outlives the invocation in someone else's hands.
/// `install` puts a binary on a PATH; `package`/`publish` ship a crate to a
/// registry; `miri` mints a pass/fail verdict that reads as "checked". The
/// local development verbs (`run`, `fix`, `clippy`, `bench`, `doc`, `rustc`,
/// `rustdoc`, `-Zscript`) proceed on their only lane with the UNVERIFIED
/// notice — for them the flag answers no question and the daily toll builds
/// the type-it-without-reading reflex this authorization exists to prevent.
fn requires_explicit_lane(cmd: &str) -> bool {
    // Trust: the private helper launches roots only with an explicit native lane.
    if cmd == "__resource-epoch" {
        return true;
    }
    matches!(cmd, "install" | "package" | "publish" | "miri")
}

/// Trust: the `targo trust` sub-subcommand that performs the same work as a
/// branded compilation command while producing a proof claim, or `None` when
/// the verifier driver has no counterpart for it.
///
/// Naming a counterpart that does not exist would be worse than naming none: a
/// reader who types it and gets "unknown subcommand" learns that verification
/// was unavailable, when what actually happened is that this frontend guessed.
/// Only the sub-subcommands the driver dispatches (`targo-trust`'s `check`,
/// `build`, `test`) may appear here.
fn verified_trust_lane_for(cmd: &str) -> Option<&'static str> {
    match cmd {
        "build" => Some("build"),
        "check" => Some("check"),
        "test" => Some("test"),
        _ => None,
    }
}

/// Trust: this refusal is the only place a human is ever shown Targo's two
/// lanes side by side, so it names the exact command for each one and states
/// the claim that command's artifact carries.
///
/// Refusing without naming the verified spelling teaches the reader that
/// `--unverified` is how you make Targo work, which is how an unverified build
/// becomes someone's habit. Naming the lanes without naming their claims is
/// worse still: the failure this whole authorization exists to prevent is a
/// binary whose owner believes it was proved.
fn unauthorized_lane_message(cmd: &str, is_manifest_command: bool) -> String {
    let invocation = if is_manifest_command {
        format!("-Zscript {cmd}")
    } else {
        cmd.to_owned()
    };
    let unverified = format!(
        "  `targo --unverified {invocation}`\n      \
         UNVERIFIED: runs with the proof pipeline off. Anything it produces carries NO proof claim."
    );

    // A manifest command's `cmd` is the script path, so there is no
    // sub-subcommand to name; the driver has no `-Zscript` lane either.
    match verified_trust_lane_for(cmd).filter(|_| !is_manifest_command) {
        Some(lane) => format!(
            "`targo {invocation}` refuses to create an implicitly unverified artifact. \
             Targo has exactly two lanes, and neither of them is silent:\n\
             \x20 `targo trust {lane}`\n      \
             VERIFIED: fail-closed verification, an authenticated per-unit proof report, \
             and an explicit dependency-TCB assumption ledger. The artifact carries a proof claim.\n\
             {unverified}"
        ),
        None => format!(
            "`targo {invocation}` refuses to create an implicitly unverified artifact. \
             Targo has exactly two lanes, and neither of them is silent:\n\
             {unverified} This is the only lane for `{invocation}`: the verifier driver has no \
             `targo trust` counterpart for it.\n\
             \x20 `targo trust check`\n      \
             VERIFIED: verifies this crate fail-closed and writes a proof report. \
             It does not perform `{invocation}` and does not substitute for it."
        ),
    }
}

/// Establish the process-local compilation policy before Cargo constructs any
/// units. Branded Targo has exactly two authorization roots: its authenticated
/// verifier loader, or a human-visible `--unverified` decision (direct or
/// broker-authenticated from an ancestor). Bootstrap's shim controls are
/// deliberately not frontend authority.
#[allow(clippy::disallowed_methods)]
pub(crate) fn configure_trust_execution_policy(
    cmd: &str,
    is_manifest_command: bool,
    explicit_unverified: bool,
) -> CargoResult<()> {
    let verified_marker = env::var_os("TRUST_TARGO_VERIFY").as_deref() == Some(OsStr::new("1"));
    let inherited_unverified = targo::nested_unverified_targo_handoff_active();
    let legacy_bootstrap_marker = env::var_os("TRUST_BOOTSTRAP_NO_VERIFY").is_some()
        || env::var_os("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY").is_some();
    let authorization = authorize_trust_execution(
        targo::is_targo_invocation(),
        cmd,
        is_manifest_command,
        explicit_unverified,
        inherited_unverified,
        verified_marker,
        legacy_bootstrap_marker,
    )
    .map_err(|error| {
        withheld_authority_note(error, targo::withheld_nested_unverified_targo_authority())
    })?;
    match authorization {
        TrustExecutionAuthorization::Verified => {
            targo::validate_verified_targo_startup_loader_environment()
                .map_err(anyhow::Error::msg)?;
            targo::set_trust_verified_targo(true);
        }
        #[expect(
            clippy::print_stderr,
            reason = "the explicit unverified authorization must report its no-proof status before ordinary Shell setup"
        )]
        TrustExecutionAuthorization::ExplicitUnverified => {
            // Trust: this exact authorization match is the only place allowed
            // to create live nested-unverified authority.
            targo::start_explicit_unverified_targo_broker().map_err(anyhow::Error::msg)?;
            targo::set_trust_no_verify_fast(true);
            let invocation = if is_manifest_command {
                format!("-Zscript {cmd}")
            } else {
                cmd.to_owned()
            };
            // Two different things reach this arm, and telling a user their run
            // "was explicitly authorized" when they typed no flag is a lie in the
            // one message whose whole job is to be believed. A verb with no
            // verified counterpart lands here with `explicit_unverified` false —
            // Targo chose the lane, nobody authorized it — and that is precisely
            // the case where the reader most needs to know a choice was made for
            // them.
            let how = if explicit_unverified {
                "was explicitly authorized with Trust verification disabled"
            } else {
                "has no verified lane, so Trust verification is off; nobody was asked"
            };
            eprintln!(
                "warning: UNVERIFIED: `targo {invocation}` {how}; this run emits no proof claim"
            );
        }
        #[expect(
            clippy::print_stderr,
            reason = "inherited unverified authorization must disclose its no-proof status before ordinary Shell setup"
        )]
        TrustExecutionAuthorization::InheritedExplicitUnverified => {
            targo::set_trust_no_verify_fast(true);
            let invocation = if is_manifest_command {
                format!("-Zscript {cmd}")
            } else {
                cmd.to_owned()
            };
            eprintln!(
                "warning: UNVERIFIED: `targo {invocation}` inherited live broker-authenticated explicit-unverified authority from its Targo ancestor; this run emits no proof claim"
            );
        }
        TrustExecutionAuthorization::NotApplicable => {}
    }
    Ok(())
}

/// Trust (T14c): a refusal under an inherited endpoint that did not
/// authenticate says so, since the reader most likely expected the ancestor's
/// `--unverified` to carry over (a stale endpoint, another Targo build, or a
/// root that exited).
fn withheld_authority_note(error: anyhow::Error, withheld: Option<&str>) -> anyhow::Error {
    match withheld {
        Some(reason) => anyhow::format_err!(
            "{error}\nnote: an inherited TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT granted \
             nothing: {reason}"
        ),
        None => error,
    }
}

fn is_native_compilation_command(cmd: &str) -> bool {
    matches!(
        cmd,
        "build"
            | "__resource-epoch" // Trust: controlled native root transport.
            | "check"
            | "fix"
            | "clippy"
            | "miri"
            | "test"
            | "run"
            | "bench"
            | "doc"
            | "rustc"
            | "rustdoc"
            | "install"
            | "package"
            | "publish"
    )
}

fn external_subcommand_prefixes() -> &'static [&'static str] {
    external_subcommand_prefixes_for_invocation(targo::is_targo_invocation())
}

fn external_subcommand_prefixes_for_invocation(trust_invocation: bool) -> &'static [&'static str] {
    if trust_invocation {
        &["targo-", "cargo-"]
    } else {
        &["cargo-"]
    }
}

/// Trust: one executable is installed under both `targo` and a `cargo` compat
/// symlink, so which name a user typed is a runtime fact. Every help string
/// upstream writes as a `cargo` literal has to route through here instead, or
/// the tool tells users to run a command that does not exist on their PATH.
fn frontend_binary_name() -> &'static str {
    if targo::is_targo_invocation() {
        "targo"
    } else {
        "cargo"
    }
}

pub(crate) fn command_help_footer(command: &str) -> String {
    color_print::cformat!(
        "Run `<bright-cyan,bold>{} help {}</>` for more detailed information.\n",
        frontend_binary_name(),
        command
    )
}

pub(crate) fn command_help_footer_with_invocation(
    command: &str,
    invocation: &str,
    detail: &str,
) -> String {
    let mut footer = command_help_footer(command);
    footer.push_str(&color_print::cformat!(
        "Run `<bright-cyan,bold>{} {}</>` {}.\n",
        frontend_binary_name(),
        invocation,
        detail
    ));
    footer
}

fn third_party_subcommands(gctx: &GlobalContext) -> BTreeMap<String, CommandInfo> {
    let suffix = env::consts::EXE_SUFFIX;
    let mut commands = BTreeMap::new();
    let search_directories = search_directories(gctx);
    for prefix in external_subcommand_prefixes() {
        for dir in &search_directories {
            let entries = match fs::read_dir(dir) {
                Ok(entries) => entries,
                _ => continue,
            };
            for entry in entries.filter_map(|e| e.ok()) {
                let path = entry.path();
                let Some(filename) = path.file_name().and_then(|s| s.to_str()) else {
                    continue;
                };
                let Some(name) = filename
                    .strip_prefix(prefix)
                    .and_then(|s| s.strip_suffix(suffix))
                else {
                    continue;
                };
                if targo::is_targo_invocation() && PROTECTED_TRUST_SUBCOMMANDS.contains(&name) {
                    // Trust: upstream resolves external subcommands from PATH,
                    // which would let any directory on it supply `targo trust`.
                    // Protected names are added only from the selected
                    // frontend's own bin directory below.
                    continue;
                }
                if is_executable(entry.path()) {
                    commands
                        .entry(name.to_string())
                        .or_insert_with(|| CommandInfo::External { path: path.clone() });
                }
            }
        }
    }
    if targo::is_targo_invocation()
        && let Ok(frontend) = gctx.cargo_exe()
    {
        for command in PROTECTED_TRUST_SUBCOMMANDS {
            if matches!(*command, "tippy" | "clippy") {
                commands.insert(
                    (*command).to_string(),
                    CommandInfo::External {
                        path: frontend.to_path_buf(),
                    },
                );
                continue;
            }
            if let Some(path) = protected_trust_subcommand_path(&frontend, command) {
                commands.insert((*command).to_string(), CommandInfo::External { path });
            }
        }
    }
    commands
}

fn user_defined_aliases(gctx: &GlobalContext) -> BTreeMap<String, CommandInfo> {
    let mut commands = BTreeMap::new();
    if let Ok(aliases) = gctx.get::<BTreeMap<String, StringOrVec>>(["alias"]) {
        for (name, target) in aliases.iter() {
            if !user_alias_allowed_for_invocation(targo::is_targo_invocation(), name.as_str()) {
                continue;
            }
            commands.insert(
                name.to_string(),
                CommandInfo::Alias {
                    target: target.clone(),
                },
            );
        }
    }
    commands
}

fn find_external_subcommand(gctx: &GlobalContext, cmd: &str) -> Option<PathBuf> {
    if targo::is_targo_invocation() && matches!(cmd, "tippy" | "clippy") {
        return gctx.cargo_exe().ok().map(Path::to_path_buf);
    }
    if targo::is_targo_invocation() && protected_trust_subcommand_binary(cmd).is_some() {
        let frontend = gctx.cargo_exe().ok()?;
        return protected_trust_subcommand_path(&frontend, cmd);
    }
    let search_directories = search_directories(gctx);
    for prefix in external_subcommand_prefixes() {
        let command_exe = format!("{}{}{}", prefix, cmd, env::consts::EXE_SUFFIX);
        if let Some(path) = search_directories
            .iter()
            .map(|dir| dir.join(&command_exe))
            .find(|file| is_executable(file))
        {
            return Some(path);
        }
    }
    None
}

// Trust: everything from here to `execute_external_subcommand` is
// Trust-authored — the protected-subcommand guard. Upstream treats an external
// subcommand as an arbitrary PATH executable it spawns and forgets. For the
// branded toolchain a handful of those names carry proof, lint, formatting, or
// interpreter authority, so their binary has to be resolved from the selected
// frontend's own directory and its identity has to still hold when the run
// finishes. The guard therefore captures identity before launch and revalidates
// after, rather than checking once.
//
// On a cargo re-align this block has no upstream counterpart; only
// `execute_external_subcommand` below is shared code.

/// Branded subcommands that are installed as part of the selected Trust
/// toolchain and whose identity affects proof, lint, formatting, or interpreter
/// semantics. Ordinary third-party Cargo/Targo extensions intentionally retain
/// Cargo's historical PATH/CARGO_HOME lookup behavior.
const PROTECTED_TRUST_SUBCOMMANDS: &[&str] = &["trust", "tippy", "clippy", "fmt", "miri"];

fn protected_trust_subcommand_binary(command: &str) -> Option<&'static str> {
    match command {
        "trust" => Some("targo-trust"),
        "fmt" => Some("targo-fmt"),
        "miri" => Some("targo-miri"),
        _ => None,
    }
}

/// Trust: `targo trust` sub-subcommands that run the developer/CI harness or a
/// diagnostic rather than produce a user-facing proof claim, and so run WITHOUT
/// the protected-subcommand guard on their OUTER wrapper.
///
/// INCLUSION CRITERION — a subcommand belongs here iff BOTH hold:
///   1. It makes no proof claim about user code (guard integrity is only
///      security-relevant for a run that credits a proof), AND
///   2. it can build / churn the in-tree `build/` toolchain directories that
///      ARE ancestors of the protected `targo-trust` binary during a long run,
///      which the post-run integrity guard would otherwise (correctly, for a
///      proof-producing run) treat as tampering — the self-inflicted false
///      positive this list removes.
///
/// `domination` runs the local gate suite (three-suite + corpus verification);
/// `doctor` builds an environment/toolchain diagnostic report. Any proof work a
/// dev-gate performs is dispatched through separately-guarded nested
/// `targo trust check`/`build` invocations, so excluding only the outer wrapper
/// weakens the guard for nothing.
///
/// NEVER add a proof-producing subcommand here (`check`, `build`, `test`,
/// `report`, `loop`, `prove`, `verify`, …): excluding one would let a raced
/// `targo-trust` swap escape detection on a run that credits a proof.
const TRUST_DEV_GATE_SUBCOMMANDS: &[&str] = &["domination", "doctor"];

/// True when this is a `targo trust <dev-gate>` invocation whose outer wrapper
/// must run WITHOUT the protected-subcommand guard. `args` is the external
/// command's argv with the repeated subcommand token at index 0
/// (`["trust", "domination", ...]`), so the sub-subcommand is the first
/// non-flag token after it.
fn trust_invocation_is_dev_gate(command: &str, args: &[&OsStr]) -> bool {
    if command != "trust" {
        return false;
    }
    args.iter()
        .skip(1)
        .filter_map(|arg| arg.to_str())
        .find(|token| !token.starts_with('-'))
        .is_some_and(|subcommand| TRUST_DEV_GATE_SUBCOMMANDS.contains(&subcommand))
}

fn user_alias_allowed_for_invocation(trust_invocation: bool, command: &str) -> bool {
    !trust_invocation || !PROTECTED_TRUST_SUBCOMMANDS.contains(&command)
}

fn protected_trust_subcommand_path(frontend: &Path, command: &str) -> Option<PathBuf> {
    let binary = protected_trust_subcommand_binary(command)?;
    if !frontend.is_absolute() {
        return None;
    }
    let directory = frontend.parent()?;
    let candidate = directory.join(format!("{binary}{}", env::consts::EXE_SUFFIX));
    let is_regular_file = fs::symlink_metadata(&candidate)
        .map(|metadata| metadata_is_plain_file(&metadata))
        .unwrap_or(false);
    (is_regular_file && is_executable(&candidate)).then_some(candidate)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProtectedPathSnapshot {
    len: u64,
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(unix)]
    mode: u32,
    #[cfg(unix)]
    links: u64,
    #[cfg(unix)]
    uid: u32,
    #[cfg(unix)]
    gid: u32,
    #[cfg(unix)]
    modified_seconds: i64,
    #[cfg(unix)]
    modified_nanoseconds: i64,
    #[cfg(unix)]
    changed_seconds: i64,
    #[cfg(unix)]
    changed_nanoseconds: i64,
    #[cfg(windows)]
    file_attributes: u32,
    #[cfg(windows)]
    creation_time: u64,
    #[cfg(windows)]
    last_write_time: u64,
}

impl ProtectedPathSnapshot {
    #[cfg(unix)]
    fn from_metadata(metadata: &fs::Metadata, _path: &Path) -> Result<Self, String> {
        use std::os::unix::fs::MetadataExt as _;

        Ok(Self {
            len: metadata.len(),
            device: metadata.dev(),
            inode: metadata.ino(),
            mode: metadata.mode(),
            links: metadata.nlink(),
            uid: metadata.uid(),
            gid: metadata.gid(),
            modified_seconds: metadata.mtime(),
            modified_nanoseconds: metadata.mtime_nsec(),
            changed_seconds: metadata.ctime(),
            changed_nanoseconds: metadata.ctime_nsec(),
        })
    }

    #[cfg(windows)]
    fn from_metadata(metadata: &fs::Metadata, path: &Path) -> Result<Self, String> {
        use std::os::windows::fs::MetadataExt as _;

        let _ = path;
        Ok(Self {
            len: metadata.len(),
            file_attributes: metadata.file_attributes(),
            creation_time: metadata.creation_time(),
            last_write_time: metadata.last_write_time(),
        })
    }

    #[cfg(not(any(unix, windows)))]
    fn from_metadata(_metadata: &fs::Metadata, path: &Path) -> Result<Self, String> {
        Err(format!(
            "cannot authenticate protected Trust path `{}` because this platform has no supported stable file-identity API",
            path.display()
        ))
    }

    // Trust: cross-time identity comparison that excludes the modification and
    // change timestamps. The OS mutates a protected executable's `ctime` (and
    // can touch `mtime`) for reasons unrelated to its contents — most notably
    // macOS writing the `com.apple.provenance` extended attribute the first
    // time the guard *executes* the binary, which bumps `ctime` between the
    // pre-launch capture and the post-run revalidation and would otherwise fail
    // the run closed against the guard's own execution side effect. Device +
    // inode (independently cross-checked via the retained `OpenedFileIdentity`
    // handle), size, mode, link count, and ownership are the fields a genuine
    // rebuild (cargo installs via a temp file + atomic rename -> new inode) or
    // tampering event actually changes; a currently-executing image cannot be
    // rewritten in place (ETXTBSY), so the timestamps were never the
    // load-bearing signal. The microsecond-wide capture-window stability check
    // (`capture_protected_path`) keeps full equality, timestamps included,
    // because no execution-time xattr write can occur inside that read-only
    // window.
    #[cfg(unix)]
    fn same_stable_identity(&self, other: &Self) -> bool {
        self.len == other.len
            && self.device == other.device
            && self.inode == other.inode
            && self.mode == other.mode
            && self.links == other.links
            && self.uid == other.uid
            && self.gid == other.gid
    }

    #[cfg(windows)]
    fn same_stable_identity(&self, other: &Self) -> bool {
        self.len == other.len && self.file_attributes == other.file_attributes
    }

    #[cfg(not(any(unix, windows)))]
    fn same_stable_identity(&self, other: &Self) -> bool {
        self == other
    }

    /// Whether two snapshots of an ANCESTOR directory carry the same
    /// authority over the selected path. Ordinary entry churn changes a
    /// directory's length, link count, and timestamps, so none of those are
    /// authority. Replacing the directory changes its identity; changing who
    /// can rewrite it changes its mode/owner (or Windows attributes).
    fn same_directory_authority(&self, other: &Self) -> bool {
        #[cfg(unix)]
        {
            self.device == other.device
                && self.inode == other.inode
                && self.mode == other.mode
                && self.uid == other.uid
                && self.gid == other.gid
        }
        #[cfg(windows)]
        {
            self.file_attributes == other.file_attributes
        }
        #[cfg(not(any(unix, windows)))]
        {
            let _ = other;
            false
        }
    }

    /// Whether the LATER ancestor snapshot `other` has the rename-shaped
    /// metadata signature: ctime advanced while mtime did not. Entry churn
    /// advances both; rename/restore advances ctime alone. Windows directory
    /// handles are retained without delete sharing, so rename is prevented by
    /// the kernel there rather than inferred from timestamps.
    fn metadata_tampered_since(&self, other: &Self) -> bool {
        #[cfg(unix)]
        {
            let ctime_advanced = (other.changed_seconds, other.changed_nanoseconds)
                > (self.changed_seconds, self.changed_nanoseconds);
            let mtime_advanced = (other.modified_seconds, other.modified_nanoseconds)
                > (self.modified_seconds, self.modified_nanoseconds);
            ctime_advanced && !mtime_advanced
        }
        #[cfg(not(unix))]
        {
            let _ = other;
            false
        }
    }
}

struct ProtectedSubcommandGuard {
    executable: ProtectedPathGuard,
    directories: Vec<ProtectedDirectoryGuard>,
    /// Trust: every symlink traversed while resolving the launch path to its
    /// canonical toolchain, in resolution order. Always empty when the launch
    /// path is already canonical, and always empty on Windows, where reparse
    /// points are held by `open_protected_path`'s share mode instead.
    symlink_hops: Vec<ProtectedSymlinkHop>,
}

/// Trust: one symlink on the launch path, pinned by its own exact metadata and
/// by the target it names.
///
/// A symlink has no interior to churn, so — unlike a directory — it is held to
/// full snapshot equality with no slack at all, and a replacement (new inode) or
/// a rename-and-restore (`ctime` moves, `mtime` does not) is refused.
struct ProtectedSymlinkHop {
    path: PathBuf,
    target: PathBuf,
    snapshot: ProtectedPathSnapshot,
    parent: PathBuf,
    parent_snapshot: ProtectedPathSnapshot,
}

struct ProtectedDirectoryGuard {
    path: PathBuf,
    selected: ProtectedPathGuard,
    role: ProtectedDirectoryRole,
}

/// What a directory in the selected path is trusted for, and therefore how
/// strictly it is rechecked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProtectedDirectoryRole {
    /// The selected toolchain `bin` itself: any content change is relevant.
    Selected,
    /// A directory that merely contains the selected one: identity and rewrite
    /// authority matter, unrelated entries do not.
    Ancestor,
}

impl ProtectedDirectoryGuard {
    fn still_authentic(&self, observed: &Self) -> bool {
        if self.path != observed.path || self.role != observed.role {
            return false;
        }
        match self.role {
            ProtectedDirectoryRole::Selected => {
                self.selected.identity == observed.selected.identity
                    && self.selected.snapshot == observed.selected.snapshot
            }
            ProtectedDirectoryRole::Ancestor => {
                self.selected
                    .identity
                    .same_file(&observed.selected.identity)
                    && self
                        .selected
                        .snapshot
                        .same_directory_authority(&observed.selected.snapshot)
                    && !self
                        .selected
                        .snapshot
                        .metadata_tampered_since(&observed.selected.snapshot)
            }
        }
    }
}

struct ProtectedPathGuard {
    // On Windows this is opened with sharing that denies executable writes and
    // all path deletion/renaming. Retaining it from initial selection through
    // child completion closes timestamp-restorable rewrite/replacement races.
    _handle: fs::File,
    identity: OpenedFileIdentity,
    snapshot: ProtectedPathSnapshot,
}

impl ProtectedSubcommandGuard {
    fn capture(path: &Path) -> Result<Self, String> {
        let directory_path = path.parent().ok_or_else(|| {
            format!(
                "protected Trust subcommand `{}` has no toolchain bin directory",
                path.display()
            )
        })?;
        let canonical_directory = directory_path.canonicalize().map_err(|error| {
            format!(
                "cannot canonicalize protected Trust toolchain directory `{}`: {error}",
                directory_path.display()
            )
        })?;
        // Trust: a non-canonical launch path is AUTHENTICATED, not refused.
        // `rustup toolchain link` can only install a custom toolchain as a
        // symlink, so refusing every non-canonical spelling did not defend the
        // toolchain — it made every protected subcommand unreachable through the
        // only entry point users have, and pushed fmt/clippy gates onto a stock
        // compiler instead.
        //
        // What replaces it is the substitution quantifier this codebase already
        // states for pathname-backed execution (`targo::util::process_authority`):
        // no principal other than root or the invoking identity may be able to
        // swap the object. Replacing a symlink needs write access to the same
        // containing directory that replacing a directory needs, and both are
        // caught the same way, by pinned device/inode identity — so a hop is
        // admitted, then held to MORE than a directory ancestor is: exact
        // metadata plus its target, an owner that is root or us, and a holding
        // directory no other principal may write.
        let symlink_hops = capture_protected_symlink_hops(directory_path, &canonical_directory)?;

        // The protected child is launched through a pathname. Retain the full
        // launch and canonical ancestor chains so rename -> redirect -> restore
        // of any selected directory changes the nearest unchanged parent even
        // when the original directory object itself is restored.
        let paths =
            protected_directory_ancestors(directory_path, &canonical_directory, &symlink_hops);
        let directories =
            capture_protected_directories(&paths, directory_path, &canonical_directory)?;
        let executable = capture_protected_path(path, true, None)?;
        let confirmed_directories =
            capture_protected_directories(&paths, directory_path, &canonical_directory)?;
        let confirmed_canonical_directory = directory_path.canonicalize().map_err(|error| {
            format!(
                "cannot re-canonicalize protected Trust toolchain directory `{}`: {error}",
                directory_path.display()
            )
        })?;
        if confirmed_canonical_directory != canonical_directory {
            return Err(format!(
                "protected Trust toolchain directory `{}` changed canonical target from `{}` to `{}` while subcommand identity was captured",
                directory_path.display(),
                canonical_directory.display(),
                confirmed_canonical_directory.display()
            ));
        }
        if !same_protected_directories(&directories, &confirmed_directories) {
            return Err(format!(
                "protected Trust toolchain directory chain `{}` changed while subcommand identity was captured",
                directory_path.display()
            ));
        }
        let confirmed_hops = capture_protected_symlink_hops(directory_path, &canonical_directory)?;
        if !same_protected_symlink_hops(&symlink_hops, &confirmed_hops) {
            return Err(format!(
                "protected Trust toolchain launch path `{}` changed a symlink while subcommand identity was captured",
                directory_path.display()
            ));
        }
        Ok(Self {
            executable,
            directories,
            symlink_hops,
        })
    }

    fn same_identity(&self, other: &Self) -> bool {
        self.executable.identity == other.executable.identity
            && self
                .executable
                .snapshot
                .same_stable_identity(&other.executable.snapshot)
            && same_protected_directories(&self.directories, &other.directories)
            && same_protected_symlink_hops(&self.symlink_hops, &other.symlink_hops)
    }
}

/// Trust: every DIRECTORY on the launch and canonical paths, with the symlink
/// hops removed — those are authenticated separately, to a stricter standard.
///
/// A launch ancestor reached THROUGH a hop stays in this list: it is a real
/// directory, and pinning that spelling is what makes a retargeted hop change
/// the identity of the launch path's own toolchain directory.
fn protected_directory_ancestors(
    launch: &Path,
    canonical: &Path,
    hops: &[ProtectedSymlinkHop],
) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for ancestor in launch.ancestors().chain(canonical.ancestors()) {
        if hops.iter().any(|hop| hop.path == ancestor) {
            continue;
        }
        if !paths.iter().any(|path| path == ancestor) {
            paths.push(ancestor.to_owned());
        }
    }
    paths
}

/// Trust: the two halves of a hop are re-checked at DIFFERENT strictnesses, for
/// the same reason `ProtectedDirectoryGuard::still_authentic` splits Selected
/// from Ancestor.
///
/// The symlink itself is held to exact metadata plus its target: a symlink has
/// no interior, so nothing about it churns for unrelated reasons, and a
/// replacement (new inode) or a rename-and-restore (`ctime` moves, `mtime` does
/// not) has to be refused.
///
/// The directory HOLDING it is an ancestor and is held to authority only. It is
/// a real directory — `~/.rustup/toolchains`, `~/toolchains` — whose `len`,
/// `mtime` and `ctime` move whenever any unrelated entry is created or removed
/// inside it. Comparing those would make an unrelated file appearing beside the
/// toolchain link abort an in-flight protected subcommand, which is exactly the
/// defect `fix(targo): tolerate unrelated protected-ancestor churn` removed from
/// the directory chain. The rename-shaped signature is still not tolerated.
fn same_protected_symlink_hops(
    left: &[ProtectedSymlinkHop],
    right: &[ProtectedSymlinkHop],
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.path == right.path
                && left.target == right.target
                && left.snapshot == right.snapshot
                && left.parent == right.parent
                && left
                    .parent_snapshot
                    .same_directory_authority(&right.parent_snapshot)
                && !left
                    .parent_snapshot
                    .metadata_tampered_since(&right.parent_snapshot)
        })
}

/// Trust: resolve the launch path one component at a time, authenticating every
/// symlink it goes through, and prove the walk lands exactly where
/// `canonicalize` said it would.
///
/// The walk is what finds hops `Path::ancestors` cannot see — a hop introduced
/// by a previous hop's target, which on this machine is the promotion symlink
/// (`~/.rustup/toolchains/trust -> ~/toolchains/trust-current -> trust-<rev>`)
/// and therefore the one object most likely to be rewritten under a live run.
/// The cross-check against `canonical` is what makes the resulting list safe to
/// rely on: a hop rewritten mid-walk makes the two disagree and the capture is
/// refused.
#[cfg(unix)]
fn capture_protected_symlink_hops(
    directory: &Path,
    canonical: &Path,
) -> Result<Vec<ProtectedSymlinkHop>, String> {
    use std::collections::VecDeque;
    use std::ffi::OsString;
    use std::path::Component;

    /// A resolution needing more hops than this is a loop or an attack, not a
    /// toolchain layout; Linux's own limit is 40.
    const MAX_LAUNCH_SYMLINK_HOPS: usize = 64;

    let mut remaining = VecDeque::new();
    push_protected_path_components(directory, &mut remaining)?;
    let mut resolved = PathBuf::from("/");
    let mut hops: Vec<ProtectedSymlinkHop> = Vec::new();
    while let Some(name) = remaining.pop_front() {
        if name == OsString::from(Component::CurDir.as_os_str()) {
            continue;
        }
        if name == OsString::from(Component::ParentDir.as_os_str()) {
            // `resolved` is fully resolved at every step, so a lexical pop is
            // what the kernel does too, and `/..` is `/`.
            resolved.pop();
            continue;
        }
        let candidate = resolved.join(&name);
        let metadata = fs::symlink_metadata(&candidate).map_err(|error| {
            format!(
                "cannot inspect protected Trust launch path component `{}`: {error}",
                candidate.display()
            )
        })?;
        if !metadata.file_type().is_symlink() {
            resolved = candidate;
            continue;
        }
        if hops.len() >= MAX_LAUNCH_SYMLINK_HOPS {
            return Err(format!(
                "protected Trust toolchain directory `{}` resolves through more than {MAX_LAUNCH_SYMLINK_HOPS} symlinks",
                directory.display()
            ));
        }
        let hop = capture_protected_symlink_hop(&candidate, &resolved)?;
        if hop.target.is_absolute() {
            resolved = PathBuf::from("/");
        }
        let mut expansion = VecDeque::new();
        push_protected_path_components(&hop.target, &mut expansion)?;
        if expansion.is_empty() {
            return Err(format!(
                "protected Trust launch path symlink `{}` has an empty target",
                candidate.display()
            ));
        }
        while let Some(component) = expansion.pop_back() {
            remaining.push_front(component);
        }
        hops.push(hop);
    }
    if resolved != canonical {
        return Err(format!(
            "protected Trust toolchain directory `{}` resolves to `{}`, but its authenticated symlink chain resolves to `{}`",
            directory.display(),
            canonical.display(),
            resolved.display()
        ));
    }
    Ok(hops)
}

#[cfg(not(unix))]
fn capture_protected_symlink_hops(
    _directory: &Path,
    _canonical: &Path,
) -> Result<Vec<ProtectedSymlinkHop>, String> {
    Ok(Vec::new())
}

#[cfg(unix)]
fn push_protected_path_components(
    path: &Path,
    out: &mut std::collections::VecDeque<std::ffi::OsString>,
) -> Result<(), String> {
    use std::path::Component;

    for component in path.components() {
        match component {
            Component::RootDir => {}
            Component::CurDir | Component::ParentDir | Component::Normal(_) => {
                out.push_back(component.as_os_str().to_owned());
            }
            Component::Prefix(_) => {
                return Err(format!(
                    "protected Trust launch path `{}` carries a platform prefix component",
                    path.display()
                ));
            }
        }
    }
    Ok(())
}

/// Trust: the substitution check for one symlink hop, the same quantifier
/// `targo::util::process_authority` applies to a pathname-backed execution
/// object — no principal other than root or the invoking identity may be able to
/// replace it. Two things decide that for a symlink:
///
/// * who owns the LINK — with a sticky holding directory, only its owner (or the
///   directory's owner, or root) may remove or rename it; and
/// * who may write the DIRECTORY that holds it. That, not the link, is the
///   substitution primitive: a symlink's target is immutable, so the only way to
///   retarget one is to replace the directory entry.
///
/// The link's OWN mode bits are deliberately not examined. Linux reports every
/// symlink as `0o777` and ignores the bits entirely, so testing them would refuse
/// every symlink on Linux while proving nothing on any platform.
#[cfg(unix)]
fn capture_protected_symlink_hop(
    path: &Path,
    parent: &Path,
) -> Result<ProtectedSymlinkHop, String> {
    use std::os::unix::fs::MetadataExt as _;

    let invoking_uid = unsafe { libc::geteuid() };
    let metadata = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect protected Trust launch path symlink `{}`: {error}",
            path.display()
        )
    })?;
    if !metadata.file_type().is_symlink() {
        return Err(format!(
            "protected Trust launch path component `{}` is no longer a symlink",
            path.display()
        ));
    }
    if metadata.uid() != 0 && metadata.uid() != invoking_uid {
        return Err(format!(
            "protected Trust launch path symlink `{}` is owned by uid={}, which is neither root nor the invoking identity (uid={invoking_uid}); a redirection a foreign principal owns can be repointed at another toolchain",
            path.display(),
            metadata.uid()
        ));
    }
    let target = fs::read_link(path).map_err(|error| {
        format!(
            "cannot read protected Trust launch path symlink `{}`: {error}",
            path.display()
        )
    })?;
    let snapshot = ProtectedPathSnapshot::from_metadata(&metadata, path)?;

    let parent_metadata = fs::symlink_metadata(parent).map_err(|error| {
        format!(
            "cannot inspect the directory `{}` holding protected Trust launch path symlink `{}`: {error}",
            parent.display(),
            path.display()
        )
    })?;
    if !protected_path_type_is_valid(&parent_metadata, false) {
        return Err(format!(
            "the directory `{}` holding protected Trust launch path symlink `{}` is not a plain directory",
            parent.display(),
            path.display()
        ));
    }
    if parent_metadata.uid() != 0 && parent_metadata.uid() != invoking_uid {
        return Err(format!(
            "the directory `{}` holding protected Trust launch path symlink `{}` is owned by uid={}, which is neither root nor the invoking identity (uid={invoking_uid}); its owner can repoint the symlink at another toolchain",
            parent.display(),
            path.display(),
            parent_metadata.uid()
        ));
    }
    // Sticky (`0o1000`) is the exemption POSIX defines for exactly this: in a
    // sticky directory only the entry's own owner, the directory's owner, or root
    // may remove or rename an entry, and both owners were just proven to be root
    // or the invoking identity. Without sticky, a group- or world-writable
    // directory hands any local principal the ability to replace the link.
    if parent_metadata.mode() & 0o022 != 0 && parent_metadata.mode() & 0o1000 == 0 {
        return Err(format!(
            "the directory `{}` holding protected Trust launch path symlink `{}` is group- or world-writable without the sticky bit (mode={:#o}); any local principal could repoint the symlink at another toolchain",
            parent.display(),
            path.display(),
            parent_metadata.mode() & 0o7777
        ));
    }
    let parent_snapshot = ProtectedPathSnapshot::from_metadata(&parent_metadata, parent)?;

    Ok(ProtectedSymlinkHop {
        path: path.to_owned(),
        target,
        snapshot,
        parent: parent.to_owned(),
        parent_snapshot,
    })
}

fn capture_protected_directories(
    paths: &[PathBuf],
    selected_directory: &Path,
    canonical_selected_directory: &Path,
) -> Result<Vec<ProtectedDirectoryGuard>, String> {
    paths
        .iter()
        .map(|path| {
            // Both spellings name the selected directory. On Unix capture has
            // already proven them equal; Windows canonical spelling can differ.
            let role = if path == selected_directory || path == canonical_selected_directory {
                ProtectedDirectoryRole::Selected
            } else {
                ProtectedDirectoryRole::Ancestor
            };
            let selected = capture_protected_path(path, false, Some(role))?;
            Ok(ProtectedDirectoryGuard {
                path: path.clone(),
                selected,
                role,
            })
        })
        .collect()
}

fn same_protected_directories(
    left: &[ProtectedDirectoryGuard],
    right: &[ProtectedDirectoryGuard],
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.still_authentic(right))
}

struct AuthenticatedProtectedSubcommand {
    path: PathBuf,
    selected: ProtectedSubcommandGuard,
}

impl AuthenticatedProtectedSubcommand {
    fn capture(path: PathBuf) -> Result<Self, String> {
        if !path.is_absolute() {
            return Err(format!(
                "protected Trust subcommand `{}` is not an absolute selected-toolchain path",
                path.display()
            ));
        }
        let selected = ProtectedSubcommandGuard::capture(&path)?;
        Ok(Self { path, selected })
    }

    /// Run a protected child with latest-boundary handles open, then reject
    /// its result if the executable or full launch/canonical directory chain
    /// no longer has the selected identity. This is not stable-handle execution:
    /// the process abstraction still launches a pathname, so a raced child's
    /// side effects can occur before the post-check rejects its result. Ancestor
    /// entry churn is deliberately ignored; selected-directory churn is not.
    fn run_guarded<T>(&self, operation: impl FnOnce() -> T) -> Result<T, String> {
        let guard = self.revalidate().map_err(|error| {
            format!("protected Trust subcommand authentication failed before launch: {error}")
        })?;
        let result = operation();
        let _post_guard = self.revalidate().map_err(|error| {
            format!(
                "protected Trust subcommand `{}` changed while it was running: {error}",
                self.path.display()
            )
        })?;
        drop(guard);
        Ok(result)
    }

    fn revalidate(&self) -> Result<ProtectedSubcommandGuard, String> {
        let current = ProtectedSubcommandGuard::capture(&self.path)?;
        if !self.selected.same_identity(&current) {
            return Err(format!(
                "selected protected Trust subcommand `{}` changed identity or contents",
                self.path.display()
            ));
        }
        Ok(current)
    }
}

fn capture_protected_path(
    path: &Path,
    require_executable: bool,
    directory_role: Option<ProtectedDirectoryRole>,
) -> Result<ProtectedPathGuard, String> {
    let before = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    if !protected_path_type_is_valid(&before, require_executable) {
        return Err(format!(
            "protected Trust path `{}` is not an admissible protected {} object",
            path.display(),
            if require_executable {
                "file"
            } else {
                "directory"
            }
        ));
    }
    if require_executable && !metadata_is_executable(&before) {
        return Err(format!(
            "protected Trust subcommand `{}` is not executable",
            path.display()
        ));
    }
    let before_snapshot = ProtectedPathSnapshot::from_metadata(&before, path)?;
    let handle = open_protected_path(path, &before, require_executable).map_err(|error| {
        format!(
            "cannot open protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let identity = opened_file_identity(&handle).map_err(|error| {
        format!(
            "cannot identify opened protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let opened = handle.metadata().map_err(|error| {
        format!(
            "cannot inspect opened protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let opened_snapshot = ProtectedPathSnapshot::from_metadata(&opened, path)?;
    let after = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot re-inspect protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let after_snapshot = ProtectedPathSnapshot::from_metadata(&after, path)?;
    let path_handle = open_protected_path(path, &after, require_executable).map_err(|error| {
        format!(
            "cannot reopen protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let path_snapshot = path_handle
        .metadata()
        .map_err(|error| {
            format!(
                "cannot inspect reopened protected Trust path `{}`: {error}",
                path.display()
            )
        })
        .and_then(|metadata| ProtectedPathSnapshot::from_metadata(&metadata, path))?;
    let path_identity = opened_file_identity(&path_handle).map_err(|error| {
        format!(
            "cannot identify reopened protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let snapshots_agree =
        |earlier: &ProtectedPathSnapshot, later: &ProtectedPathSnapshot| match directory_role {
            Some(ProtectedDirectoryRole::Ancestor) => {
                earlier.same_directory_authority(later) && !earlier.metadata_tampered_since(later)
            }
            Some(ProtectedDirectoryRole::Selected) | None => earlier == later,
        };
    // Stable opened-file identity excludes Windows change-time/link-count
    // churn while retaining the full volume + 128-bit file id. The retained
    // Windows directory handle additionally denies delete/rename sharing for
    // the guard's lifetime.
    let opened_identities_agree = match directory_role {
        Some(ProtectedDirectoryRole::Ancestor) => identity.same_file(&path_identity),
        Some(ProtectedDirectoryRole::Selected) | None => identity == path_identity,
    };
    if !snapshots_agree(&before_snapshot, &opened_snapshot)
        || !snapshots_agree(&opened_snapshot, &after_snapshot)
        || !snapshots_agree(&after_snapshot, &path_snapshot)
        || !opened_identities_agree
    {
        return Err(format!(
            "protected Trust path `{}` changed while its identity was captured",
            path.display()
        ));
    }
    Ok(ProtectedPathGuard {
        _handle: handle,
        identity,
        snapshot: opened_snapshot,
    })
}

fn protected_path_type_is_valid(metadata: &fs::Metadata, require_executable: bool) -> bool {
    if require_executable {
        return metadata_is_plain_file(metadata);
    }

    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt as _;

        const FILE_ATTRIBUTE_DIRECTORY: u32 = 0x0000_0010;
        metadata.file_attributes() & FILE_ATTRIBUTE_DIRECTORY != 0
    }
    #[cfg(not(windows))]
    {
        !metadata.file_type().is_symlink() && metadata.file_type().is_dir()
    }
}

#[cfg(not(windows))]
fn open_protected_path(
    path: &Path,
    _metadata: &fs::Metadata,
    _require_executable: bool,
) -> std::io::Result<fs::File> {
    fs::File::open(path)
}

#[cfg(windows)]
fn open_protected_path(
    path: &Path,
    metadata: &fs::Metadata,
    require_executable: bool,
) -> std::io::Result<fs::File> {
    use std::os::windows::fs::{MetadataExt as _, OpenOptionsExt as _};

    const FILE_SHARE_READ: u32 = 0x0000_0001;
    const FILE_SHARE_WRITE: u32 = 0x0000_0002;
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;
    const FILE_FLAG_BACKUP_SEMANTICS: u32 = 0x0200_0000;
    const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;

    if require_executable {
        return fs::OpenOptions::new()
            .read(true)
            // Executable contents and pathname selection stay immutable for
            // the lifetime of the retained guard.
            .share_mode(FILE_SHARE_READ)
            .open(path);
    }

    let share_mode = if metadata.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0 {
        // A junction/symlink target is writable reparse data; deny both write
        // and delete sharing while retaining the launch and canonical chains.
        FILE_SHARE_READ
    } else {
        // Permit ordinary descendant access, but prevent this directory object
        // from being renamed or deleted out from under the selected path.
        FILE_SHARE_READ | FILE_SHARE_WRITE
    };
    fs::OpenOptions::new()
        .access_mode(0)
        .share_mode(share_mode)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
        .open(path)
}

#[cfg(unix)]
fn metadata_is_executable(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt as _;

    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn metadata_is_executable(_metadata: &fs::Metadata) -> bool {
    true
}

fn execute_external_subcommand(gctx: &GlobalContext, cmd: &str, args: &[&OsStr]) -> CliResult {
    if targo::is_targo_invocation() && matches!(cmd, "tippy" | "clippy") {
        return finish_guarded_protected_subcommand(targo::util::lint_frontend::run(
            gctx, cmd, args,
        ));
    }
    let path = find_external_subcommand(gctx, cmd);
    let command = match path {
        Some(command) => command,
        None => {
            let script_suggestion = if gctx.cli_unstable().script
                && std::path::Path::new(cmd).is_file()
            {
                let sep = std::path::MAIN_SEPARATOR;
                format!(
                    "\nhelp: to run the file `{cmd}`, provide a relative path like `.{sep}{cmd}`"
                )
            } else {
                "".to_owned()
            };
            let err = if cmd.starts_with('+') {
                anyhow::format_err!(
                    "no such command: `{cmd}`\n\n\
                    help: invoke `{}` through `rustup` to handle `+toolchain` directives{script_suggestion}",
                    frontend_binary_name(),
                )
            } else {
                let suggestions = list_commands(gctx);
                // Trust: upstream 1.99's rustfmt->fmt hint, extended to the
                // Trust spelling (`trustfmt`).
                let did_you_mean = if cmd == "rustfmt" || cmd == "trustfmt" {
                    "\n\nhelp: a command with a similar name exists: `fmt`".to_string()
                } else if cmd == "clippy" || cmd == "cargo-clippy" {
                    // This toolchain ships the linter as `tippy`, and deletes
                    // `cargo-clippy`. Without this arm the generic path below
                    // suggested `search targo-clippy` — a package that cannot
                    // exist — and `closest_msg` could not rescue it because the
                    // candidate list only holds commands whose binary RESOLVED,
                    // so `tippy` is absent precisely when the user needs it.
                    //
                    "\n\nhelp: this toolchain ships the linter as `tippy`: run `targo tippy`"
                        .to_string()
                } else {
                    closest_msg(cmd, suggestions.keys(), |c| c, "command")
                };
                let frontend = frontend_binary_name();
                let package_prefix = if targo::is_targo_invocation() {
                    "targo"
                } else {
                    "cargo"
                };

                anyhow::format_err!(
                    "no such command: `{cmd}`{did_you_mean}\n\n\
                    help: view all installed commands with `{frontend} --list`\n\
                    help: find a package to install `{cmd}` with `{frontend} search {package_prefix}-{cmd}`{script_suggestion}",
                )
            };

            return Err(CliError::new(err, 101));
        }
    };
    let protected = targo::is_targo_invocation()
        && protected_trust_subcommand_binary(cmd).is_some()
        && !trust_invocation_is_dev_gate(cmd, args);
    execute_subcommand(gctx, Some(&command), args, protected)
}

fn execute_internal_subcommand(gctx: &GlobalContext, args: &[&OsStr]) -> CliResult {
    execute_subcommand(gctx, None, args, false)
}

// This function is used to execute a subcommand. It is used to execute both
// internal and external subcommands.
// If `cmd_path` is `None`, then the subcommand is an internal subcommand.
fn execute_subcommand(
    gctx: &GlobalContext,
    cmd_path: Option<&PathBuf>,
    args: &[&OsStr],
    protected: bool,
) -> CliResult {
    let cargo_exe = gctx.cargo_exe()?;
    let mut cmd = match cmd_path {
        Some(cmd_path) => ProcessBuilder::new(cmd_path),
        None => ProcessBuilder::new(&cargo_exe),
    };
    cmd.env(targo::CARGO_ENV, cargo_exe).args(args);
    targo::withhold_unauthenticated_nested_unverified_endpoint(&mut cmd);
    if let Some(client) = gctx.jobserver_from_env()? {
        cmd.inherit_jobserver(client);
    }

    // Trust: a protected subcommand cannot use upstream's `exec_replace` — this
    // process has to survive the child in order to revalidate the toolchain
    // identity it captured before launch.
    if protected {
        let path = cmd_path.expect("only an external Trust subcommand can be protected");
        let authenticated =
            AuthenticatedProtectedSubcommand::capture(path.clone()).map_err(|error| {
                CliError::new(
                    anyhow::format_err!(
                        "could not authenticate protected Trust subcommand: {error}"
                    ),
                    // Same authority class as a post-run guard trip, just
                    // detected before launch.
                    PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
                )
            })?;
        return finish_guarded_protected_subcommand(authenticated.run_guarded(|| cmd.status()));
    }

    let err = match cmd.exec_replace() {
        Ok(()) => return Ok(()),
        Err(e) => e,
    };

    if let Some(perr) = err.downcast_ref::<ProcessError>() {
        if let Some(code) = perr.code {
            return Err(CliError::code(code));
        }
    }
    Err(CliError::new(err, 101))
}

/// Trust: exit code for a protected-subcommand AUTHORITY failure (the toolchain
/// or its recorded ancestor chain changed while the subcommand ran, so the
/// captured identity can no longer be trusted).
///
/// This is a setup/toolchain-authority failure, which the CLI contract numbers
/// 2 — the same code `targo-trust`'s own pipeline returns for every
/// setup/evidence failure. It is NOT 101: cargo reserves 101 for "could not
/// compile", so mapping a raced toolchain there makes an environment defect
/// impersonate a compiler crash, and (worse) DISCARDS the child's real exit
/// status after it has already written a complete, sealed report to stdout —
/// turning an honest `exit 1` verification-gate failure into an unexplained
/// 101.
const PROTECTED_SUBCOMMAND_AUTHORITY_EXIT: i32 = 2;

/// Trust: the single mapping point from a guarded protected-subcommand run to
/// this process's exit contract.
///
/// A guard failure NEVER inherits or fabricates the child's status (the guard
/// exists precisely because the child's identity is in doubt); the child's own
/// status governs only when the guard HOLDS. Extracted from
/// `execute_subcommand` so the mapping is unit-testable without a
/// `GlobalContext`.
fn finish_guarded_protected_subcommand(
    outcome: Result<CargoResult<ExitStatus>, String>,
) -> CliResult {
    let status = outcome
        .map_err(|error| {
            CliError::new(
                anyhow::format_err!(error),
                PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
            )
        })?
        // A spawn-level io error genuinely is "cargo could not execute the
        // tool", which is cargo's own 101 convention.
        .map_err(|error| CliError::new(error, 101))?;
    if status.success() {
        Ok(())
    } else {
        Err(CliError::code(subcommand_exit_status_code(&status)))
    }
}

fn subcommand_exit_status_code(status: &ExitStatus) -> i32 {
    if let Some(code) = status.code() {
        return code;
    }

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;

        if let Some(signal) = status.signal() {
            return 128_i32.saturating_add(signal).min(u8::MAX.into());
        }
    }

    101
}

#[cfg(unix)]
fn is_executable<P: AsRef<Path>>(path: P) -> bool {
    use std::os::unix::prelude::*;
    fs::metadata(path)
        .map(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}
#[cfg(windows)]
fn is_executable<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref().is_file()
}

fn search_directories(gctx: &GlobalContext) -> Vec<PathBuf> {
    let mut path_dirs = if let Some(val) = gctx.get_env_os("PATH") {
        env::split_paths(&val).collect()
    } else {
        vec![]
    };

    let home_bin = gctx.home().clone().into_path_unlocked().join("bin");

    // If any of that PATH elements contains `home_bin`, do not
    // add it again. This is so that the users can control priority
    // of it using PATH, while preserving the historical
    // behavior of preferring it over system global directories even
    // when not in PATH at all.
    // See https://github.com/rust-lang/cargo/issues/11020 for details.
    //
    // Note: `p == home_bin` will ignore trailing slash, but we don't
    // `canonicalize` the paths.
    if !path_dirs.iter().any(|p| p == &home_bin) {
        path_dirs.insert(0, home_bin);
    };

    // Trust toolchains ship `targo-trust` as a sibling of the installed
    // `targo` binary. rustup does not add arbitrary component binaries to PATH.
    // This directory must be first: inserting CARGO_HOME after it used to let a
    // stale or attacker-controlled `~/.cargo/bin/targo-trust` shadow the
    // verifier bundled with the selected Trust toolchain.
    if targo::is_targo_invocation()
        && let Ok(frontend_exe) = gctx.cargo_exe()
        && let Some(current_bin) = frontend_exe.parent()
    {
        path_dirs.retain(|path| path != current_bin);
        path_dirs.insert(0, current_bin.to_path_buf());
    }

    path_dirs
}

// Trust: pins the frontend's authorization contract — lane selection, alias and
// external-subcommand resolution, and the guard's exit-code mapping. These live
// here rather than in `tests/testsuite` because a testsuite binary cannot
// observe this process's own argv-derived frontend identity.
#[cfg(test)]
mod trust_tests {
    use super::{
        AuthenticatedProtectedSubcommand, PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
        TrustExecutionAuthorization, authorize_trust_execution, env_to_bool,
        external_subcommand_prefixes_for_invocation, finish_guarded_protected_subcommand,
        is_native_compilation_command, protected_trust_subcommand_binary,
        protected_trust_subcommand_path, requires_explicit_lane, subcommand_exit_status_code,
        trust_compiler_override_name, trust_invocation_is_dev_gate, unauthorized_lane_message,
        user_alias_allowed_for_invocation, verified_trust_lane_for, withheld_authority_note,
    };
    use std::ffi::{OsStr, OsString};
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, ExitStatus};
    use std::sync::Mutex;
    use targo::CargoResult;

    static PROTECTED_FIXTURE_LOCK: Mutex<()> = Mutex::new(());

    /// The package, the library this binary links (`targo::…` paths above) and
    /// this binary are all `targo`, so no Trust build compiles `--crate-name
    /// cargo`. The stock name survives only as the compatibility entry point
    /// bootstrap installs beside `targo` (docs/trust-naming.md).
    #[test]
    fn the_trust_cargo_package_and_binary_crate_are_named_targo() {
        assert_eq!(env!("CARGO_PKG_NAME"), "targo");
        assert_eq!(env!("CARGO_CRATE_NAME"), "targo");
        assert_eq!(option_env!("CARGO_BIN_NAME"), Some("targo"));
    }

    #[test]
    fn trust_boolean_environment_values_are_explicit() {
        assert!(env_to_bool(Some(OsStr::new("1"))));
        assert!(env_to_bool(Some(OsStr::new("true"))));
        assert!(!env_to_bool(Some(OsStr::new("0"))));
        assert!(!env_to_bool(Some(OsStr::new("false"))));
        assert!(!env_to_bool(Some(OsStr::new(""))));
        assert!(!env_to_bool(None));
    }

    #[test]
    fn the_native_compilation_set_is_exactly_the_fourteen_transport_verbs() {
        for command in [
            "build", "check", "fix", "clippy", "miri", "test", "run", "bench", "doc", "rustc",
            "rustdoc", "install", "package", "publish",
        ] {
            assert!(
                is_native_compilation_command(command),
                "native `{command}` transport must require an explicit authorization lane"
            );
        }
        for command in ["trust", "metadata", "fetch"] {
            assert!(!is_native_compilation_command(command));
        }
    }

    #[test]
    fn branded_native_compilation_refuses_implicit_unverified_mode() {
        let error = authorize_trust_execution(true, "build", false, false, false, false, false)
            .expect_err("implicit unverified Targo must fail");
        assert!(error.to_string().contains("implicitly unverified artifact"));
    }

    /// A REFUSAL MUST BE ABLE TO STEER SOMEWHERE.
    ///
    /// `build`/`check`/`test` have a `targo trust` counterpart, so refusing puts a real
    /// alternative in front of the user and must keep happening. `run` has none — the
    /// refusal's own text conceded "This is the only lane for `run`" — so demanding the
    /// flag could only make the user retype the identical command. That toll builds the
    /// `--unverified` reflex this authorization exists to prevent, and spends it on a verb
    /// where the choice is real.
    ///
    /// This pins the DISTINCTION, not either half alone: a change that starts refusing
    /// `run` again, or stops refusing `build`, fails here.
    #[test]
    fn a_local_development_verb_proceeds_and_an_artifact_emitting_one_refuses() {
        // Local development verbs: the only lane is taken and announced. (`ship`
        // was in this list once — asserting `ExplicitUnverified` for a verb that
        // is not a native compilation command at all, so the row could never
        // pass: `authorize_trust_execution` answers `NotApplicable` for it. The
        // row now asserts what the code does.)
        for lane_less in ["run", "fix", "bench", "doc", "rustc", "rustdoc", "clippy"] {
            let got = authorize_trust_execution(true, lane_less, false, false, false, false, false)
                .unwrap_or_else(|e| panic!("`targo {lane_less}` must not refuse: {e}"));
            assert!(
                matches!(got, TrustExecutionAuthorization::ExplicitUnverified),
                "`{lane_less}` must take the only lane it has, got {got:?}"
            );
            assert!(
                verified_trust_lane_for(lane_less).is_none(),
                "precondition: `{lane_less}` has no verified counterpart"
            );
        }
        let got = authorize_trust_execution(true, "ship", false, false, false, false, false)
            .expect("`ship` is not a native compilation command");
        assert!(
            matches!(got, TrustExecutionAuthorization::NotApplicable),
            "`ship` is outside the transport set entirely, got {got:?}"
        );
        // Single-lane verbs whose artifact leaves the machine (or mints a
        // verdict) still demand the typed flag: the refusal cannot steer to a
        // verified lane, but it makes a human own the choice the artifact's
        // consumers inherit. This is what the integration suite pinned for
        // `miri` throughout.
        for emitting in ["install", "package", "publish", "miri"] {
            assert!(requires_explicit_lane(emitting), "boundary: `{emitting}`");
            let error =
                authorize_trust_execution(true, emitting, false, false, false, false, false)
                    .expect_err("an artifact-emitting verb must refuse the implicit lane");
            assert!(
                error.to_string().contains("implicitly unverified artifact"),
                "the refusal names the stake: {error}"
            );
        }
        // …and the verbs that DO have a counterpart still refuse, for the same reason.
        for steerable in ["build", "check", "test"] {
            assert!(
                verified_trust_lane_for(steerable).is_some(),
                "precondition: `{steerable}` has a verified counterpart"
            );
            authorize_trust_execution(true, steerable, false, false, false, false, false)
                .expect_err("`{steerable}` must still refuse — the refusal can steer");
        }
    }

    #[test]
    fn the_refusal_names_both_lanes_and_the_claim_each_artifact_carries() {
        // A refusal that only forbids leaves the reader to discover
        // `--unverified` first, because it is the spelling the message
        // mentions. Both exact commands, and what each one's artifact asserts,
        // have to be in the text a human actually sees.
        let message = unauthorized_lane_message("build", false);
        assert!(message.contains("`targo trust build`"), "{message}");
        assert!(message.contains("`targo --unverified build`"), "{message}");
        let verified = message
            .find("VERIFIED: fail-closed")
            .expect("verified lane claim");
        let unverified = message.find("UNVERIFIED:").expect("unverified lane claim");
        assert!(
            verified < unverified,
            "the lane that carries a proof claim is the one being recommended: {message}"
        );
        assert!(message.contains("carries a proof claim"), "{message}");
        assert!(message.contains("carries NO proof claim"), "{message}");

        for (command, lane) in [("check", "check"), ("test", "test")] {
            let message = unauthorized_lane_message(command, false);
            assert!(
                message.contains(&format!("`targo trust {lane}`")),
                "{message}"
            );
            assert!(
                message.contains(&format!("`targo --unverified {command}`")),
                "{message}"
            );
        }
    }

    #[test]
    fn a_command_with_no_verified_counterpart_is_told_so_rather_than_sent_to_one() {
        // `targo trust doc` does not exist. Printing it would read as "you
        // declined verification", when the truth is that this command has no
        // verified lane at all — and the reader would then run a command that
        // errors out with `unknown subcommand`.
        for command in ["doc", "miri", "run", "install", "publish"] {
            assert!(
                verified_trust_lane_for(command).is_none(),
                "`targo trust {command}` is not a driver subcommand"
            );
            let message = unauthorized_lane_message(command, false);
            assert!(
                !message.contains(&format!("targo trust {command}")),
                "invented a verified lane for `{command}`: {message}"
            );
            assert!(message.contains("This is the only lane for"), "{message}");
            assert!(
                message.contains(&format!("does not perform `{command}`")),
                "the nearest verified lane must not read as an equivalent: {message}"
            );
        }
    }

    #[test]
    fn a_manifest_command_is_not_offered_a_script_lane_the_driver_lacks() {
        // Here `cmd` is the script path, not a subcommand name, and the driver
        // resolves no embedded manifest. Substituting the path into
        // `targo trust <cmd>` would print a command that cannot work.
        let message = unauthorized_lane_message("./script.rs", true);
        assert!(
            message.contains("`targo --unverified -Zscript ./script.rs`"),
            "{message}"
        );
        assert!(!message.contains("targo trust ./script.rs"), "{message}");
        assert!(message.contains("`targo trust check`"), "{message}");
    }

    #[test]
    fn branded_native_compilation_accepts_each_authenticated_or_explicit_lane() {
        assert_eq!(
            authorize_trust_execution(true, "check", false, true, false, false, false).unwrap(),
            TrustExecutionAuthorization::ExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(true, "check", false, false, true, false, false).unwrap(),
            TrustExecutionAuthorization::InheritedExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(true, "test", false, false, false, true, false).unwrap(),
            TrustExecutionAuthorization::Verified
        );
    }

    #[test]
    fn unverified_outside_a_compilation_command_names_the_command_and_remedy() {
        // `tippy` and an external subcommand do compile, so the refusal must not
        // say they compile nothing; `trust` is the verified lane itself.
        for command in ["new", "metadata", "tree", "tippy", "nextest", "trust"] {
            let error = authorize_trust_execution(true, command, false, true, false, false, false)
                .expect_err("`--unverified` stays refused outside a compilation command");
            let message = error.to_string();
            assert!(
                message.starts_with("`--unverified` is valid only for a Targo compilation command"),
                "{message}"
            );
            let reason = if command == "trust" {
                "`targo trust` is the verified lane".to_string()
            } else {
                format!("`targo {command}` is not one")
            };
            assert!(message.contains(&reason), "{message}");
            assert!(!message.contains("compiles nothing"), "{message}");
            assert!(
                message.contains("run it without `--unverified`"),
                "{message}"
            );
        }
    }

    /// T14c (DECISION_QUEUE T14-EXPORT-1): an explicit lane beats an
    /// inherited one. `targo trust check` run by a tool or test under
    /// `targo --unverified` keeps its verified lane instead of being refused.
    #[test]
    fn the_verified_marker_beats_inherited_unverified_authority() {
        for command in ["build", "check", "test"] {
            assert_eq!(
                authorize_trust_execution(true, command, false, false, true, true, false).unwrap(),
                TrustExecutionAuthorization::Verified,
                "{command}"
            );
        }
    }

    /// T14c (T14-EXPORT-1): an inherited endpoint that did not authenticate
    /// grants nothing (`inherited_unverified` stays false). A typed
    /// `--unverified`, the verified marker and a verb that compiles nothing
    /// proceed on their own; a compile verb naming no lane is refused, and the
    /// refusal says why the ancestor's lane did not carry over.
    #[test]
    fn an_endpoint_that_did_not_authenticate_grants_nothing_and_is_named() {
        assert_eq!(
            authorize_trust_execution(true, "check", false, true, false, false, false).unwrap(),
            TrustExecutionAuthorization::ExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(true, "check", false, false, false, true, false).unwrap(),
            TrustExecutionAuthorization::Verified
        );
        assert_eq!(
            authorize_trust_execution(true, "metadata", false, false, false, false, false).unwrap(),
            TrustExecutionAuthorization::NotApplicable
        );
        let refusal = || {
            authorize_trust_execution(true, "build", false, false, false, false, false).unwrap_err()
        };
        let plain = refusal().to_string();
        let named = withheld_authority_note(
            refusal(),
            Some("failed to connect to nested-unverified Targo broker `/x/b`"),
        )
        .to_string();
        assert!(named.starts_with(&plain), "{named}");
        assert!(
            named.contains("UNVERIFIED_ENDPOINT granted nothing"),
            "{named}"
        );
        assert!(named.contains("failed to connect"), "{named}");
        assert_eq!(withheld_authority_note(refusal(), None).to_string(), plain);
    }

    #[test]
    fn legacy_bootstrap_markers_never_authorize_branded_targo() {
        for command in ["build", "metadata"] {
            let error = authorize_trust_execution(true, command, false, false, false, false, true)
                .expect_err("legacy ambient marker must fail before command dispatch");
            assert!(error.to_string().contains("do not authorize branded Targo"));
        }
    }

    #[test]
    fn targo_authorization_lanes_cannot_be_combined_or_misapplied() {
        // The verified marker beside a typed `--unverified`, with or without
        // inherited authority, is a conflict.
        assert!(authorize_trust_execution(true, "build", false, true, false, true, false).is_err());
        assert!(authorize_trust_execution(true, "build", false, true, true, true, false).is_err());
        assert!(authorize_trust_execution(true, "build", false, false, false, true, true).is_err());
        assert_eq!(
            authorize_trust_execution(true, "build", false, true, true, false, false).unwrap(),
            TrustExecutionAuthorization::InheritedExplicitUnverified,
            "an explicit flag in an inherited subtree must reuse the live root broker"
        );
        assert!(
            authorize_trust_execution(true, "metadata", false, true, false, false, false).is_err()
        );
        assert_eq!(
            authorize_trust_execution(true, "metadata", false, false, true, false, false).unwrap(),
            TrustExecutionAuthorization::NotApplicable,
            "an inherited capability grants only native compilation authority"
        );
    }

    #[test]
    fn cargo_compatibility_identity_is_never_promoted_by_targo_markers() {
        for command in ["build", "miri"] {
            assert_eq!(
                authorize_trust_execution(false, command, false, false, true, true, true).unwrap(),
                TrustExecutionAuthorization::NotApplicable
            );
        }
    }

    #[test]
    fn branded_manifest_script_is_a_native_compilation_entry_path() {
        let error =
            authorize_trust_execution(true, "./subject.rs", true, false, false, false, false)
                .expect_err("implicit Targo script compilation must fail");
        assert!(error.to_string().contains("implicitly unverified artifact"));
        assert!(error.to_string().contains("-Zscript ./subject.rs"));
        assert_eq!(
            authorize_trust_execution(true, "./subject.rs", true, true, false, false, false)
                .unwrap(),
            TrustExecutionAuthorization::ExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(false, "./subject.rs", true, false, true, true, false)
                .unwrap(),
            TrustExecutionAuthorization::NotApplicable,
            "ordinary Cargo script behavior remains outside Targo policy"
        );
    }

    #[test]
    fn compiler_override_warning_uses_whole_executable_names() {
        assert!(trust_compiler_override_name(Path::new("trustc")));
        assert!(trust_compiler_override_name(Path::new("rustc")));
        assert!(!trust_compiler_override_name(Path::new("trustc.backup")));
        assert!(!trust_compiler_override_name(Path::new("not-rustc")));
        if !cfg!(windows) {
            assert!(!trust_compiler_override_name(Path::new("TRUSTC")));
            assert!(!trust_compiler_override_name(Path::new("trustc.exe")));
        }
    }

    #[test]
    fn targo_prefers_trust_subcommand_names() {
        assert_eq!(
            external_subcommand_prefixes_for_invocation(true),
            &["targo-", "cargo-"]
        );
        assert_eq!(
            external_subcommand_prefixes_for_invocation(false),
            &["cargo-"]
        );
    }

    #[test]
    fn protected_front_doors_have_one_bundled_binary_identity() {
        assert_eq!(
            protected_trust_subcommand_binary("trust"),
            Some("targo-trust")
        );
        // Lint is protected native dispatch, not an external SDK planner.
        assert_eq!(protected_trust_subcommand_binary("tippy"), None);
        assert_eq!(protected_trust_subcommand_binary("clippy"), None);
        assert_eq!(protected_trust_subcommand_binary("fmt"), Some("targo-fmt"));
        assert_eq!(
            protected_trust_subcommand_binary("miri"),
            Some("targo-miri")
        );
        assert_eq!(protected_trust_subcommand_binary("third-party"), None);
    }

    #[test]
    fn branded_front_door_aliases_cannot_shadow_bundled_tools() {
        for command in ["trust", "tippy", "clippy", "fmt", "miri"] {
            assert!(
                !user_alias_allowed_for_invocation(true, command),
                "[alias] {command} must not replace a bundled Trust front door"
            );
            assert!(
                user_alias_allowed_for_invocation(false, command),
                "ordinary Cargo alias semantics must remain unchanged"
            );
        }
        assert!(user_alias_allowed_for_invocation(true, "third-party"));
    }

    #[cfg(unix)]
    #[test]
    fn protected_front_door_never_falls_back_to_ambient_or_nonexecutable_binary() {
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-command-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let selected_bin = root.join("selected/bin");
        let ambient_bin = root.join("ambient/bin");
        fs::create_dir_all(&selected_bin).expect("create selected bin");
        fs::create_dir_all(&ambient_bin).expect("create ambient bin");
        let frontend = selected_bin.join("targo");
        fs::write(&frontend, b"frontend").expect("write frontend fixture");
        assert_eq!(
            protected_trust_subcommand_path(std::path::Path::new("targo"), "trust"),
            None,
            "relative frontend identity must fail closed"
        );
        let ambient = ambient_bin.join("targo-trust");
        fs::write(&ambient, b"ambient shadow").expect("write ambient fixture");
        fs::set_permissions(&ambient, fs::Permissions::from_mode(0o755))
            .expect("make ambient fixture executable");

        assert_eq!(
            protected_trust_subcommand_path(&frontend, "trust"),
            None,
            "an executable ambient shadow must not satisfy a missing sibling"
        );

        let sibling = selected_bin.join("targo-trust");
        fs::write(&sibling, b"selected but not executable").expect("write sibling fixture");
        fs::set_permissions(&sibling, fs::Permissions::from_mode(0o644))
            .expect("make sibling nonexecutable");
        assert_eq!(protected_trust_subcommand_path(&frontend, "trust"), None);

        fs::set_permissions(&sibling, fs::Permissions::from_mode(0o755))
            .expect("make sibling executable");
        assert_eq!(
            protected_trust_subcommand_path(&frontend, "trust"),
            Some(sibling)
        );

        fs::remove_file(&selected_bin.join("targo-trust")).expect("remove regular sibling");
        std::os::unix::fs::symlink(&ambient, selected_bin.join("targo-trust"))
            .expect("install sibling symlink shadow");
        assert_eq!(
            protected_trust_subcommand_path(&frontend, "trust"),
            None,
            "protected front doors require a regular sibling executable, not a redirecting symlink"
        );
        let _ = fs::remove_dir_all(root);
    }

    #[cfg(windows)]
    #[test]
    fn protected_windows_handles_deny_hidden_rewrite_and_ancestor_rename() {
        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-windows-lock-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let bin = root.join("bin");
        fs::create_dir_all(&bin).expect("create selected Windows toolchain directory");
        let command = bin.join("targo-trust.exe");
        fs::write(&command, b"selected protected Windows command")
            .expect("write selected Windows command");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected Windows command");
        assert!(
            fs::OpenOptions::new().write(true).open(&command).is_err(),
            "protected executable unexpectedly shared write authority"
        );
        let renamed = root.join("bin-renamed");
        assert!(
            fs::rename(&bin, &renamed).is_err(),
            "protected directory unexpectedly shared delete/rename authority"
        );

        drop(authenticated);
        fs::rename(&bin, &renamed).expect("selection locks are released when the guard is dropped");
        fs::remove_dir_all(root).expect("remove protected Windows fixture");
    }

    /// `<temp>/<unique>/ancestor/bin/targo-trust`: a private chain whose
    /// selected directory and ancestor can be mutated independently.
    #[cfg(unix)]
    fn protected_ancestor_fixture(label: &str) -> (PathBuf, PathBuf, PathBuf, PathBuf) {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-ancestor-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let ancestor = root.join("ancestor");
        let selected_bin = ancestor.join("bin");
        fs::create_dir_all(&selected_bin).expect("create protected ancestor fixture");
        let command = selected_bin.join("targo-trust");
        fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write protected fixture command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make protected fixture command executable");
        (root, ancestor, selected_bin, command)
    }

    /// THE FALSE POSITIVE THIS POLICY CLOSES: a protected compile must not be
    /// invalidated because an unrelated process creates or removes an entry in
    /// an ancestor such as `$HOME` or `/private/tmp`.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_allows_unrelated_ancestor_entry_churn() {
        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let (root, ancestor, _selected_bin, command) = protected_ancestor_fixture("churn");
        let authenticated = AuthenticatedProtectedSubcommand::capture(command)
            .expect("authenticate protected ancestor fixture");

        fs::write(ancestor.join("unrelated.tmp"), b"noise").expect("create unrelated entry");
        authenticated
            .revalidate()
            .expect("ancestor entry creation must preserve authentication");
        fs::remove_file(ancestor.join("unrelated.tmp")).expect("remove unrelated entry");
        authenticated
            .revalidate()
            .expect("ancestor entry removal must preserve authentication");
        fs::create_dir(ancestor.join("unrelated-dir")).expect("create unrelated directory");
        authenticated
            .revalidate()
            .expect("ancestor link-count churn must preserve authentication");

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected ancestor fixture");
    }

    /// The selected toolchain directory remains strict: a new sibling binary
    /// is toolchain churn, not unrelated ancestor churn.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_still_rejects_selected_directory_churn() {
        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let (root, _ancestor, selected_bin, command) = protected_ancestor_fixture("selected-churn");
        let authenticated = AuthenticatedProtectedSubcommand::capture(command)
            .expect("authenticate protected selected directory");

        fs::write(selected_bin.join("new-tool"), b"replacement candidate")
            .expect("create selected-directory sibling");
        assert!(
            authenticated.revalidate().is_err(),
            "selected toolchain directory churn escaped authentication"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected selected-directory fixture");
    }

    /// Renaming an ancestor aside and restoring the same inode leaves a ctime
    /// signature even though identity and permissions match again.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_still_rejects_renamed_and_restored_ancestor() {
        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let (root, ancestor, _selected_bin, command) = protected_ancestor_fixture("rename");
        let parked = root.join("ancestor-parked");
        let authenticated = AuthenticatedProtectedSubcommand::capture(command)
            .expect("authenticate protected ancestor before rename");

        fs::rename(&ancestor, &parked).expect("rename protected ancestor aside");
        fs::rename(&parked, &ancestor).expect("restore protected ancestor");
        assert!(
            authenticated.revalidate().is_err(),
            "rename-and-restore escaped ancestor authentication"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected rename fixture");
    }

    /// Ancestor content is irrelevant, but ancestor rewrite authority is not.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_still_rejects_widened_ancestor_permissions() {
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let (root, ancestor, _selected_bin, command) = protected_ancestor_fixture("permissions");
        let authenticated = AuthenticatedProtectedSubcommand::capture(command)
            .expect("authenticate protected ancestor before permission change");
        let original = fs::metadata(&ancestor)
            .expect("inspect ancestor permissions")
            .permissions();
        let mut widened = original.clone();
        widened.set_mode(original.mode() | 0o022);
        assert_ne!(
            widened.mode(),
            original.mode(),
            "fixture ancestor was already writable"
        );
        fs::set_permissions(&ancestor, widened).expect("widen ancestor permissions");

        assert!(
            authenticated.revalidate().is_err(),
            "widened ancestor authority escaped authentication"
        );

        fs::set_permissions(&ancestor, original).expect("restore ancestor permissions");
        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected permission fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_rejects_rewrite_and_swap_restore() {
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-command-identity-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        fs::create_dir(&root).expect("create protected-command identity fixture");
        let command = root.join("targo-trust");
        let replacement = root.join("replacement");
        let saved = root.join("saved");
        fs::write(&command, b"selected protected command").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected command");
        let rewrite = authenticated.run_guarded(|| {
            fs::write(&command, b"hostile protected command").expect("rewrite selected command");
        });
        assert!(
            rewrite.is_err(),
            "an in-place protected-command rewrite was accepted"
        );
        assert_eq!(
            fs::read(&command).expect("read rewritten command"),
            b"hostile protected command",
            "rewrite fixture did not reach the guarded operation"
        );
        drop(authenticated);

        fs::write(&command, b"selected protected command").expect("restore selected bytes");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("restore selected permissions");
        fs::write(&replacement, b"hostile protected command").expect("write hostile replacement");
        fs::set_permissions(&replacement, fs::Permissions::from_mode(0o755))
            .expect("make hostile replacement executable");
        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("reauthenticate protected command");
        let swap_restore = authenticated.run_guarded(|| {
            fs::rename(&command, &saved).expect("save selected command inode");
            fs::rename(&replacement, &command).expect("install hostile command");
            fs::remove_file(&command).expect("remove hostile command");
            fs::rename(&saved, &command).expect("restore exact selected inode");
        });
        assert!(
            swap_restore.is_err(),
            "a swap-and-restore escaped protected toolchain-directory authentication"
        );
        assert!(
            !replacement.exists(),
            "swap-and-restore fixture did not reach the guarded operation"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected-command identity fixture");
    }

    /// Trust: THE NEGATIVE THAT DEFINES THE RULE. What makes an ancestor symlink
    /// inadmissible is not that it is a symlink — `rustup toolchain link` can
    /// only ever produce one — it is that some principal other than root or the
    /// invoking identity can replace it. A world-writable holding directory is
    /// exactly that primitive and is refused at capture; the SAME symlink is
    /// admitted once the directory is closed again, which is what proves the
    /// refusal is caused by the writability rather than by the redirection.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_rejects_mutable_ancestor_symlink() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-command-symlink-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let real_bin = root.join("real/bin");
        fs::create_dir_all(&real_bin).expect("create real protected-command directory");
        let command = real_bin.join("targo-trust");
        fs::write(&command, b"selected protected command").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");
        let holder = root.join("holder");
        fs::create_dir(&holder).expect("create the directory that holds the hop");
        let redirected_root = holder.join("redirected");
        symlink(root.join("real"), &redirected_root).expect("create mutable ancestor symlink");
        let redirected_command = redirected_root.join("bin/targo-trust");

        fs::set_permissions(&holder, fs::Permissions::from_mode(0o777))
            .expect("make the holding directory world-writable");
        let error = AuthenticatedProtectedSubcommand::capture(redirected_command.clone())
            .err()
            .expect("an ancestor symlink any local principal can replace must be rejected");
        assert!(
            error.contains("group- or world-writable"),
            "the refusal must name the substitution primitive, got: {error}"
        );

        fs::set_permissions(&holder, fs::Permissions::from_mode(0o755))
            .expect("close the holding directory again");
        AuthenticatedProtectedSubcommand::capture(redirected_command).expect(
            "the same ancestor symlink must authenticate once no other principal can replace it",
        );

        fs::remove_dir_all(root).expect("remove protected-command symlink fixture");
    }

    /// Trust: the hop's HOLDING DIRECTORY is an ancestor, so it gets the
    /// ancestor contract `fix(targo): tolerate unrelated protected-ancestor
    /// churn` established for the directory chain — unrelated entries appearing
    /// beside the toolchain symlink must not abort an in-flight subcommand,
    /// because on a real machine that directory is `~/.rustup/toolchains` and
    /// anything may write there. The SYMLINK itself keeps exact metadata: it has
    /// no interior, so it has nothing to churn.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_allows_churn_beside_a_launch_symlink() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-hop-churn-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let sealed_bin = root.join("sealed/bin");
        fs::create_dir_all(&sealed_bin).expect("create sealed toolchain");
        let command = sealed_bin.join("targo-trust");
        fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make command executable");
        // `holder` stands in for `~/.rustup/toolchains`: it holds the toolchain
        // symlink AND whatever else the user happens to install.
        let holder = root.join("holder");
        fs::create_dir(&holder).expect("create the directory holding the hop");
        let linked = holder.join("trust");
        symlink(root.join("sealed"), &linked).expect("create rustup-style symlink");

        let authenticated =
            AuthenticatedProtectedSubcommand::capture(linked.join("bin/targo-trust"))
                .expect("a rustup-style symlinked toolchain must authenticate");

        // Exactly what installing an unrelated toolchain beside this one does.
        let churned = authenticated.run_guarded(|| {
            fs::create_dir(holder.join("unrelated-toolchain")).expect("install a neighbour");
            fs::write(holder.join("unrelated.tmp"), b"noise").expect("write an unrelated entry");
            fs::remove_file(holder.join("unrelated.tmp")).expect("remove it again");
        });
        assert!(
            churned.is_ok(),
            "unrelated churn beside a launch symlink must not break authentication: {churned:?}"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove hop-churn fixture");
    }

    /// Trust: the rustup shape end to end. A linked custom toolchain is always
    /// reached through a symlink, and this machine adds a second, INTERMEDIATE
    /// hop that an atomic promotion rewrites
    /// (`~/.rustup/toolchains/trust -> ~/toolchains/trust-current -> trust-<rev>`).
    /// `Path::ancestors` cannot see that second hop at all, so this test is what
    /// proves the component-by-component resolution walk is load-bearing:
    /// capture succeeds, and flipping the intermediate hop under the guard is
    /// refused.
    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_authenticates_a_rustup_style_symlink_chain() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-rustup-symlink-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let sealed_bin = root.join("sealed/bin");
        let decoy_bin = root.join("decoy/bin");
        fs::create_dir_all(&sealed_bin).expect("create sealed toolchain");
        fs::create_dir_all(&decoy_bin).expect("create decoy toolchain");
        for bin in [&sealed_bin, &decoy_bin] {
            let command = bin.join("targo-trust");
            fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write command");
            fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
                .expect("make command executable");
        }
        let current = root.join("trust-current");
        let linked = root.join("linked");
        symlink(root.join("sealed"), &current).expect("create promotion symlink");
        symlink(&current, &linked).expect("create rustup-style symlink");

        let launched = linked.join("bin/targo-trust");
        let authenticated = AuthenticatedProtectedSubcommand::capture(launched)
            .expect("a rustup-style symlinked toolchain must authenticate");
        assert_eq!(
            authenticated.selected.symlink_hops.len(),
            2,
            "both hops must be pinned, including the intermediate one `Path::ancestors` cannot see"
        );

        let flipped = authenticated.run_guarded(|| {
            let staged = root.join("trust-staged");
            symlink(root.join("decoy"), &staged).expect("stage the replacement");
            fs::rename(&staged, &current).expect("flip the promotion symlink");
        });
        assert!(
            flipped.is_err(),
            "flipping the intermediate promotion symlink under the guard must be refused"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove rustup-style symlink fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_rejects_ancestor_redirect_restore_after_raced_child_runs() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-ancestor-race-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let selected_root = root.join("selected");
        let selected_bin = selected_root.join("bin");
        let attacker_root = root.join("attacker");
        let attacker_bin = attacker_root.join("bin");
        fs::create_dir_all(&selected_bin).expect("create selected toolchain directory");
        fs::create_dir_all(&attacker_bin).expect("create attacker toolchain directory");
        let command = selected_bin.join("targo-trust");
        fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");
        let hostile_command = attacker_bin.join("targo-trust");
        fs::write(&hostile_command, b"#!/bin/sh\nexit 23\n").expect("write hostile command");
        fs::set_permissions(&hostile_command, fs::Permissions::from_mode(0o755))
            .expect("make hostile command executable");
        let saved_root = root.join("selected-saved");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected command and ancestor chain");
        let mut hostile_child_ran = false;
        let result = authenticated.run_guarded(|| {
            fs::rename(&selected_root, &saved_root).expect("save selected toolchain root");
            symlink(&attacker_root, &selected_root).expect("redirect selected toolchain root");
            let status = Command::new(&command)
                .status()
                .expect("run protected command through redirected pathname");
            hostile_child_ran = status.code() == Some(23);
            fs::remove_file(&selected_root).expect("remove attacker redirect");
            fs::rename(&saved_root, &selected_root).expect("restore exact selected toolchain root");
        });

        assert!(
            hostile_child_ran,
            "fixture did not execute the redirected command"
        );
        assert!(
            result.is_err(),
            "an ancestor redirect-and-restore escaped protected subcommand authentication"
        );
        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected-command ancestor-race fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_admits_executable_timestamp_churn_but_rejects_content_change() {
        // Regression: macOS writes the `com.apple.provenance` extended
        // attribute the first time the guard *executes* a protected Mach-O
        // binary, bumping the executable's `ctime` between the pre-launch
        // capture and the post-run revalidation. The cross-time comparison
        // included the full stat snapshot (timestamps and all), so the guard
        // failed the run closed against its own execution side effect: on the
        // first run after every rebuild, `targo trust check` exited 2 with an
        // empty stdout even though the child had produced a complete report.
        // The executable's cross-time identity must ignore OS-mutated
        // timestamps (its device+inode is anchored by the retained handle)
        // while still rejecting a genuine content/size change.
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-timestamp-churn-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let bin = root.join("bin");
        fs::create_dir_all(&bin).expect("create toolchain directory");
        let command = bin.join("targo-trust");
        fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected command and ancestor chain");

        // A timestamp-only change to the executable — exactly what the OS
        // inflicts by writing the provenance xattr on execution — must NOT
        // trip the guard.
        let holds = authenticated.run_guarded(|| {
            let earlier =
                std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
            fs::File::options()
                .write(true)
                .open(&command)
                .expect("open protected command to bump its timestamp")
                .set_modified(earlier)
                .expect("bump protected command mtime (and ctime)");
        });
        assert!(
            holds.is_ok(),
            "an executable timestamp-only change (provenance-xattr churn) must not trip the guard: {:?}",
            holds.err()
        );

        // A genuine content/size change to the executable must STILL fail the
        // guarded run closed.
        let rejects = authenticated.run_guarded(|| {
            fs::write(
                &command,
                b"#!/bin/sh\nexit 0\n# tampered: strictly longer body\n",
            )
            .expect("rewrite protected command with different content");
        });
        assert!(
            rejects.is_err(),
            "a genuine content change to the executable must still fail the guarded run closed"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected-command timestamp-churn fixture");
    }

    #[cfg(unix)]
    #[test]
    fn guarded_subcommand_status_preserves_exit_and_signal_identity() {
        use std::os::unix::process::ExitStatusExt as _;

        let exited = Command::new("sh")
            .args(["-c", "exit 42"])
            .status()
            .expect("run exit-status fixture");
        assert_eq!(subcommand_exit_status_code(&exited), 42);

        let signaled = Command::new("sh")
            .args(["-c", "kill -TERM $$"])
            .status()
            .expect("run signal-status fixture");
        assert_eq!(signaled.signal(), Some(15));
        assert_eq!(subcommand_exit_status_code(&signaled), 128 + 15);
    }

    #[test]
    fn trust_dev_gate_subcommands_bypass_the_protected_guard_but_proof_commands_do_not() {
        // The external command's argv repeats the subcommand token at index 0.
        let argv =
            |tokens: &[&str]| -> Vec<OsString> { tokens.iter().map(OsString::from).collect() };
        // A local `fn` (not a closure) so the returned `&OsStr` borrows tie to
        // the input slice's lifetime.
        fn as_os(v: &[OsString]) -> Vec<&OsStr> {
            v.iter().map(OsString::as_os_str).collect()
        }

        // `targo trust domination …` is a dev/CI gate: it builds (churning the
        // in-tree toolchain ancestors) and dispatches its proof work through
        // separately-guarded nested checks, so the outer wrapper is unguarded.
        let domination = argv(&[
            "trust",
            "domination",
            "trust-added",
            "native-contracts-pipeline-v2",
        ]);
        assert!(trust_invocation_is_dev_gate("trust", &as_os(&domination)));

        // `doctor` is a pure diagnostic (builds an environment report, makes no
        // proof claim), so it is likewise unguarded.
        let doctor = argv(&["trust", "doctor", "--format", "json"]);
        assert!(trust_invocation_is_dev_gate("trust", &as_os(&doctor)));

        // A leading flag before the sub-subcommand must not hide it.
        let flagged = argv(&["trust", "--frozen", "domination", "trust-added"]);
        assert!(trust_invocation_is_dev_gate("trust", &as_os(&flagged)));

        // Proof-producing commands STAY guarded.
        for proof in [
            ["trust", "check"],
            ["trust", "build"],
            ["trust", "test"],
            ["trust", "report"],
        ] {
            let v = argv(&proof);
            assert!(
                !trust_invocation_is_dev_gate("trust", &as_os(&v)),
                "{proof:?} is proof-producing and must remain guarded"
            );
        }

        // Only the `trust` front door has dev-gate subcommands.
        let fmt = argv(&["fmt", "domination"]);
        assert!(!trust_invocation_is_dev_gate("fmt", &as_os(&fmt)));
    }

    #[test]
    fn protected_guard_failure_is_not_reported_as_a_compiler_error() {
        // Regression: a post-run guard trip DISCARDED the child's real
        // `ExitStatus` and returned 101. `targo trust check` therefore exited
        // 101 — cargo's "could not compile" — even though the child had
        // already written a complete sealed report to stdout whose own gate
        // object recorded `exit_code: 1` with complete coverage. Any churn in
        // a recorded ancestor directory (a concurrent build or test writing
        // under `build/`) tripped it, so an ordinary verification-gate
        // failure was indistinguishable from a compiler crash.
        //
        // A guard trip is a toolchain-AUTHORITY failure: exit 2, the code this
        // project's own pipeline uses for every setup/evidence failure.
        let guard_failure: Result<CargoResult<ExitStatus>, String> =
            Err("protected Trust subcommand `x` changed while it was running".to_string());
        let error = finish_guarded_protected_subcommand(guard_failure)
            .expect_err("a guard failure must fail closed");
        assert_eq!(
            error.exit_code, PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
            "a guard failure is a setup/authority failure, not a compiler error"
        );
        assert_ne!(
            error.exit_code, 101,
            "101 is reserved for `could not compile`"
        );

        // When the guard HOLDS, the child's own status governs unchanged —
        // in particular an ordinary verification-gate failure stays exit 1.
        let gate_failure = Command::new("sh")
            .args(["-c", "exit 1"])
            .status()
            .expect("run gate-failure fixture");
        let error = finish_guarded_protected_subcommand(Ok(Ok(gate_failure)))
            .expect_err("a nonzero child status must fail closed");
        assert_eq!(
            error.exit_code, 1,
            "an ordinary verification-gate failure stays exit 1"
        );

        let success = Command::new("sh")
            .args(["-c", "exit 0"])
            .status()
            .expect("run success fixture");
        assert!(
            finish_guarded_protected_subcommand(Ok(Ok(success))).is_ok(),
            "a successful guarded run stays successful"
        );
    }
}

/// Initialize libgit2.
#[tracing::instrument(skip_all)]
fn init_git() {
    // Disabling the owner validation in git can, in theory, lead to code execution
    // vulnerabilities. However, libgit2 does not launch executables, which is the foundation of
    // the original security issue. Meanwhile, issues with refusing to load git repos in
    // `CARGO_HOME` for example will likely be very frustrating for users. So, we disable the
    // validation.
    //
    // For further discussion of Cargo's current interactions with git, see
    //
    //   https://github.com/rust-lang/rfcs/pull/3279
    //
    // and in particular the subsection on "Git support".
    //
    // Note that we only disable this when Cargo is run as a binary. If Cargo is used as a library,
    // this code won't be invoked. Instead, developers will need to explicitly disable the
    // validation in their code. This is inconvenient, but won't accidentally open consuming
    // applications up to security issues if they use git2 to open repositories elsewhere in their
    // code.
    unsafe {
        git2::opts::set_verify_owner_validation(false)
            .expect("set_verify_owner_validation should never fail");
    }
}
