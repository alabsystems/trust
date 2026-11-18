//! Native fixed admission before project configuration. The inner ordinary
//! Targo owns configuration, the compile/test graph and GNU-credit retirement.
//! This standalone entry does not replace an inherited hosted/root protocol.

use std::ffi::{OsStr, OsString};
use std::io::Write as _;
use std::num::{NonZeroU32, NonZeroU64};
use std::process::{Command, ExitStatus};
use std::time::{Duration, Instant};

use anyhow::{Context as _, Result, ensure};
use clap::{Arg, ArgAction};
use trust_build_tree::admission::{
    Attempt, FixedCommandAdmission, FixedCpuRequest, RunningFixedGroup,
};
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use trust_build_tree::admission::ExecutionStartPipe;

#[path = "resource_fixed/adopt.rs"]
mod adopt;
#[path = "resource_fixed/attribution.rs"]
mod attribution;
#[path = "resource_budget.rs"]
mod budget;

const MAX_WAIT_SECONDS: u64 = 7 * 24 * 60 * 60;

fn cli() -> clap::Command {
    clap::Command::new("targo --unverified resource fixed")
        .about("Run an ordinary Targo job, held native tool or repo-lock-exec under fixed host admission")
        .after_help(format!("{}\nSelected tool: targo --unverified resource fixed [sizing] -- fixed-tool -- ABSOLUTE_NATIVE_PROGRAM [args...]\nThe native system-only image is held and checked while stopped before GO. This is original fixed/GNU continuation, not SDK or hosted-runtime authority.", trust_build_tree::trust_repo_lock::management::exec::USAGE))
        .arg(
            Arg::new("cpus")
                .long("cpus")
                .value_parser(clap::value_parser!(NonZeroU32)),
        )
        .arg(
            Arg::new("slots")
                .long("slots")
                .value_parser(clap::value_parser!(NonZeroU32)),
        )
        .arg(
            Arg::new("memory-mib")
                .long("memory-mib")
                .default_value("8192")
                .value_parser(clap::value_parser!(NonZeroU64)),
        )
        .arg(
            Arg::new("wait-seconds")
                .long("wait-seconds")
                .value_parser(clap::value_parser!(NonZeroU64)),
        )
        .arg(
            Arg::new("exclusive")
                .long("exclusive")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("execution-start-fd")
                .long("execution-start-fd")
                .hide(true)
                .value_parser(clap::builder::OsStringValueParser::new()),
        )
        .arg(
            Arg::new("command")
                .required(true)
                .num_args(1..)
                .last(true)
                .value_parser(clap::builder::OsStringValueParser::new()),
        )
}

// Trust: this continuation is reached only with the original fixed claim and
// GNU transport. A fresh caller uses `resource fixed -- fixed-tool -- ...`.
fn fixed_tool_cli() -> clap::Command {
    clap::Command::new("fixed-tool")
        .about("Continue original fixed admission for an absolute native system-only tool")
        .arg(
            Arg::new("command")
                .required(true)
                .num_args(1..)
                .last(true)
                .value_parser(clap::builder::OsStringValueParser::new()),
        )
}

pub(super) fn help_command() -> clap::Command {
    clap::Command::new("resource")
        .about("Native resource admission")
        .subcommand(cli().name("fixed"))
        .subcommand(fixed_tool_cli())
        .subcommand(super::resource_prune::help_command())
        .subcommand(
            clap::Command::new("status")
                .about("Observe the original machine namespace without admission or cleanup")
                .arg(Arg::new("json").long("json").action(ArgAction::SetTrue)),
        )
        .subcommand(adopt::cli().name("adopt"))
        .subcommand(budget::cli().name("budget"))
}

pub(super) fn reject_alias_dispatch(
    _gctx: &mut crate::GlobalContext,
    _args: &clap::ArgMatches,
) -> crate::CliResult {
    Err(anyhow::anyhow!(
        "native resource commands must use the original `targo --unverified resource ...` entry before project configuration"
    ).into())
}

struct Options {
    cpus: FixedCpuRequest,
    slots: Option<NonZeroU32>,
    memory: NonZeroU64,
    memory_explicit: bool,
    exclusive: bool,
    timeout: Option<Duration>,
    command: Vec<OsString>,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    execution_start: Option<ExecutionStartPipe>,
}

// Trust: explicit operation intent, never executable-name inference or an
// admission capability. The existing native owner captures the selected image.
enum CommandIntent<'a> {
    Targo,
    Tool {
        program: &'a OsStr,
        args: &'a [OsString],
    },
}

fn command_intent(command: &[OsString]) -> Result<CommandIntent<'_>> {
    if command.first().is_some_and(|arg| arg == "fixed-tool") {
        ensure!(
            command.get(1).is_some_and(|arg| arg == "--"),
            "fixed-tool requires its explicit -- program delimiter"
        );
        let program = command
            .get(2)
            .context("fixed-tool requires an absolute native program")?;
        ensure!(
            std::path::Path::new(program).is_absolute(),
            "fixed-tool requires an absolute native program; PATH lookup is not image custody"
        );
        return Ok(CommandIntent::Tool {
            program,
            args: &command[3..],
        });
    }
    ensure!(
        command
            .first()
            .and_then(|arg| arg.to_str())
            .is_some_and(|arg| {
                matches!(
                    arg,
                    "build"
                        | "check"
                        | "test"
                        | "run"
                        | "bench"
                        | "doc"
                        | "rustc"
                        | "rustdoc"
                        | "repo-lock-exec"
                        | "repo-prune"
                )
            }),
        "native fixed admission requires an ordinary Targo command, fixed-tool, or exact repo-lock-exec after --"
    );
    Ok(CommandIntent::Targo)
}

fn options(args: &[OsString]) -> Result<Options> {
    let matches = cli().try_get_matches_from(
        std::iter::once(OsString::from("resource fixed")).chain(args.iter().cloned()),
    )?;
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    let execution_start = matches
        .get_one::<OsString>("execution-start-fd")
        .map(|value| ExecutionStartPipe::from_descriptor(value))
        .transpose()?;
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    ensure!(
        matches.get_one::<OsString>("execution-start-fd").is_none(),
        "native loaded execution-start is unavailable on this platform; no command started"
    );
    let command = matches
        .get_many::<OsString>("command")
        .expect("required command")
        .cloned()
        .collect::<Vec<_>>();
    let _ = command_intent(&command)?;
    let memory = matches
        .get_one::<NonZeroU64>("memory-mib")
        .expect("default memory")
        .get()
        .checked_mul(1024 * 1024)
        .and_then(NonZeroU64::new)
        .context("native fixed memory floor is unrepresentable")?;
    let timeout = matches
        .get_one::<NonZeroU64>("wait-seconds")
        .map(|seconds| {
            ensure!(
                seconds.get() <= MAX_WAIT_SECONDS,
                "native fixed wait exceeds seven days"
            );
            Ok(Duration::from_secs(seconds.get()))
        })
        .transpose()?;
    Ok(Options {
        cpus: matches
            .get_one::<NonZeroU32>("cpus")
            .copied()
            .map_or(FixedCpuRequest::Automatic, FixedCpuRequest::Limit),
        slots: matches.get_one::<NonZeroU32>("slots").copied(),
        memory,
        memory_explicit: matches.value_source("memory-mib")
            == Some(clap::parser::ValueSource::CommandLine),
        exclusive: matches.get_flag("exclusive"),
        timeout,
        command,
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        execution_start,
    })
}

#[expect(
    clippy::disallowed_methods,
    reason = "reject live inherited admission locators before configuration; a project environment snapshot cannot authorize replacement of their original owners"
)]
fn check_ancestors() -> Result<()> {
    // These locators cannot authorize a new root. Refuse even an unusable
    // locator rather than replacing/borrowing its original native owner.
    for name in [
        "BUILD_SLOT_HELD",
        "ATERM_RESOURCE_JOB_V3",
        "ATERM_SDK_LEASE_V3",
        "TRUST_CPU_HANDOFF",
        "TRUST_CPU_IMPLICIT_FD",
        "TRUST_FIXED_CLAIM_HANDOFF_V1",
        trust_build_tree::admission::FIXED_HANDOFF_ENV,
    ] {
        ensure!(
            std::env::var_os(name).is_none(),
            "native fixed admission cannot replace original {name}; run outside that admission"
        );
    }
    Ok(())
}

/// Route observation captured before any descriptor-opening startup callback.
/// Neither variant grants admission until its original owner is authenticated.
pub(super) enum NestedInput {
    Direct(trust_build_tree::admission::EarlyFixedClaim),
    Courier(OsString),
}

#[expect(
    clippy::disallowed_methods,
    reason = "capture the original direct/courier admission advertisements at native entry before any configuration or descriptor-opening callback"
)]
pub(super) fn snapshot_nested(args: &[OsString]) -> std::io::Result<Option<NestedInput>> {
    if args.get(..3).is_none_or(|prefix| {
        prefix[..2] != ["--unverified", "resource"]
            || !matches!(
                prefix[2].to_str(),
                Some("fixed" | "fixed-tool" | "repo-prune" | "budget")
            )
    }) {
        return Ok(None);
    }
    let direct = std::env::var_os(trust_build_tree::admission::FIXED_HANDOFF_ENV);
    let courier = std::env::var_os(cargo_util::FIXED_CLAIM_HANDOFF_ENV);
    nested_input(direct, courier)
}

fn nested_input(
    direct: Option<OsString>,
    courier: Option<OsString>,
) -> std::io::Result<Option<NestedInput>> {
    match (direct, courier) {
        (Some(direct), Some(courier)) if direct == "requires-live-ancestor-v1" => {
            Ok(Some(NestedInput::Courier(courier)))
        }
        (_, Some(_)) => Err(std::io::Error::other(
            "fixed original courier requires its old-reader refusal sentinel",
        )),
        (Some(direct), None) => trust_build_tree::admission::EarlyFixedClaim::snapshot(&direct)
            .map(NestedInput::Direct)
            .map(Some),
        (None, None) => Ok(None),
    }
}

fn nested_budget(
    request: FixedCpuRequest,
    caller: Option<&OsStr>,
    original: NonZeroU32,
) -> Result<NonZeroU32> {
    let requested = match request {
        FixedCpuRequest::Automatic => original,
        FixedCpuRequest::Limit(value) => value,
    };
    ensure!(
        requested <= original,
        "nested command exceeds its original fixed CPU budget"
    );
    // Caller counts may reduce an authentic ceiling, never create one. Keep
    // earlier local reductions even when this nested CLI asks for more jobs.
    Ok(match caller_request(FixedCpuRequest::Automatic, caller)? {
        FixedCpuRequest::Automatic => requested,
        FixedCpuRequest::Limit(cap) => requested.min(cap),
    })
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[expect(
    clippy::disallowed_methods,
    reason = "retain the live inherited admission and caller ceiling, and remove actual loader overrides from the nested native image before launch"
)]
fn run_nested(options: Options, input: NestedInput) -> Result<i32> {
    for name in [
        "BUILD_SLOT_HELD",
        "ATERM_RESOURCE_JOB_V3",
        "ATERM_SDK_LEASE_V3",
        "TRUST_CPU_HANDOFF",
        "TRUST_CPU_IMPLICIT_FD",
    ] {
        ensure!(
            std::env::var_os(name).is_none(),
            "nested fixed admission cannot replace original {name}"
        );
    }
    ensure!(
        options.slots.is_none(),
        "nested fixed admission cannot select another slot reservation"
    );
    ensure!(
        !options.memory_explicit,
        "nested fixed admission retains its original memory admission"
    );
    ensure!(
        options.timeout.is_none(),
        "nested fixed admission has no new admission wait"
    );
    ensure!(
        options
            .command
            .first()
            .is_none_or(|arg| arg != "repo-lock-exec"),
        "nested held exec requires its separately supported original entry"
    );
    let original = match input {
        NestedInput::Direct(early) => early.capture()?,
        NestedInput::Courier(courier) => {
            trust_build_tree::admission::InheritedFixedClaim::from_descendant(&courier)?
        }
    };
    let budget = nested_budget(
        options.cpus,
        std::env::var_os("CARGO_BUILD_JOBS").as_deref(),
        original.budget()?,
    )?;
    let context = crate::GlobalContext::default()?;
    let scheduler = context
        .jobserver_from_env()?
        .context("nested fixed admission requires its original GNU transport")?
        .clone();
    let worktree = worktree_lock()?;
    let output_directory = original.original_output_cwd()?;
    let intent = command_intent(&options.command)?;
    let mut command = match &intent {
        CommandIntent::Targo => {
            let mut command = Command::new(std::env::current_exe()?);
            command.arg("--unverified");
            command
        }
        CommandIntent::Tool { program, args } => {
            let mut command = Command::new(program);
            command.args(*args);
            command
        }
    };
    // The selected self image has the closed native system-only load profile.
    // Do not carry Cargo's generated build-script loader search list, or any
    // other loader override, into this known frontend. This chooses no alternate
    // image or runtime; the actual stopped image is still checked before GO.
    // An explicitly selected tool keeps its requested environment semantics:
    // the held native owner refuses loader overrides instead of deleting them.
    if matches!(intent, CommandIntent::Targo) {
        for (name, _) in std::env::vars_os() {
            if name.as_encoded_bytes().starts_with(b"DYLD_")
                || name.as_encoded_bytes().starts_with(b"LD_")
            {
                command.env_remove(name);
            }
        }
        if options
            .command
            .first()
            .is_some_and(|arg| arg == "repo-prune")
        {
            command.arg("resource");
        }
        command.args(&options.command);
    }
    // SAFETY: the original native entry captures this GNU transport exactly
    // once. The checked fixed originals and same worktree are retained, Host/
    // SDK/worker routes were refused, and this wrapper waits serially while
    // the outer owner continues to own group signalling/retirement. This
    // command retains console stdio. A V2 output continuation additionally
    // pins its SAME actual current directory for native child-only fchdir;
    // it cannot substitute a pathname or manufacture V1 membership.
    let prepared = unsafe {
        if let Some(directory) = output_directory {
            original.prepare_nested_output_command(
                command,
                scheduler,
                budget,
                directory,
                options.exclusive,
                Instant::now()
                    .checked_add(Duration::from_secs(30))
                    .context("nested output input deadline overflow")?,
            )?
        } else {
            original.prepare_nested_command(
                command,
                scheduler,
                budget,
                worktree.as_deref(),
                options.exclusive,
                Instant::now()
                    .checked_add(Duration::from_secs(30))
                    .context("nested input deadline overflow")?,
            )?
        }
    };
    let prepared = match options.execution_start {
        Some(pipe) => prepared.with_execution_start(pipe)?,
        None => prepared,
    };
    let mut owner = prepared.spawn()?;
    // Same existing group: the outer owner retains all group signalling and
    // descendant retirement. This wrapper waits only for its actual child.
    let status = owner.wait()?;
    Ok(exit_code(status))
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
fn run_nested(_options: Options, _input: NestedInput) -> Result<i32> {
    anyhow::bail!("native nested image owner is unavailable on this platform; no command started")
}

fn caller_request(request: FixedCpuRequest, caller: Option<&OsStr>) -> Result<FixedCpuRequest> {
    let caller = caller
        .map(|value| {
            value
                .to_str()
                .filter(|text| !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()))
                .and_then(|text| text.parse::<NonZeroU32>().ok())
                .context("native fixed caller CARGO_BUILD_JOBS must be a positive integer")
        })
        .transpose()?;
    Ok(match (request, caller) {
        (FixedCpuRequest::Automatic, Some(cap)) => FixedCpuRequest::Limit(cap),
        (request, _) => request,
    })
}

fn worktree_lock() -> Result<Option<std::path::PathBuf>> {
    match git2::Repository::discover(std::env::current_dir()?) {
        Ok(repo) => Ok(Some(repo.path().canonicalize()?.join("build-slot.lock"))),
        Err(error) if error.code() == git2::ErrorCode::NotFound => Ok(None),
        Err(error) => Err(error).context("cannot resolve original worktree admission namespace"),
    }
}

/// Exact original argv entry, before aliases/configuration or a compiler query.
/// Returning None leaves every other Targo/Cargo dispatch unchanged.
#[expect(
    clippy::disallowed_methods,
    reason = "snapshot the actual original fixed-exec locator before configuration can replace its descriptor custody input"
)]
pub(super) fn snapshot_exec(
    args: &[OsString],
) -> std::io::Result<Option<trust_build_tree::admission::EarlyFixedClaim>> {
    if args
        .get(..3)
        .is_some_and(|prefix| prefix == ["--unverified", "resource", "repo-lock-exec"])
    {
        std::env::var_os(trust_build_tree::admission::FIXED_HANDOFF_ENV)
            .map(|value| trust_build_tree::admission::EarlyFixedClaim::snapshot(&value))
            .transpose()
    } else {
        Ok(None)
    }
}

#[expect(
    clippy::disallowed_methods,
    reason = "fixed admission uses the live original caller CARGO_BUILD_JOBS ceiling before project configuration, never a configured substitute"
)]
pub(super) fn dispatch(
    args: &[OsString],
    early: Option<trust_build_tree::admission::EarlyFixedClaim>,
    nested: Option<NestedInput>,
) -> Option<Result<i32>> {
    if args.first().is_some_and(|arg| arg == "resource") {
        return Some(Err(anyhow::anyhow!(
            "native resource commands require the original `targo --unverified resource ...` entry"
        )));
    }
    if args
        .get(..2)
        .is_none_or(|prefix| prefix != ["--unverified", "resource"])
    {
        return None;
    }
    Some((|| {
        if args.get(2).is_some_and(|arg| arg == "fixed-tool") {
            if args.len() == 4 && matches!(args[3].to_str(), Some("--help" | "-h")) {
                fixed_tool_cli().print_help()?;
                let mut output = std::io::stdout().lock();
                writeln!(output)?;
                output.flush()?;
                return Ok(0);
            }
            let matches = fixed_tool_cli().try_get_matches_from(
                std::iter::once(OsString::from("fixed-tool")).chain(args[3..].iter().cloned()),
            )?;
            let command = matches
                .get_many::<OsString>("command")
                .context("missing selected native tool")?;
            let options = options(
                &std::iter::once(OsString::from("--"))
                    .chain([OsString::from("fixed-tool"), OsString::from("--")])
                    .chain(command.cloned())
                    .collect::<Vec<_>>(),
            )?;
            return run_nested(options, nested.context(
                "fixed-tool requires an authenticated original fixed claim; use resource fixed -- fixed-tool -- PROGRAM outside an existing admission",
            )?);
        }
        if args.get(2).is_some_and(|arg| arg == "budget") {
            return budget::dispatch(&args[3..], nested);
        }
        if args.get(2).is_some_and(|arg| arg == "status") {
            trust_build_tree::admission::status::command(
                &args[3..],
                &mut std::io::stdout().lock(),
            )?;
            return Ok(0);
        }
        if args.get(2).is_some_and(|arg| arg == "repo-prune") {
            return super::resource_prune::run(&args[3..], nested);
        }
        if args.get(2).is_some_and(|arg| arg == "adopt") {
            return adopt::dispatch(&args[3..]);
        }
        if args.get(2).is_some_and(|arg| arg == "repo-lock-exec") {
            let context = crate::GlobalContext::default()?;
            return trust_build_tree::trust_repo_lock::management::exec::run(
                &args[3..],
                context.jobserver_from_env()?,
                early,
            )
            .map_err(Into::into);
        }
        ensure!(
            args.get(2).is_some_and(|arg| arg == "fixed"),
            "use `targo --unverified resource fixed --help` or `targo --unverified resource status`"
        );
        if args
            .get(3)
            .is_some_and(|arg| arg == "--help" || arg == "-h")
            && args.len() == 4
        {
            cli().print_help()?;
            let mut output = std::io::stdout().lock();
            writeln!(output)?;
            output.flush()?;
            return Ok(0);
        }
        let options = options(&args[3..])?;
        if matches!(
            command_intent(&options.command)?,
            CommandIntent::Tool { .. }
        ) {
            ensure!(
                cfg!(all(target_os = "macos", target_arch = "aarch64")),
                "held selected-tool execution is unavailable on this platform; no admission or child started"
            );
        }
        if let Some(input) = nested {
            return run_nested(options, input);
        }
        check_ancestors()?;
        // A caller cap may reduce sizing but cannot manufacture capacity.
        // Do not borrow every idle share for an already capped invocation.
        let request = caller_request(
            options.cpus,
            std::env::var_os("CARGO_BUILD_JOBS").as_deref(),
        )?;
        // Minimal context only: the early importer already owns the original
        // GNU transport. No project configuration or compiler query runs here.
        let context = crate::GlobalContext::default()?;
        let started = Instant::now();
        let deadline = options
            .timeout
            .map(|timeout| {
                started
                    .checked_add(timeout)
                    .context("native fixed wait deadline is unrepresentable")
            })
            .transpose()?;
        let repo_exec = options
            .command
            .first()
            .is_some_and(|arg| arg == "repo-lock-exec");
        let selected_tool = matches!(
            command_intent(&options.command)?,
            CommandIntent::Tool { .. }
        );
        let mut command = Command::new(std::env::current_exe()?);
        command.arg("--unverified");
        if repo_exec
            || selected_tool
            || options
                .command
                .first()
                .is_some_and(|arg| arg == "repo-prune")
        {
            command.arg("resource");
        }
        command.args(&options.command);
        // This bounded control-only discovery precedes machine acquisition.
        // No producing target or original fixed descriptors are delivered by
        // the probe. A failed/unknown probe therefore cannot release a claim
        // whose command scope might still be live.
        let mut command = attribution::command(&context, command, deadline)?;
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let native_image = if options.execution_start.is_some() {
            Some(trust_resource_provenance::program::HeldSystemCommand::open(
                std::path::Path::new(command.get_program()),
                deadline
                    .unwrap_or_else(|| Instant::now() + Duration::from_secs(30))
                    .min(Instant::now() + Duration::from_secs(30)),
            ).context("capture original native execution-start orchestrator")?)
        } else {
            None
        };
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let observed_launch = native_image.is_some();
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        let observed_launch = false;
        let mut admission = FixedCommandAdmission::for_current_user(
            worktree_lock()?,
            options.slots,
            options.exclusive,
            request,
            options.memory,
        )?;
        let mut previous_wait = None;
        let claim = loop {
            ensure!(
                deadline.is_none_or(|until| Instant::now() < until),
                "native fixed admission timed out; no command started"
            );
            match admission
                .attempt()
                .context("native fixed admission attempt")?
            {
                Attempt::Admitted(claim) => {
                    ensure!(
                        deadline.is_none_or(|until| Instant::now() < until),
                        "native fixed admission timed out; no command started"
                    );
                    break claim;
                }
                Attempt::Waiting(reason) => {
                    let reason = format!("{reason:?}");
                    if previous_wait.as_ref() != Some(&reason) {
                        // Diagnostics must not panic or interrupt native ownership.
                        let _ = writeln!(
                            std::io::stderr().lock(),
                            "targo: waiting for native fixed admission: {reason}"
                        );
                        previous_wait = Some(reason);
                    }
                    std::thread::sleep(Duration::from_millis(50));
                }
            }
        };
        let claim = if observed_launch {
            claim
                .with_original_output_member()
                .context("issue original fixed Root output member")?
        } else {
            claim
        };
        // Only a standalone owned fixed root without an inherited scheduler
        // creates its one original GNU server. Consume its real implicit credit
        // exactly as ordinary Cargo does; inner exec never creates a pool.
        let repo_prune = options
            .command
            .first()
            .is_some_and(|arg| arg == "repo-prune");
        let original_exec_server = if (repo_exec || repo_prune || selected_tool || observed_launch)
            && context.jobserver_from_env()?.is_none()
        {
            let mut original = cargo_util::Jobserver::new(claim.budget().get() as usize)
                .context("create original admitted fixed GNU transport")?;
            original
                .client()
                .acquire_raw()
                .context("retain original fixed implicit GNU credit")?;
            original
                .enable_descendant_handoff()
                .context("retain original fixed GNU courier")?;
            Some(original)
        } else {
            None
        };
        if let Some(original) = original_exec_server
            .as_ref()
            .or(context.jobserver_from_env()?)
        {
            // Imported numeric slots are stale after early capture. Export
            // only the actual retained transport into ALL three GNU aliases.
            original.configure_make(&mut command);
        }
        let prepared = if options.exclusive {
            let remaining = deadline.map_or(Duration::from_secs(MAX_WAIT_SECONDS), |until| {
                until.saturating_duration_since(Instant::now())
            });
            claim
                .prepare_exclusive_command(command, remaining)
                .context("prepare original exclusive command")?
        } else {
            claim
                .prepare_command(command)
                .context("prepare original fixed command")?
        };
        ensure!(
            deadline.is_none_or(|until| Instant::now() < until),
            "native fixed admission timed out; no command started"
        );
        let launch_deadline =
            deadline.unwrap_or_else(|| Instant::now() + Duration::from_secs(MAX_WAIT_SECONDS));
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let mut owner = if let Some(image) = native_image {
            let scheduler = original_exec_server
                .as_ref()
                .or(context.jobserver_from_env()?)
                .context("native execution-start requires the same original GNU server")?
                .clone();
            // SAFETY: this command was built here without caller callbacks,
            // cwd/stdio redirection, arg0 or env_clear. Only preparation's own
            // descriptor callback is replaced. This SAME original GNU server
            // consumed its admitted implicit credit above and is paused while
            // the child runs; the returned owner retains the complete group.
            unsafe {
                prepared.spawn_loaded_group_with_signal_forwarding_before(
                    image,
                    scheduler,
                    options.execution_start,
                    launch_deadline,
                )
            }
        } else {
            prepared.spawn_group_with_signal_forwarding_before(launch_deadline)
        }
        .context("launch original fixed command group")?;
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        let mut owner = prepared
            .spawn_group_with_signal_forwarding_before(launch_deadline)
            .context("launch original fixed command group")?;
        let status = wait_owner(&mut owner)?;
        // Keep the original claim through the actual owning wait. This entry
        // inherits console streams; it owns no detached output-reader task.
        Ok(exit_code(status))
    })())
}

fn wait_owner(owner: &mut RunningFixedGroup) -> Result<ExitStatus> {
    match owner.wait() {
        Ok(status) => Ok(status),
        Err(original) => {
            // The standalone process must stay alive with its actual claim
            // until retirement is established. Forgetting a claim then exiting
            // would release its kernel files while children might still run.
            // A diagnostic failure must never skip cancellation/retirement.
            let _ = writeln!(
                std::io::stderr().lock(),
                "targo: original group wait failed; cancelling while retaining native resources: {original}"
            );
            let mut previous = None;
            loop {
                match owner.cancel() {
                    Ok(_) => {
                        return Err(original)
                            .context("native fixed wait failed; original group retired");
                    }
                    Err(error) => {
                        let error = error.to_string();
                        if previous.as_ref() != Some(&error) {
                            let _ = writeln!(
                                std::io::stderr().lock(),
                                "targo: original group retirement unknown; retaining native resources: {error}"
                            );
                            previous = Some(error);
                        }
                        std::thread::sleep(Duration::from_secs(1));
                    }
                }
            }
        }
    }
}

fn exit_code(status: ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt as _;
    status
        .code()
        .unwrap_or_else(|| 128 + status.signal().unwrap_or(1))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn words(args: &[&str]) -> Vec<OsString> {
        args.iter().map(OsString::from).collect()
    }

    #[test]
    fn selected_tool_requires_an_explicit_absolute_image_without_path_or_shell_fallback() {
        for command in [
            vec!["fixed-tool"],
            vec!["fixed-tool", "/native/tool"],
            vec!["fixed-tool", "--"],
            vec!["fixed-tool", "--", "tool"],
            vec!["fixed-tool", "--", "./tool"],
        ] {
            assert!(command_intent(&words(&command)).is_err(), "{command:?}");
        }
        let command = words(&["fixed-tool", "--", "/native/tool", "--cpus", "99", ";"]);
        let CommandIntent::Tool { program, args } = command_intent(&command).unwrap() else {
            panic!("explicit selected tool became ordinary Targo dispatch");
        };
        assert_eq!(program, OsStr::new("/native/tool"));
        assert_eq!(args, words(&["--cpus", "99", ";"]).as_slice());
    }

    #[test]
    fn selected_tool_without_original_custody_cannot_open_its_image_or_acquire_a_new_claim() {
        // This nonexistent image must not even be opened before authentic
        // original custody. In particular, no ordinary/unmanaged fallback is
        // attempted and no GlobalContext or machine admission is constructed.
        let error = dispatch(
            &words(&[
                "--unverified",
                "resource",
                "fixed-tool",
                "--",
                "/missing-original-custody/native-tool",
            ]),
            None,
            None,
        )
        .unwrap()
        .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("requires an authenticated original fixed claim"),
            "{error:#}"
        );
    }

    #[test]
    fn fixed_parser_preserves_the_complete_inner_command_and_its_test_delimiter() {
        let parsed = options(&words(&[
            "--cpus", "3", "--", "test", "--tests", "--", "--exact", "one",
        ]))
        .unwrap();
        assert_eq!(
            parsed.command,
            words(&["test", "--tests", "--", "--exact", "one"])
        );
        assert_eq!(
            parsed.cpus,
            FixedCpuRequest::Limit(NonZeroU32::new(3).unwrap())
        );
        assert_eq!(parsed.memory.get(), 8192 * 1024 * 1024);
    }

    #[test]
    fn fixed_exec_selects_only_the_exact_native_inner_route() {
        let parsed = options(&words(&[
            "--cpus",
            "1",
            "--",
            "repo-lock-exec",
            "--repo-root",
            "/tree",
            "--",
            "/native/bootstrap",
            "--help",
        ]))
        .unwrap();
        assert_eq!(
            parsed.command,
            words(&[
                "repo-lock-exec",
                "--repo-root",
                "/tree",
                "--",
                "/native/bootstrap",
                "--help"
            ])
        );
        assert!(
            options(&words(&[
                "--",
                "trust",
                "repo",
                "lock",
                "exec",
                "--",
                "/native/bootstrap"
            ]))
            .is_err()
        );
        assert!(
            options(&words(&[
                "--",
                "resource",
                "repo-lock-exec",
                "--",
                "/native/bootstrap"
            ]))
            .is_err()
        );
    }

    #[test]
    fn malformed_sizing_and_noncompile_entries_refuse_before_any_admission() {
        for args in [
            vec!["--cpus", "0", "--", "check"],
            vec!["--slots", "0", "--", "check"],
            vec!["--memory-mib", "18446744073709551615", "--", "check"],
            vec!["--wait-seconds", "604801", "--", "check"],
            vec!["--", "trust", "check"],
            vec!["--", "resource", "fixed"],
        ] {
            assert!(options(&words(&args)).is_err(), "{args:?}");
        }
    }

    #[test]
    fn entry_cannot_infer_lane_consent_or_reinterpret_an_inner_delimiter() {
        assert!(
            dispatch(&words(&["resource", "fixed", "--", "check"]), None, None)
                .unwrap()
                .is_err()
        );
        assert!(
            dispatch(&words(&["--unverified", "resource", "unknown"]), None, None)
                .unwrap()
                .is_err()
        );
        assert!(
            dispatch(
                &words(&["--unverified", "check", "--", "resource", "fixed"]),
                None,
                None
            )
            .is_none()
        );
    }

    #[test]
    fn automatic_sizing_retains_the_actual_caller_cap_without_borrowing_idle_extras() {
        let limit = FixedCpuRequest::Limit(NonZeroU32::new(3).unwrap());
        assert_eq!(
            caller_request(FixedCpuRequest::Automatic, Some(OsStr::new("3"))).unwrap(),
            limit
        );
        assert_eq!(
            caller_request(FixedCpuRequest::Automatic, None).unwrap(),
            FixedCpuRequest::Automatic
        );
        assert_eq!(caller_request(limit, Some(OsStr::new("1"))).unwrap(), limit);
    }

    #[test]
    fn invalid_caller_caps_cannot_reach_native_admission() {
        for cap in ["", "0", "-1", "+3", "no", "4294967296"] {
            assert!(
                caller_request(FixedCpuRequest::Automatic, Some(OsStr::new(cap))).is_err(),
                "{cap}"
            );
        }
    }

    #[test]
    fn nested_requests_preserve_the_actual_parent_and_earlier_local_ceiling() {
        let parent = NonZeroU32::new(3).unwrap();
        assert_eq!(
            nested_budget(FixedCpuRequest::Automatic, None, parent).unwrap(),
            parent
        );
        assert_eq!(
            nested_budget(FixedCpuRequest::Automatic, Some(OsStr::new("2")), parent)
                .unwrap()
                .get(),
            2
        );
        assert_eq!(
            nested_budget(
                FixedCpuRequest::Limit(parent),
                Some(OsStr::new("1")),
                parent
            )
            .unwrap()
            .get(),
            1
        );
        assert!(
            nested_budget(
                FixedCpuRequest::Limit(NonZeroU32::new(4).unwrap()),
                Some(OsStr::new("1")),
                parent
            )
            .is_err()
        );
        for caller in ["0", "-1", "arbitrary"] {
            assert!(
                nested_budget(FixedCpuRequest::Automatic, Some(OsStr::new(caller)), parent)
                    .is_err()
            );
        }
        assert!(!options(&words(&["--", "check"])).unwrap().memory_explicit);
        assert!(
            options(&words(&["--memory-mib", "8192", "--", "check"]))
                .unwrap()
                .memory_explicit
        );
    }

    #[test]
    fn nested_route_requires_original_packet_or_complete_old_reader_refusal_binding() {
        assert!(nested_input(None, None).unwrap().is_none());
        for direct in [None, Some("0"), Some("3")] {
            assert!(
                nested_input(direct.map(OsString::from), Some("not-authority".into())).is_err()
            );
        }
        for direct in ["0", "requires-live-ancestor-v1"] {
            assert!(nested_input(Some(direct.into()), None).is_err());
        }
        // This only snapshots inert routing. The distinct live original
        // importer must still authenticate it before any work can start.
        assert!(matches!(
            nested_input(
                Some("requires-live-ancestor-v1".into()),
                Some("routing-only".into())
            )
            .unwrap(),
            Some(NestedInput::Courier(_))
        ));
    }
}
