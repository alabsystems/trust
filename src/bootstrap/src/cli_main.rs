//! bootstrap, the Rust build system
//!
//! This is the entry point for the build system used to compile the `rustc`
//! compiler. Lots of documentation can be found in the `README.md` file in the
//! parent directory, and otherwise documentation can be found throughout the `build`
//! directory in each respective module.

#[cfg(not(unix))]
use std::fs::TryLockError;
use std::fs::{self, OpenOptions};
#[cfg(not(unix))]
use std::io::Read;
use std::io::{self, BufRead, BufReader, IsTerminal, Write};
use std::path::Path;
use std::str::FromStr;
use std::sync::Once;
use std::time::Instant;
use std::{env, process};

use crate::core::builder::StepStack;
use crate::core::config::flags::{Flags, Subcommand};
use crate::core::config::{ChangeId, Config};
use crate::core::session::Session;
use crate::debug;
use crate::utils::change_tracker::{
    CONFIG_CHANGE_HISTORY, find_recent_config_change_ids, human_readable_changes,
};
use crate::utils::helpers::t;

fn is_tracing_enabled() -> bool {
    cfg!(feature = "tracing")
}

pub fn main() {
    // Trust: the same native policy as `targo trust repo lock`, before any
    // configuration, Step graph, build-tree ownership or source preflight.
    if env::args_os().nth(1).as_deref() == Some(std::ffi::OsStr::new("--trust-build-tree-lock")) {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        process::exit(
            build_helper::trust_repo_lock::management::cli::run(
                &env::args_os().skip(2).collect::<Vec<_>>(),
            )
            .into(),
        );
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            eprintln!("native build-tree management is unavailable on this platform");
            process::exit(2);
        }
    }

    // Trust: pure compiled scope classification before any writer/admission.
    if env::args_os().nth(1).as_deref()
        == Some(std::ffi::OsStr::new("--trust-preparation-scope-v1"))
    {
        let args = env::args_os().skip(2).collect::<Vec<_>>();
        let result = if args.first().is_some_and(|arg| arg == "--") {
            crate::engine::xpy_preparation_scope(&args[1..])
        } else {
            Err("scope classification requires -- before complete x.py arguments".into())
        };
        match result {
            Ok(scope) => {
                let value = match scope {
                    crate::engine::PreparationScope::NotProducer => "none",
                    crate::engine::PreparationScope::RequestSources => "request",
                    crate::engine::PreparationScope::FullEnvelope => "full",
                };
                println!("trust-bootstrap-preparation-scope-v1 {value}");
            }
            Err(error) => {
                eprintln!("bootstrap: source classification: {error}");
                process::exit(2);
            }
        }
        return;
    }

    // Trust: a syscall-only compatibility operation for the existing facade.
    // Run before configuration, preflight, build ownership or the Step graph.
    if env::args_os().nth(1).as_deref() == Some(std::ffi::OsStr::new("--trust-build-lock-guard")) {
        let args = env::args_os().skip(2).collect::<Vec<_>>();
        if args == [std::ffi::OsString::from("--protocol")] {
            println!("trust-build-namespace-flock-v1");
            return;
        }
        #[cfg(unix)]
        let result = (|| {
            if args.len() != 2 {
                return Err("expected root and inherited descriptor".to_owned());
            }
            let fd = args[1]
                .to_str()
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| "invalid inherited descriptor".to_owned())?;
            build_helper::trust_build_lock::lock_inherited(Path::new(&args[0]), fd)
                .map_err(|error| error.to_string())
        })();
        #[cfg(not(unix))]
        let result: Result<(), String> = Err("namespace flock requires Unix".into());
        if let Err(error) = result {
            eprintln!("bootstrap: build namespace guard: {error}");
            process::exit(2);
        }
        println!("trust-build-namespace-held-v1");
        return;
    }

    let args = env::args().skip(1).collect::<Vec<_>>();
    if let Err(error) = run_explicit(&args, None) {
        eprintln!("bootstrap: {error}");
        process::exit(2);
    }
}

pub(crate) fn run_explicit(
    args: &[String],
    mut embedded: Option<crate::engine::Policy<'_>>,
) -> Result<crate::engine::Outcome, String> {
    #[cfg(feature = "tracing")]
    let guard = crate::utils::tracing::setup_tracing("BOOTSTRAP_TRACING");

    let _start_time = Instant::now();

    let default_panic_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        static BACKTRACE_LOCK: Once = Once::new();

        // Always print backtraces to provide richer errors, to help debug hard-to-reproduce panics
        // when the user didn't specify RUST_BACKTRACE
        // Note that we only override this variable in the panic handler, because bootstrap might
        // manually capture backtraces when a command is executed, and in that case we do not want
        // to always force backtraces.
        BACKTRACE_LOCK.call_once(|| {
            if std::env::var("RUST_BACKTRACE").is_err() {
                unsafe {
                    std::env::set_var("RUST_BACKTRACE", "1");
                }
            }
        });

        default_panic_hook(info);
        StepStack::with_current(|stack| {
            eprintln!("\nBootstrap has panicked, currently active steps:");
            for step in stack.get_active_steps() {
                eprintln!("{} at {}", step.info, step.location);
            }
        });
    }));

    if Flags::try_parse_verbose_help(args) {
        return Ok(crate::engine::Outcome::empty());
    }

    debug!("parsing flags");
    let flags = Flags::parse(args);
    // Preserve the actual caller's complete parser input before Config reads
    // includes/profiles/overrides. A later source-only Python request has no
    // such selection, and must not reconstruct it or choose default flags.
    let original_preparation_configuration =
        crate::engine::capture_original_configuration(args, &flags);
    // Trust: an embedded producing profile cannot waive the actual configured
    // SDK/compiler version observations before its original source scope.
    if embedded.is_some() {
        crate::engine::validate_flags(&flags)?;
    }
    // Trust: the versioned flag makes an older bootstrap refuse before it can
    // execute an unprotected native workflow. It conveys no release authority:
    // validate the actual live parent now, and again when acquiring the lease.
    if flags.cmd.trust_repo_parent_release_v1() {
        crate::utils::trust_repo_lock::require_parent_handoff().unwrap_or_else(|error| {
            eprintln!("native repository check: {error}");
            process::exit(2);
        });
    }
    debug!("parsing config based on flags");
    let mut config = Config::parse(flags);
    config.original_preparation_configuration = original_preparation_configuration;
    if let Some(policy) = &mut embedded {
        policy.limit(&mut config);
        crate::engine::validate_config(&config)?;
    }

    // Trust: the compiled installation producer shares native admission and ownership.
    let wp_install =
        crate::core::build_steps::install::is_wp_installation(config.cmd.kind(), &config.paths);
    if wp_install {
        crate::core::build_steps::install::validate_wp_installation(&config).unwrap_or_else(
            |error| {
                eprintln!("native WP installation: {error}");
                crate::utils::helpers::exit_process(2);
            },
        );
    }

    // Trust: reject unsupported native modes before taking either build lock.
    if config.cmd.trust_repo_check() {
        crate::core::build_steps::repo::validate(&config).unwrap_or_else(|error| {
            eprintln!("native repository check: {error}");
            crate::utils::helpers::exit_process(2);
        });
    }

    // Trust: direct compiled bootstrap must exclude the same measurements as
    // x.py. The lease belongs to this durable writer, not a short-lived helper.
    let _repo_build_lease = if (config.cmd.trust_repo_check() || wp_install) && !config.dry_run() {
        let lease = if wp_install {
            crate::utils::trust_repo_lock::BuildLease::acquire_for_installation(&config.src)
        } else if config.cmd.trust_repo_parent_release_v1() {
            crate::utils::trust_repo_lock::BuildLease::acquire_for_parent(&config.src)
        } else {
            crate::utils::trust_repo_lock::BuildLease::acquire(&config.src)
        };
        Some(lease.unwrap_or_else(|error| {
            eprintln!("native repository check: {error}");
            crate::utils::helpers::exit_process(2);
        }))
    } else {
        None
    };

    // Ordinary direct Bootstrap and x.py's compiled child participate in the
    // same native ownership policy. A valid live ancestor can be borrowed;
    // only a newly acquired original holder owns release. Named commands and
    // current configuration decide this before the output lock or Step graph.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let command_build_lease = if _repo_build_lease.is_none()
        && !config.dry_run()
        && crate::utils::trust_repo_lock::writes_build_tree(config.cmd.kind())
    {
        Some(std::sync::Arc::new(
            crate::core::build_steps::frontend_runtime::CommandOwnership::new(
                crate::utils::trust_repo_lock::acquire_command(&config.src, config.cmd.kind())
                    .unwrap_or_else(|error| {
                        eprintln!("native bootstrap build ownership: {error}");
                        crate::utils::helpers::exit_process(2);
                    }),
            ),
        ))
    } else {
        None
    };
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let command_build_lease: Option<std::sync::Arc<()>> = None;

    // The callback must act on this invocation's already acquired original
    // command ownership. It cannot create a second holder from Plan data.
    if let Some(policy) = &mut embedded {
        let shims = policy.selected_shims()?;
        let prepared = (policy.before_steps)(crate::engine::Preparation::new(
            crate::engine::Plan::from_config(&config),
            command_build_lease.as_ref(),
        ))?;
        prepared.install(command_build_lease.as_ref())?;
        assert!(policy.scope.is_none(), "cannot replace original embedded work scope");
        policy.scope = Some(prepared);
        policy.shims = Some(shims);
    }

    // Trust: retain the checked physical output root and persistent lock inode.
    // A PID is diagnostic only; the actual OS lock excludes other producers.
    #[cfg(unix)]
    let build_lock = if config.bypass_bootstrap_lock {
        None
    } else {
        Some(std::sync::Arc::new(t!(build_helper::trust_output_lock::OutputLock::acquire(
            &config.out,
            |pid| {
                if let Some(pid) = pid {
                    println!("WARNING: build directory locked by process {pid}, waiting for lock");
                } else {
                    println!("WARNING: build directory locked, waiting for lock");
                }
            }
        ))))
    };

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let runtime_build_ownership =
        if let (Some(output), Some(command)) = (&build_lock, &command_build_lease) {
            Some(std::sync::Arc::new(t!(
                crate::core::build_steps::frontend_runtime::BuildOwnership::new(
                    std::sync::Arc::clone(output),
                    std::sync::Arc::clone(command),
                )
            )))
        } else {
            None
        };
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    if let Some(scope) = embedded.as_mut().and_then(|policy| policy.scope.as_mut()) {
        scope.retain_build_ownership(std::sync::Arc::clone(
            runtime_build_ownership
                .as_ref()
                .ok_or("protected Bootstrap requires its original output and command guards")?,
        ))?;
    }

    // Trust: this closed no-core node consumes the actual prepared scope and
    // already acquired original output/command guards. It has no C, Cargo DAG,
    // submodule, linker or full-runtime prerequisites, so do not manufacture an
    // empty Session or run those unrelated graphs to execute this native node.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if embedded.is_some()
        && crate::core::build_steps::native_object::validate_config(&config).is_ok()
    {
        let scope = embedded
            .as_mut()
            .and_then(|policy| policy.scope.take())
            .ok_or("native object requires this invocation's actual original prepared scope")?;
        crate::core::build_steps::native_object::execute_original(&config, &scope)?;
        return Ok(crate::engine::Outcome::in_scope(None, scope));
    }

    // Trust: keep existing native locking where checked Unix inode identity is
    // unavailable; do not present an unsupported guard as acquired.
    #[cfg(not(unix))]
    let mut build_lock;
    #[cfg(not(unix))]
    if !config.bypass_bootstrap_lock {
        // Display PID of process holding the lock
        // PID will be stored in a lock file
        let lock_path = config.out.join("lock");
        build_lock = t!(fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&lock_path));
        t!(build_lock.try_lock().or_else(|e| {
            if let TryLockError::Error(e) = e {
                return Err(e);
            }
            let mut pid = String::new();
            t!(build_lock.read_to_string(&mut pid));
            // #135972: We can reach this point when the lock has been taken,
            // but the locker has not yet written its PID to the file
            if !pid.is_empty() {
                println!("WARNING: build directory locked by process {pid}, waiting for lock");
            } else {
                println!("WARNING: build directory locked, waiting for lock");
            }
            build_lock.lock()
        }));
        t!(build_lock.set_len(0));
        t!(build_lock.write_all(process::id().to_string().as_bytes()));
    }

    // Trust: keep the build directory out of Time Machine (EW-18). Every run marks it, so
    // a tree made before this existed is marked by its next command. A dry run writes
    // nothing outside its own scratch directory.
    if !config.dry_run() {
        crate::utils::trust_build_tree::exclude_build_dir_from_backups(&config.out);
    }

    // check_version warnings are not printed during setup, or during CI
    let changelog_suggestion = if matches!(config.cmd, Subcommand::Setup { .. })
        || config.is_running_on_ci()
        || config.dry_run()
    {
        None
    } else {
        check_version(&config)
    };

    // NOTE: Since `./configure` generates a `bootstrap.toml`, distro maintainers will see the
    // changelog warning, not the `x.py setup` message.
    let suggest_setup = config.config.is_none() && !matches!(config.cmd, Subcommand::Setup { .. });
    if suggest_setup {
        println!("WARNING: you have not made a `bootstrap.toml`");
        println!(
            "HELP: consider running `./x.py setup` or copying `bootstrap.example.toml` by running \
            `cp bootstrap.example.toml bootstrap.toml`"
        );
    } else if let Some(suggestion) = &changelog_suggestion {
        println!("{suggestion}");
    }

    let pre_commit = config.src.join(".git").join("hooks").join("pre-commit");
    let dump_bootstrap_shims = config.dump_bootstrap_shims;
    let out_dir = config.out.clone();

    let tracing_enabled = is_tracing_enabled();

    // Prepare a directory for tracing output
    // Also store a symlink named "latest" to point to the latest tracing directory.
    let tracing_dir = out_dir.join("bootstrap-trace").join(std::process::id().to_string());
    let latest_trace_dir = tracing_dir.parent().unwrap().join("latest");
    if tracing_enabled {
        let _ = std::fs::remove_dir_all(&tracing_dir);
        std::fs::create_dir_all(&tracing_dir).unwrap();

        #[cfg(windows)]
        let _ = std::fs::remove_dir(&latest_trace_dir);
        #[cfg(not(windows))]
        let _ = std::fs::remove_file(&latest_trace_dir);

        #[cfg(not(windows))]
        fn symlink_dir_inner(original: &Path, link: &Path) -> io::Result<()> {
            use std::os::unix::fs;
            fs::symlink(original, link)
        }

        #[cfg(windows)]
        fn symlink_dir_inner(target: &Path, junction: &Path) -> io::Result<()> {
            junction::create(target, junction)
        }

        t!(symlink_dir_inner(&tracing_dir, &latest_trace_dir));
    }

    debug!("creating new session based on config");
    let mut sess =
        Session::new_with_shims(config, embedded.as_ref().and_then(|policy| policy.shims.clone()));
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        sess.runtime_build_ownership = runtime_build_ownership;
    }
    #[cfg(unix)]
    if let Some(lock) = &build_lock {
        t!(lock.check_current());
    }
    // Trust: a fresh worktree's first build seeds its stage 1 from another worktree's
    // green one when their keys match, and a green build records its own key
    // (`utils::trust_stage1_seed`, EW-9). Both hold this tree's `build/lock`.
    run_session_steps(
        &mut sess,
        StepOwners::Ordinary {
            #[cfg(unix)]
            output: build_lock.as_deref(),
            _lifetime: std::marker::PhantomData,
        },
    )?;
    // Trust: after a successful run, under `build/lock`, prune what newer variants
    // superseded in every cargo target tree of this build directory, and the loose objects
    // their rlibs hold (`utils::trust_prune`). It never changes the run's result.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        use crate::utils::trust_prune::Ownership;
        let ownership = build_lock.as_deref().and_then(|output| {
            if let Some(repository) = &_repo_build_lease {
                Some(Ownership::repository(output, repository))
            } else {
                command_build_lease.as_deref().map(|command| Ownership::command(output, command))
            }
        });
        crate::utils::trust_prune::after_success(&sess.config, ownership);
    }

    if suggest_setup {
        println!("WARNING: you have not made a `bootstrap.toml`");
        println!(
            "HELP: consider running `./x.py setup` or copying `bootstrap.example.toml` by running \
            `cp bootstrap.example.toml bootstrap.toml`"
        );
    } else if let Some(suggestion) = &changelog_suggestion {
        println!("{suggestion}");
    }

    // Give a warning if the pre-commit script is in pre-commit and not pre-push.
    // HACK: Since the commit script uses hard links, we can't actually tell if it was installed by x.py setup or not.
    // We could see if it's identical to src/etc/pre-push.sh, but pre-push may have been modified in the meantime.
    // Instead, look for this comment, which is almost certainly not in any custom hook.
    if fs::read_to_string(pre_commit).is_ok_and(|contents| {
        contents.contains("https://github.com/rust-lang/rust/issues/77620#issuecomment-705144570")
    }) {
        println!(
            "WARNING: You have the pre-push script installed to .git/hooks/pre-commit. \
                  Consider moving it to .git/hooks/pre-push instead, which runs less often."
        );
    }

    if suggest_setup || changelog_suggestion.is_some() {
        println!("NOTE: this message was printed twice to make it more likely to be seen");
    }

    if dump_bootstrap_shims {
        let dump_dir = out_dir.join("bootstrap-shims-dump");
        assert!(dump_dir.exists());

        for entry in walkdir::WalkDir::new(&dump_dir) {
            let entry = t!(entry);

            if !entry.file_type().is_file() {
                continue;
            }

            let file = t!(fs::File::open(entry.path()));

            // To ensure deterministic results we must sort the dump lines.
            // This is necessary because the order of rustc invocations different
            // almost all the time.
            let mut lines: Vec<String> = t!(BufReader::new(&file).lines().collect());
            lines.sort_by_key(|t| t.to_lowercase());
            let mut file = t!(OpenOptions::new().write(true).truncate(true).open(entry.path()));
            t!(file.write_all(lines.join("\n").as_bytes()));
        }
    }

    #[cfg(feature = "tracing")]
    {
        sess.report_summary(&tracing_dir.join("command-stats.txt"), _start_time);
        sess.report_step_graph(&tracing_dir);
        guard.copy_to_dir(&tracing_dir);
        eprintln!("Tracing/profiling output has been written to {}", latest_trace_dir.display());
    }
    let completed = sess.completed_runtime.take();
    if let Some(scope) = embedded.as_mut().and_then(|policy| policy.scope.take()) {
        Ok(crate::engine::Outcome::in_scope(completed, scope))
    } else {
        Ok(crate::engine::Outcome::completed(completed))
    }
}

// Trust: the ordinary path borrows its existing OS lock; Full borrows its
// nonconstructible original owner. Neither variant constructs another guard.
pub(crate) enum StepOwners<'a> {
    Ordinary {
        #[cfg(unix)]
        output: Option<&'a build_helper::trust_output_lock::OutputLock>,
        _lifetime: std::marker::PhantomData<&'a ()>,
    },
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    Original(&'a std::sync::Arc<crate::engine::OriginalBootstrapCompilation>),
}

// Trust: one maintained Session::build/Step graph for both actual owner paths.
pub(crate) fn run_session_steps(sess: &mut Session, owners: StepOwners<'_>) -> Result<(), String> {
    let seeding = crate::utils::trust_stage1_seed::begin(sess);
    // Trust: name this run's tab, checkout and build directory for aterm (DC-12c).
    build_start::for_run(&sess.config);
    sess.build();
    // Trust: never publish a reusable output fact after its ownership namespace
    // changed. Only whole-tree clean --all without selected crate paths may
    // intentionally unlink a non-sanctioned top-level alias. Crate cleanup can
    // assemble a compiler and publish a seed record, even with --all, so it must
    // retain the final ownership check too.
    match owners {
        StepOwners::Ordinary {
            #[cfg(unix)]
            output,
            ..
        } => {
            #[cfg(unix)]
            if !(matches!(sess.config.cmd, Subcommand::Clean { all: true, .. })
                && sess.paths.is_empty())
            {
                if let Some(lock) = output {
                    lock.check_current().map_err(|error| error.to_string())?;
                }
            }
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        StepOwners::Original(owner) => owner.check_current().map_err(|error| error.to_string())?,
    }
    seeding.finish(sess);
    Ok(())
}

fn check_version(config: &Config) -> Option<String> {
    let mut msg = String::new();

    let latest_change_id = CONFIG_CHANGE_HISTORY.last().unwrap().change_id;
    let warned_id_path = config.out.join("bootstrap").join(".last-warned-change-id");

    let mut id = match config.change_id {
        Some(ChangeId::Id(id)) if id == latest_change_id => return None,
        Some(ChangeId::Ignore) => return None,
        Some(ChangeId::Id(id)) => id,
        None => {
            msg.push_str("WARNING: The `change-id` is missing in the `bootstrap.toml`. This means that you will not be able to track the major changes made to the bootstrap configurations.\n");
            msg.push_str("NOTE: to silence this warning, ");
            msg.push_str(&format!(
                "add `change-id = {latest_change_id}` or `change-id = \"ignore\"` at the top of `bootstrap.toml`"
            ));
            return Some(msg);
        }
    };

    // Always try to use `change-id` from .last-warned-change-id first. If it doesn't exist,
    // then use the one from the bootstrap.toml. This way we never show the same warnings
    // more than once.
    if let Ok(t) = fs::read_to_string(&warned_id_path) {
        let last_warned_id = usize::from_str(&t)
            .unwrap_or_else(|_| panic!("{} is corrupted.", warned_id_path.display()));

        // We only use the last_warned_id if it exists in `CONFIG_CHANGE_HISTORY`.
        // Otherwise, we may retrieve all the changes if it's not the highest value.
        // For better understanding, refer to `change_tracker::find_recent_config_change_ids`.
        if CONFIG_CHANGE_HISTORY.iter().any(|config| config.change_id == last_warned_id) {
            id = last_warned_id;
        }
    };

    let changes = find_recent_config_change_ids(id);

    if changes.is_empty() {
        return None;
    }

    msg.push_str("There have been changes to x.py since you last updated:\n");
    msg.push_str(&human_readable_changes(changes));

    msg.push_str("NOTE: to silence this warning, ");
    msg.push_str(&format!(
        "update `bootstrap.toml` to use `change-id = {latest_change_id}` or `change-id = \"ignore\"` instead"
    ));

    if io::stdout().is_terminal() {
        t!(fs::write(warned_id_path, latest_change_id.to_string()));
    }

    Some(msg)
}

/// Trust: the line an `x.py` run started in an aterm tab leaves for aterm before its steps run
/// (DC-12c), so aterm's `sys disk` shows a Trust build directory with the tab that built it.
/// The line and its place are aterm's build-start record (aterm `crates/atpkg/src/build_start.rs`,
/// DC-01), which a tool that does not link aterm writes with one append:
///
/// * **Place.** `build-starts.log` in aterm's state folder: on macOS
///   `$HOME/Library/Application Support/aterm`, on other Unix systems `$XDG_STATE_HOME/aterm`
///   where that is an absolute path, else `$HOME/.local/state/aterm`. The folder is never made
///   (where aterm made none, no window reads a line), and one this process's effective user does
///   not own gets no line (a `sudo -E` build). Bootstrap writes nowhere else (the record's
///   lock and stage beside it, below), and on no other system.
/// * **Line.** One JSON object and a `\n`, at most [`build_start::MAX_LINE`] bytes, written by one
///   append to a file opened `O_APPEND | O_CREAT` (mode 0600), never through a link:
///   `{"v":1,"session":…,"workspace":…,"build":…,"pid":…,"at_ms":…}`. `session` is
///   `ATERM_PARENT_SESSION_ID`, the tab's own session (a tab ID, `t` and 10 Crockford base-32
///   characters, or a legacy `s-` and 20 hex digits); `ATERM_SESSION_ID` is a nested aterm's
///   and is never read. `workspace` is the checkout (`config.src`) and `build` the build
///   directory (`config.out`), each absolute with its links resolved.
/// * **Never in the run's way.** A run outside a tab, a dry run, a `clean`, `setup`, `format`
///   or `vendor` (no build output; the prune's `gate` in `utils/trust_prune.rs` skips the
///   same) and a line that cannot be written write nothing and print nothing, and the run goes
///   on as before.
/// * **Bound.** A run whose line leaves the record over [`build_start::CAP`] bytes rewrites it
///   as aterm's own writers do ([`build_start::compact`]), so the record stays bounded where no
///   aterm writer runs (aterm writes lines on macOS alone, and only for builds through its
///   front): only while it holds the lock of `build-starts.log.lock` beside it, taken without
///   waiting (the same `flock` aterm's rewrite takes, so the two never rewrite at once), it keeps
///   of the last [`build_start::READ_MAX`] bytes the newest line of each workspace and the
///   newest of each session and workspace younger than a week, sheds the second kind and then
///   the first, oldest first, to half the cap, stages them in `build-starts.log.new`, renames
///   that over the record and appends the whole lines written to the old file after its read.
pub(crate) mod build_start {
    // Off Unix no line is written, and what forms and bounds one goes unused.
    #![cfg_attr(not(unix), allow(dead_code))]

    use std::collections::BTreeMap;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};

    use crate::core::builder::Kind;
    use crate::core::config::Config;

    /// The record's file name inside aterm's state folder.
    pub(crate) const RECORD: &str = "build-starts.log";
    /// The longest line, its `\n` included.
    pub(crate) const MAX_LINE: usize = 4096;
    /// The variable that holds the tab's own session.
    pub(crate) const SESSION_ENV: &str = "ATERM_PARENT_SESSION_ID";
    /// The file beside the record whose lock a rewrite holds.
    pub(crate) const LOCK: &str = "build-starts.log.lock";
    /// The file beside the record a rewrite stages its lines in.
    pub(crate) const STAGE: &str = "build-starts.log.new";
    /// The size past which a writer rewrites the record.
    pub(crate) const CAP: u64 = 256 << 10;
    /// The most a rewrite keeps: half the cap, so rewrites are at least that much growth apart.
    pub(crate) const KEEP_MAX: u64 = CAP / 2;
    /// How much of the record's end a rewrite keeps from.
    pub(crate) const READ_MAX: u64 = 1 << 20;
    /// How long a rewrite keeps a session's newest line of a workspace a later session built in.
    pub(crate) const KEEP_PAIR_MS: u64 = 7 * 24 * 60 * 60 * 1000;
    /// A tab ID's characters after its `t`.
    const ALPHABET: &[u8] = b"0123456789abcdefghjkmnpqrstvwxyz";

    /// Whether `text` is a tab's session: `t` and 10 characters of [`ALPHABET`], or `s-` and 20
    /// lower-case hex digits.
    pub(crate) fn is_session(text: &str) -> bool {
        let b = text.as_bytes();
        let tab = b.len() == 11 && b[0] == b't' && b[1..].iter().all(|c| ALPHABET.contains(c));
        let legacy = b.len() == 22
            && b.starts_with(b"s-")
            && b[2..].iter().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(c));
        tab || legacy
    }

    /// aterm's state folder for the environment `env`, as aterm's release build resolves it on
    /// macOS (`macos`) or another Unix system. `None` without a home.
    pub(crate) fn state_dir(
        env: &dyn Fn(&str) -> Option<OsString>,
        macos: bool,
    ) -> Option<PathBuf> {
        if !macos
            && let Some(state) = env("XDG_STATE_HOME").map(PathBuf::from)
            && state.is_absolute()
        {
            return Some(state.join("aterm"));
        }
        let home = PathBuf::from(env("HOME").filter(|home| !home.is_empty())?);
        if !home.is_absolute() {
            return None;
        }
        Some(if macos {
            home.join("Library/Application Support/aterm")
        } else {
            home.join(".local/state/aterm")
        })
    }

    /// Whether a run of `kind` leaves a line: one that is no dry run and may write build output.
    pub(crate) fn wanted(dry_run: bool, kind: Kind) -> bool {
        !dry_run && !matches!(kind, Kind::Clean | Kind::Setup | Kind::Format | Kind::Vendor)
    }

    /// The line for a run of the tab `session` on `workspace` into `build`: `None` for a session
    /// that is no session, a path that is relative or not UTF-8, and a line that is too long.
    pub(crate) fn line(
        session: &str,
        workspace: &Path,
        build: &Path,
        pid: u32,
        at_ms: u64,
    ) -> Option<String> {
        let text = |path: &Path| path.to_str().filter(|_| path.is_absolute()).map(str::to_owned);
        if !is_session(session) {
            return None;
        }
        let mut line = serde_json::json!({
            "v": 1,
            "session": session,
            "workspace": text(workspace)?,
            "build": text(build)?,
            "pid": pid,
            "at_ms": at_ms,
        })
        .to_string();
        line.push('\n');
        (line.len() <= MAX_LINE).then_some(line)
    }

    /// Appends the line of a run on `workspace` into `build` to the record of the tab the
    /// environment `env` names, with one write. Whether a line was written: `false` outside a
    /// tab, without a state folder this effective user owns, for a workspace or build directory
    /// that cannot be resolved, and when the record cannot be opened or written (a link, no
    /// regular file, no room).
    #[cfg(unix)]
    pub(crate) fn append(
        env: &dyn Fn(&str) -> Option<OsString>,
        workspace: &Path,
        build: &Path,
        pid: u32,
        at_ms: u64,
    ) -> bool {
        use std::io::Write as _;
        use std::os::unix::fs::MetadataExt as _;
        let Some(session) = env(SESSION_ENV).and_then(|s| s.into_string().ok()) else {
            return false;
        };
        let Some(state) = state_dir(env, cfg!(target_os = "macos")) else { return false };
        // SAFETY: geteuid has no preconditions.
        let euid = unsafe { libc::geteuid() };
        if !std::fs::metadata(&state).is_ok_and(|meta| meta.is_dir() && meta.uid() == euid) {
            return false;
        }
        let (Ok(workspace), Ok(build)) = (workspace.canonicalize(), build.canonicalize()) else {
            return false;
        };
        let Some(line) = line(&session, &workspace, &build, pid, at_ms) else { return false };
        let record = state.join(RECORD);
        let Ok(mut file) = open_private(&record, true) else { return false };
        if file.write_all(line.as_bytes()).is_err() {
            return false;
        }
        let over = file.metadata().is_ok_and(|meta| meta.len() > CAP);
        drop(file);
        if over {
            compact(&record, at_ms);
        }
        true
    }

    /// `path` opened for writing, made private (0600) where it is new, never through a link and
    /// never waiting on a FIFO; `append` for appending, else truncated. An error for anything
    /// but a regular file.
    #[cfg(unix)]
    fn open_private(path: &Path, append: bool) -> std::io::Result<std::fs::File> {
        use std::os::unix::fs::OpenOptionsExt as _;
        let file = std::fs::OpenOptions::new()
            .write(true)
            .append(append)
            .truncate(!append)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(path)?;
        if !file.metadata()?.is_file() {
            return Err(std::io::Error::other("the build-start record is not a regular file"));
        }
        Ok(file)
    }

    /// What a line of the record says that a rewrite keeps by: its session, its workspace and
    /// its time. `None` for a line aterm's reader skips: too long, no JSON object, another
    /// version, a session that is no session, a relative workspace or build directory, or one
    /// that lacks the session, the workspace, the process id or the time.
    pub(crate) fn parse(line: &str) -> Option<(String, String, u64)> {
        if line.len() >= MAX_LINE {
            return None;
        }
        let value: serde_json::Value = serde_json::from_str(line).ok()?;
        let absolute = |text: &str| Path::new(text).is_absolute();
        if value.get("v")?.as_u64()? != 1 {
            return None;
        }
        let session = value.get("session")?.as_str().filter(|s| is_session(s))?;
        match value.get("build") {
            None | Some(serde_json::Value::Null) => {}
            Some(build) => {
                build.as_str().filter(|b| absolute(b))?;
            }
        }
        let workspace = value.get("workspace")?.as_str().filter(|w| absolute(w))?;
        u32::try_from(value.get("pid")?.as_u64()?).ok()?;
        let at_ms = value.get("at_ms")?.as_u64()?;
        Some((session.to_owned(), workspace.to_owned(), at_ms))
    }

    /// Which of `lines` (oldest first) a rewrite at `now` keeps, by what they say alone: the
    /// newest line of each workspace, and the newest of each session and workspace whose time is
    /// at or before `now` and less than [`KEEP_PAIR_MS`] before it; then, oldest first, it drops
    /// lines of the second kind only, then any, until the kept lines with their `\n`s fit in
    /// [`KEEP_MAX`] bytes. aterm's rewrite keeps the same (`kept` in aterm's
    /// `crates/atpkg/src/build_start.rs`).
    pub(crate) fn kept(lines: &[(String, (String, String, u64))], now: u64) -> Vec<bool> {
        let mut newest_of_workspace: BTreeMap<&str, usize> = BTreeMap::new();
        let mut newest_of_pair: BTreeMap<(&str, &str), usize> = BTreeMap::new();
        for (at, (_, (session, workspace, _))) in lines.iter().enumerate() {
            newest_of_workspace.insert(workspace, at);
            newest_of_pair.insert((session, workspace), at);
        }
        let last_of_workspace: Vec<bool> = lines
            .iter()
            .enumerate()
            .map(|(at, (_, (_, workspace, _)))| {
                newest_of_workspace.get(workspace.as_str()) == Some(&at)
            })
            .collect();
        let mut keep: Vec<bool> = lines
            .iter()
            .enumerate()
            .map(|(at, (_, (session, workspace, at_ms)))| {
                let young = *at_ms <= now && now - at_ms < KEEP_PAIR_MS;
                last_of_workspace[at]
                    || (young
                        && newest_of_pair.get(&(session.as_str(), workspace.as_str())) == Some(&at))
            })
            .collect();
        let size = |at: usize| lines[at].0.len() as u64 + 1;
        let mut total: u64 = (0..lines.len()).filter(|&at| keep[at]).map(size).sum();
        for workspaces_too in [false, true] {
            for at in 0..lines.len() {
                if total <= KEEP_MAX {
                    return keep;
                }
                if keep[at] && (workspaces_too || !last_of_workspace[at]) {
                    keep[at] = false;
                    total -= size(at);
                }
            }
        }
        keep
    }

    /// Rewrites `record`, past [`CAP`], to the lines a rewrite at `now` keeps ([`kept`]), in
    /// their order, while this process holds the lock of [`LOCK`] beside it, taken without
    /// waiting: a lock another holds, or a record at or under the cap once it is held (a rewrite
    /// just ran), is no rewrite. The kept lines are staged in [`STAGE`] and renamed over the
    /// record; then the whole lines written to the old file after its read, up to [`READ_MAX`]
    /// bytes of them, are appended to the new one. It reads nothing a line names, never waits,
    /// and leaves the record as it is where any step fails.
    #[cfg(unix)]
    pub(crate) fn compact(record: &Path, now: u64) {
        use std::io::{Read as _, Seek as _, SeekFrom, Write as _};
        use std::os::fd::AsRawFd as _;
        use std::os::unix::fs::OpenOptionsExt as _;
        let Some(folder) = record.parent() else { return };
        let Ok(lock) = open_private(&folder.join(LOCK), true) else { return };
        // SAFETY: `lock` is an open descriptor for the call's whole length; flock has no other
        // precondition. The lock belongs to the open description, so it goes when `lock` drops
        // unless a process another thread is starting still holds a copy; a lock held on that
        // way only makes a concurrent rewrite skip, and a later line rewrites.
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return;
        }
        let old = std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(record);
        let Ok(mut old) = old else { return };
        let Ok(meta) = old.metadata() else { return };
        let end = meta.len();
        if !meta.is_file() || end <= CAP {
            return;
        }
        let from = end.saturating_sub(READ_MAX);
        let mut bytes = Vec::new();
        if old.seek(SeekFrom::Start(from)).is_err()
            || (&mut old).take(end - from).read_to_end(&mut bytes).is_err()
        {
            return;
        }
        let mut text = bytes.as_slice();
        if from > 0 {
            let first = text.iter().position(|b| *b == b'\n').map_or(text.len(), |at| at + 1);
            text = &text[first..];
        }
        let lines: Vec<(String, (String, String, u64))> = text
            .split(|b| *b == b'\n')
            .filter_map(|line| std::str::from_utf8(line).ok())
            .filter_map(|line| parse(line).map(|said| (line.to_owned(), said)))
            .collect();
        let mut kept_text = String::new();
        for ((line, _), keep) in lines.iter().zip(kept(&lines, now)) {
            if keep {
                kept_text.push_str(line);
                kept_text.push('\n');
            }
        }
        let stage = folder.join(STAGE);
        let staged =
            open_private(&stage, false).and_then(|mut file| file.write_all(kept_text.as_bytes()));
        if staged.and_then(|()| std::fs::rename(&stage, record)).is_err() {
            let _ = std::fs::remove_file(&stage);
            return;
        }
        let mut late = Vec::new();
        if old.seek(SeekFrom::Start(end)).is_err()
            || (&mut old).take(READ_MAX).read_to_end(&mut late).is_err()
        {
            return;
        }
        let whole = late.iter().rposition(|b| *b == b'\n').map_or(0, |at| at + 1);
        if whole > 0
            && let Ok(mut new) = open_private(record, true)
        {
            let _ = new.write_all(&late[..whole]);
        }
        drop(lock);
    }

    #[cfg(not(unix))]
    pub(crate) fn append(
        _env: &dyn Fn(&str) -> Option<OsString>,
        _workspace: &Path,
        _build: &Path,
        _pid: u32,
        _at_ms: u64,
    ) -> bool {
        false
    }

    /// The line of this run, where [`wanted`] and [`append`] write one.
    pub(crate) fn for_run(config: &Config) -> bool {
        if !wanted(config.dry_run(), config.cmd.kind()) {
            return false;
        }
        let at_ms = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |since| u64::try_from(since.as_millis()).unwrap_or(u64::MAX));
        append(&|name| std::env::var_os(name), &config.src, &config.out, std::process::id(), at_ms)
    }
}

#[cfg(all(test, unix))]
mod tests;
