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
