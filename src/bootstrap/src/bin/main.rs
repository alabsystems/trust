//! bootstrap, the Rust build system
//!
//! This is the entry point for the build system used to compile the `rustc`
//! compiler. Lots of documentation can be found in the `README.md` file in the
//! parent directory, and otherwise documentation can be found throughout the `build`
//! directory in each respective module.

use std::fs::{self, OpenOptions, TryLockError};
use std::io::{self, BufRead, BufReader, IsTerminal, Read, Write};
use std::path::Path;
use std::str::FromStr;
use std::time::Instant;
use std::{env, process};

use bootstrap::{
    Build, CONFIG_CHANGE_HISTORY, ChangeId, Config, Flags, Subcommand, debug,
    find_recent_config_change_ids, human_readable_changes, t,
};

fn is_tracing_enabled() -> bool {
    cfg!(feature = "tracing")
}

fn main() {
    clamp_umask_for_sysroot_authenticity();

    #[cfg(feature = "tracing")]
    let guard = bootstrap::setup_tracing("BOOTSTRAP_TRACING");

    let _start_time = Instant::now();

    let args = env::args().skip(1).collect::<Vec<_>>();

    if Flags::try_parse_verbose_help(&args) {
        return;
    }

    debug!("parsing flags");
    let flags = Flags::parse(&args);
    debug!("parsing config based on flags");
    let config = Config::parse(flags);

    let mut build_lock;

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

    debug!("creating new build based on config");
    let mut build = Build::new(config);
    build.build();

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
        build.report_summary(&tracing_dir.join("command-stats.txt"), _start_time);
        build.report_step_graph(&tracing_dir);
        guard.copy_to_dir(&tracing_dir);
        eprintln!("Tracing/profiling output has been written to {}", latest_trace_dir.display());
    }
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

// Trust: the sysroot we assemble must satisfy the toolchain's OWN
// authenticity checks, and a group-writable one does not.
//
// `trust_router::coordinator::validate_authorized_directory_chain` refuses
// any ancestor of `trustd` with `mode & 0o022 != 0`, because a group- or
// world-writable directory lets another user swap the daemon binary between
// the moment its bytes are hashed and the moment it is exec'd. That refusal
// is correct and must not be relaxed.
//
// But under the common `umask 0002` (default on Debian/Ubuntu-family
// systems with per-user groups) bootstrap creates `build/<triple>/stageN`
// and its `bin/` as 0775, so the compiler we just built rejects its own
// daemon and `targo trust check` cannot run at all. Measured on
// aarch64-unknown-linux-gnu 2026-08-31: chmod'ing the chain by hand fixed
// it, and the very next `x.py build` recreated `stage1` and `bin` as
// `drwxrwxr-x` and broke it again — so a one-off chmod is not a fix.
//
// Clamp OUR file-creation mask instead. This only ever removes bits the
// caller's umask would have granted; it cannot widen anything, it does not
// touch files bootstrap did not create, and it leaves owner permissions
// alone. `0o022` is what a toolchain build should have used regardless.
#[cfg(unix)]
fn clamp_umask_for_sysroot_authenticity() {
    // SAFETY: `umask` is a process-global getter/setter taking a scalar, with
    // no failure mode and no pointer arguments. This runs before bootstrap
    // spawns a thread or creates a file, so nothing can observe a half-applied
    // mask.
    unsafe {
        let previous = libc::umask(0o022);
        // Preserve whatever the caller was ALREADY excluding: the contract is
        // "at least as strict as 022", never "exactly 022".
        libc::umask(previous | 0o022);
    }
}

#[cfg(not(unix))]
fn clamp_umask_for_sysroot_authenticity() {}
