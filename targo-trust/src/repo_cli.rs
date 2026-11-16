//! Native repository execution through the existing compiled bootstrap graph.

use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus};
#[cfg(unix)]
use std::time::Duration;
use std::{env, fs};

#[cfg(unix)]
use crate::process_lifecycle::{self, StopCause};

#[cfg(unix)]
mod lease;

const USAGE: &str = "\
Usage: targo trust repo check-ui --test tests/ui/trust/FILE.rs [--repo-root DIR] [--config FILE] [--jobs N]

Check every compiler target and run exactly the selected Trust UI file (all its
revisions) using one local stage-1 compiler and one compiled bootstrap invocation.
Every invocation executes the compiler check and selected UI test; Cargo may reuse
unchanged compilation units. Saved facts describe completed inner bootstrap
execution, not proof evidence or the outer command's process cleanup. Prior success
never skips execution: arbitrary test/build-script reads are not a complete input closure.

Requires an existing build/bootstrap/{debug,release}/bootstrap in this checkout
and the machine's existing build-slot admission. The native mode takes the same
build/measurement lock as x.py; it refuses an existing holder instead of breaking it.
";

#[derive(Debug, PartialEq, Eq)]
struct Args {
    root: Option<PathBuf>,
    test: PathBuf,
    config: Option<PathBuf>,
    jobs: Option<u32>,
}

fn parse(args: &[String]) -> Result<Args, String> {
    let mut root = None;
    let mut test = None;
    let mut config = None;
    let mut jobs = None;
    let mut arguments = args.iter();
    while let Some(argument) = arguments.next() {
        let value = arguments.next().ok_or_else(|| format!("{argument} requires a value"))?;
        match argument.as_str() {
            "--repo-root" if root.is_none() => root = Some(PathBuf::from(value)),
            "--test" if test.is_none() => test = Some(PathBuf::from(value)),
            "--config" if config.is_none() => config = Some(PathBuf::from(value)),
            "--jobs" if jobs.is_none() => {
                jobs = Some(
                    value
                        .parse::<u32>()
                        .ok()
                        .filter(|jobs| *jobs > 0)
                        .ok_or("--jobs requires a positive integer")?,
                );
            }
            _ => return Err(format!("unknown or repeated option {argument}")),
        }
    }
    let test = test.ok_or("--test must select one existing tests/ui/trust/*.rs file")?;
    if test.is_absolute()
        || test.components().any(|component| !matches!(component, Component::Normal(_)))
        || !test.starts_with("tests/ui/trust")
        || test.extension().is_none_or(|extension| extension != "rs")
    {
        return Err("--test requires a relative tests/ui/trust/*.rs file".into());
    }
    Ok(Args { root, test, config, jobs })
}

pub(crate) fn run(args: &[String]) -> ExitCode {
    if args.iter().any(|argument| matches!(argument.as_str(), "--help" | "-h")) {
        print!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    match run_checked(args) {
        Ok(status) => status
            .code()
            .and_then(|code| u8::try_from(code).ok())
            .map_or(ExitCode::FAILURE, ExitCode::from),
        Err(error) => {
            eprintln!("targo trust repo check-ui: {error}");
            ExitCode::from(2)
        }
    }
}

fn run_checked(args: &[String]) -> Result<ExitStatus, String> {
    if !cfg!(unix) {
        return Err(
            "this first native repository slice requires Unix process-tree ownership".into()
        );
    }
    let args = parse(args)?;
    let root = match args.root {
        Some(root) => root,
        None => env::current_dir()
            .map_err(|e| e.to_string())?
            .ancestors()
            .find(|root| {
                root.join("src/bootstrap/Cargo.toml").is_file()
                    && root.join("targo-trust/Cargo.toml").is_file()
            })
            .ok_or("run from a Trust checkout or select --repo-root")?
            .to_owned(),
    };
    let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
    let selected = fs::canonicalize(root.join(&args.test)).map_err(|e| e.to_string())?;
    if !selected.is_file() || !selected.starts_with(root.join("tests/ui/trust")) {
        return Err("the selected UI file resolves outside this checkout's Trust suite".into());
    }
    if env::var_os("BUILD_SLOT_HELD").as_deref() != Some(std::ffi::OsStr::new("1")) {
        return Err(
            "run this heavy workflow through the existing machine-wide build-slot admission".into(),
        );
    }
    let share = env::var("CARGO_BUILD_JOBS")
        .ok()
        .and_then(|value| value.parse::<u32>().ok())
        .filter(|share| *share > 0)
        .ok_or("build-slot must supply a positive CARGO_BUILD_JOBS share")?;
    let jobs = args.jobs.unwrap_or(share);
    if jobs > share {
        return Err("--jobs exceeds the admitted CARGO_BUILD_JOBS share".into());
    }
    // Select the checkout's existing native bootstrap, never an arbitrary runner.
    // A stale bootstrap rejects the new flag instead of silently running a legacy gate.
    let bootstrap = ["debug", "release"].into_iter()
        .map(|profile| root.join("build/bootstrap").join(profile).join("bootstrap"))
        .find(|path| fs::symlink_metadata(path).is_ok_and(|metadata| metadata.is_file()))
        .ok_or("this checkout has no compiled bootstrap; initialize its existing bootstrap build first")?;
    #[cfg(unix)]
    {
        let mut command =
            bootstrap_command(&bootstrap, &root, &args.test, args.config.as_deref(), jobs);
        let handoff = lease::ParentHandoff::new()?;
        handoff.configure(&mut command);
        wait_owned(&mut command, Some((&root, &handoff)))
    }
    #[cfg(not(unix))]
    Err("native repository execution requires Unix process ownership".into())
}

fn bootstrap_command(
    bootstrap: &Path,
    root: &Path,
    test: &Path,
    config: Option<&Path>,
    jobs: u32,
) -> Command {
    let mut command = Command::new(bootstrap);
    command
        .current_dir(root)
        .args([
            "test",
            "--stage",
            "1",
            "--trust-repo-check",
            "--trust-repo-parent-release-v1",
            "--jobs",
        ])
        .arg(jobs.to_string())
        .arg(test)
        .env("CARGO_NET_OFFLINE", "true");
    if let Some(config) = config {
        command.arg("--config").arg(config);
    }
    command
}

#[cfg(unix)]
fn wait_owned(
    command: &mut Command,
    handoff: Option<(&Path, &lease::ParentHandoff)>,
) -> Result<ExitStatus, String> {
    let (mut child, ownership) =
        process_lifecycle::spawn_owned(command).map_err(|e| e.to_string())?;
    loop {
        match crate::bounded_process::exited_without_reaping(&mut child) {
            Ok(true) => break,
            Ok(false) => {}
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => {
                let _ = process_lifecycle::stop_child(&mut child, StopCause::Released);
                let _ = child.wait();
                drop(ownership);
                return Err(error.to_string());
            }
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    // A production bootstrap failure can use process::exit, which skips its
    // BuildLease destructor. Capture only this still-unreaped child's holder.
    let held = handoff
        .map(|(root, parent)| {
            lease::HeldBuildLease::capture(root, child.id(), parent)?.ok_or_else(|| {
                "native bootstrap did not retain this invocation's acknowledged build holder"
                    .to_owned()
            })
        })
        .transpose();
    // Keep the unreaped leader's PID/PGID reservation while stopping descendants.
    let stopped = process_lifecycle::stop_tree(child.id(), StopCause::LeaderExited);
    // Never unlock while a descendant may still write. Even a failed invocation
    // must finish its tree shutdown before releasing its exact captured holder.
    let cleanup = match (&stopped, held) {
        (Ok(stopped), Ok(held)) if observed_quiet_complete(stopped) => {
            held.map_or(Ok(()), lease::HeldBuildLease::release)
        }
        (_, Err(error)) => Err(error),
        _ => Ok(()),
    };
    let status = child.wait();
    drop(ownership);
    let stopped = stopped.map_err(|e| e.to_string())?;
    let status = status.map_err(|e| e.to_string())?;
    cleanup?;
    require_clean_stop(stopped)?;
    Ok(status)
}

// A completed stop can have killed leaked writers. Release their exact fence
// after final observed quietness, then reject workflow success separately.
#[cfg(unix)]
fn observed_quiet_complete(stopped: &process_lifecycle::StopOutcome) -> bool {
    stopped.observation == process_lifecycle::tree::Observation::Complete && stopped.left == 0
}

#[cfg(unix)]
fn require_clean_stop(stopped: process_lifecycle::StopOutcome) -> Result<(), String> {
    if !observed_quiet_complete(&stopped) {
        return Err(format!(
            "bootstrap process-tree quietness was not completely observed: {:?}",
            stopped.observation
        ));
    }
    if stopped.observed_running || stopped.terminated != 0 || stopped.killed != 0 {
        return Err(
            "bootstrap left running descendants; the native workflow could not complete cleanly"
                .into(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{bootstrap_command, parse};

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_owned()).collect()
    }

    #[test]
    fn requires_one_confined_file_and_closed_options() {
        assert!(parse(&strings(&["--test", "tests/ui/trust/one.rs"])).is_ok());
        for args in [
            vec![],
            vec!["--test", "tests/ui/trust"],
            vec!["--test", "/tmp/test.rs"],
            vec!["--test", "tests/ui/trust/../outside.rs"],
            vec!["--test", "tests/ui/trust/one.rs", "--test", "tests/ui/trust/two.rs"],
            vec!["--test", "tests/ui/trust/one.rs", "--bootstrap", "/bin/true"],
        ] {
            assert!(parse(&strings(&args)).is_err(), "{args:?}");
        }
    }

    #[test]
    fn dispatches_one_native_graph_without_a_shell_or_generated_runner() {
        let command = bootstrap_command(
            Path::new("/repo/build/bootstrap/debug/bootstrap"),
            Path::new("/repo"),
            Path::new("tests/ui/trust/one.rs"),
            None,
            2,
        );
        assert_eq!(command.get_program(), "/repo/build/bootstrap/debug/bootstrap");
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            [
                "test",
                "--stage",
                "1",
                "--trust-repo-check",
                "--trust-repo-parent-release-v1",
                "--jobs",
                "2",
                "tests/ui/trust/one.rs"
            ]
        );
        assert_eq!(command.get_current_dir(), Some(Path::new("/repo")));
    }

    #[cfg(unix)]
    #[test]
    fn zero_counters_require_complete_quiet_and_no_late_live_evidence() {
        use crate::process_lifecycle::StopOutcome;
        use crate::process_lifecycle::tree::Observation;
        assert!(super::require_clean_stop(StopOutcome::default()).is_err());
        let quiet = StopOutcome { observation: Observation::Complete, ..StopOutcome::default() };
        assert!(super::require_clean_stop(quiet).is_ok());
        assert!(super::observed_quiet_complete(&quiet));
        assert!(!super::observed_quiet_complete(&StopOutcome::default()));
        for observation in [Observation::Unknown, Observation::Exhausted] {
            assert!(!super::observed_quiet_complete(&StopOutcome { observation, ..quiet }));
            assert!(super::require_clean_stop(StopOutcome { observation, ..quiet }).is_err());
        }
        assert!(
            super::require_clean_stop(StopOutcome { observed_running: true, ..quiet }).is_err()
        );
        assert!(super::require_clean_stop(StopOutcome { killed: 1, ..quiet }).is_err());
        assert!(!super::observed_quiet_complete(&StopOutcome { left: 1, ..quiet }));
        // A completed stop releases its exact fence even if it stopped leaked
        // writers, while the invocation still reports failure.
        assert!(super::observed_quiet_complete(&StopOutcome {
            observed_running: true,
            killed: 1,
            ..quiet
        }));
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn an_owned_normal_exit_needs_a_complete_quiet_observation() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "exit 0"]);
        assert!(super::wait_owned(&mut command, None).unwrap().success());
        use crate::process_lifecycle::tree::{Observation, ReadKind, with_read_fault};
        for (kind, fault) in [
            (ReadKind::Identity, Observation::Unknown),
            (ReadKind::Group, Observation::Unknown),
            (ReadKind::Group, Observation::Exhausted),
        ] {
            let result = with_read_fault(kind, fault, || {
                let mut command = std::process::Command::new("/bin/sh");
                command.args(["-c", "exit 0"]);
                super::wait_owned(&mut command, None)
            });
            assert!(result.is_err(), "{kind:?}/{fault:?} must not accept zero counts");
        }
    }

    #[cfg(unix)]
    #[test]
    fn normal_leader_exit_does_not_release_running_descendants() {
        let root = tempfile::tempdir().unwrap();
        let pid_file = root.path().join("child-pid");
        let mut command = std::process::Command::new("/bin/sh");
        command
            .args(["-c", "sleep 60 & printf '%s' \"$!\" > \"$1\"", "native-repo-test"])
            .arg(&pid_file);
        let result = super::wait_owned(&mut command, None);
        assert!(result.unwrap_err().contains("left running descendants"));
        let pid: u32 = std::fs::read_to_string(pid_file).unwrap().parse().unwrap();
        assert!(!crate::process_lifecycle::tree::still_running(pid, None));
    }

    #[cfg(unix)]
    #[test]
    fn real_failed_exit_releases_its_holder_after_descendant_shutdown() {
        const MODE: &str = "TRUST_NATIVE_REPO_EXIT_CONTROL_MODE";
        const ROOT: &str = "TRUST_NATIVE_REPO_EXIT_CONTROL_ROOT";
        const NAME: &str =
            "repo_cli::tests::real_failed_exit_releases_its_holder_after_descendant_shutdown";
        let mode = std::env::var(MODE).ok();
        if mode.as_deref() == Some("unacknowledged") {
            let root = std::path::PathBuf::from(std::env::var_os(ROOT).unwrap());
            std::fs::write(root.join("executed-writer"), b"executed").unwrap();
            return;
        }
        if matches!(
            mode.as_deref(),
            Some("writer" | "leaking-writer" | "returning-writer" | "leaking-returning-writer")
        ) {
            let root = std::path::PathBuf::from(std::env::var_os(ROOT).unwrap());
            let namespace = build_helper::trust_build_lock::NamespaceGuard::acquire(&root).unwrap();
            let directory = root.join(".trust-build-lock");
            std::fs::create_dir(&directory).unwrap();
            let pid = std::process::id();
            let start = super::lease::process_start(pid).unwrap();
            // EW18-LOCKUTC-1: the zone-free start a current bootstrap records
            // beside the zoned one. This writer runs in another time zone than
            // its controller (below), so only this field identifies it there.
            let start_utc = super::lease::process_start_utc(pid).unwrap();
            let parent = std::env::var("TRUST_NATIVE_REPO_PARENT_PID").unwrap();
            let parent_start = std::env::var("TRUST_NATIVE_REPO_PARENT_START").unwrap();
            let token = std::env::var("TRUST_NATIVE_REPO_PARENT_TOKEN").unwrap();
            // A current bootstrap identifies its parent before it writes
            // (`parent_handoff` in src/bootstrap/src/utils/trust_repo_lock.rs): by
            // `..._START_UTC` alone when the parent sends it, else by the zoned
            // `..._START`, which cannot match here, since the parent read its own
            // start in Los Angeles and this child reads it in Tokyo. The stand-in
            // makes the same start check, so a handoff that stopped sending the
            // zone-free start fails here as it would against the real bootstrap.
            let parent_pid = parent.parse::<u32>().unwrap();
            assert_ne!(parent_start, super::lease::process_start(parent_pid).unwrap());
            let parent_start_utc = std::env::var("TRUST_NATIVE_REPO_PARENT_START_UTC")
                .expect("the parent sends its zone-free start");
            assert_eq!(parent_start_utc, super::lease::process_start_utc(parent_pid).unwrap());
            std::fs::write(
                directory.join("info"),
                format!(
                    "token=.trust-build-lock.tmp.real-exit\nkind=build\npid={pid}\npstart={start}\npstart_utc={start_utc}\npgid={pid}\nrelease_parent_pid={parent}\nrelease_parent_start={parent_start}\nrelease_token={token}\n"
                ),
            )
            .unwrap();
            drop(namespace);
            std::fs::write(root.join("executed-writer"), b"executed").unwrap();
            if mode.as_deref().unwrap().starts_with("leaking-") {
                let child = std::process::Command::new("/bin/sleep").arg("60").spawn().unwrap();
                std::fs::write(root.join("descendant-pid"), child.id().to_string()).unwrap();
                // Deliberately leave this own child for the outer ownership test.
            }
            if mode.as_deref().unwrap().contains("returning") {
                return;
            }
            // Exercise real process exit; a test-build bootstrap panic would
            // unwind its RAII lease and conceal the production failure.
            std::process::exit(7);
        }
        if mode.as_deref() == Some("controller") {
            let root = std::path::PathBuf::from(std::env::var_os(ROOT).unwrap());
            for writer in [
                "returning-writer",
                "writer",
                "leaking-writer",
                "leaking-returning-writer",
                "unacknowledged",
            ] {
                let handoff = super::lease::ParentHandoff::new().unwrap();
                let mut command = std::process::Command::new(std::env::current_exe().unwrap());
                command
                    .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
                    .env(MODE, writer)
                    .env(ROOT, &root)
                    // The controller runs in Los Angeles (below): the writer's zoned
                    // `pstart` cannot match what the controller's `ps` prints.
                    .env("TZ", "Asia/Tokyo");
                handoff.configure(&mut command);
                let result = super::wait_owned(&mut command, Some((&root, &handoff)));
                assert_eq!(std::fs::read(root.join("executed-writer")).unwrap(), b"executed");
                if writer == "unacknowledged" {
                    assert!(result.unwrap_err().contains("acknowledged build holder"));
                } else if !writer.starts_with("leaking-") {
                    assert_eq!(
                        result.unwrap().code(),
                        Some(if writer == "writer" { 7 } else { 0 })
                    );
                } else {
                    assert!(result.unwrap_err().contains("left running descendants"));
                    let pid = std::fs::read_to_string(root.join("descendant-pid"))
                        .unwrap()
                        .parse()
                        .unwrap();
                    assert!(!crate::process_lifecycle::tree::still_running(pid, None));
                }
                assert!(!root.join(".trust-build-lock").exists());
                std::fs::remove_file(root.join("executed-writer")).unwrap();
            }
            println!("failed-exit and descendant cleanup controls executed");
            return;
        }

        // Re-execute only this test beneath the existing bounded owned-process
        // helper. A broken waiter is killed and reaped with its own descendants.
        let root = tempfile::tempdir().unwrap();
        let mut command = std::process::Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
            .env(MODE, "controller")
            .env(ROOT, root.path())
            .env("TZ", "America/Los_Angeles");
        let output = crate::bounded_process::output(
            &mut command,
            "native repository real exit controls",
            64 * 1024,
            std::time::Duration::from_secs(10),
        )
        .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout)
                .contains("failed-exit and descendant cleanup controls executed"),
            "zero executed controls cannot pass: {output:?}"
        );
    }
}
