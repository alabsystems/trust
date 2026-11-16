//! The legs of `targo trust stability`: their checkouts, the load generator,
//! the `check` process each one is, and the records it leaves.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use super::closure::{ClosurePackage, PathClosure};
use super::judge::{Side, UnitFacts};
use super::{Checkout, Leg, LegRun, Plan};
use crate::process_lifecycle::{self, Ownership, StopCause};

/// How one leg's process ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LegExit {
    Exited(i32),
    /// Ended by a signal (no exit status).
    Signalled,
    /// Could not be started, or waited for.
    Failed(String),
}

/// One leg's `targo trust check`, as the verb hands it to a [`LegRunner`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LegSpec {
    pub(crate) leg: Leg,
    /// The directory the check runs in.
    pub(crate) cwd: PathBuf,
    /// The leg's own target directory (`CARGO_TARGET_DIR`).
    pub(crate) target_dir: PathBuf,
    /// The check's arguments (after `check`).
    pub(crate) args: Vec<String>,
    /// Environment to set (`Some`) or remove (`None`) on top of the verb's own.
    pub(crate) env: Vec<(String, Option<String>)>,
    /// Where the check's stdout and stderr go.
    pub(crate) stdout: PathBuf,
    pub(crate) stderr: PathBuf,
}

/// What runs a leg's check. The verb's is [`CheckProcess`]; the verb's tests
/// stand in a runner that writes records (`stability/tests.rs`).
pub(crate) trait LegRunner {
    fn run(&mut self, spec: &LegSpec) -> LegExit;
}

/// Each leg is this executable's own `check`, a fresh process: it finds the
/// toolchain beside itself exactly as the caller's `targo trust check` does,
/// and inherits the verb's environment but for what the leg sets. It is an
/// owned child (`process_lifecycle`): a signal to the verb stops it, and when
/// its leader exits, whatever is left of its process group is stopped before
/// the leader is reaped ([`wait_then_sweep`]).
pub(crate) struct CheckProcess {
    pub(crate) exe: PathBuf,
}

impl LegRunner for CheckProcess {
    fn run(&mut self, spec: &LegSpec) -> LegExit {
        let open = |path: &Path| {
            File::create(path)
                .map_err(|error| format!("cannot create `{}`: {error}", path.display()))
        };
        let (stdout, stderr) = match (open(&spec.stdout), open(&spec.stderr)) {
            (Ok(stdout), Ok(stderr)) => (stdout, stderr),
            (Err(error), _) | (_, Err(error)) => return LegExit::Failed(error),
        };
        let mut command = Command::new(&self.exe);
        command
            .arg("check")
            .args(&spec.args)
            .current_dir(&spec.cwd)
            .env("CARGO_TARGET_DIR", &spec.target_dir)
            .stdin(Stdio::null())
            .stdout(stdout)
            .stderr(stderr);
        for (key, value) in &spec.env {
            match value {
                Some(value) => command.env(key, value),
                None => command.env_remove(key),
            };
        }
        let (mut child, ownership) = match process_lifecycle::spawn_owned(&mut command) {
            Ok(owned) => owned,
            Err(error) => return LegExit::Failed(format!("cannot start the check: {error}")),
        };
        let status = wait_then_sweep(&mut child);
        drop(ownership);
        match status {
            Ok(status) => status.code().map_or(LegExit::Signalled, LegExit::Exited),
            Err(error) => LegExit::Failed(format!("cannot wait for the check: {error}")),
        }
    }
}

/// Wait for a leg's process-group leader WITHOUT reaping it, then stop what is
/// left of its group (a build-script helper that stayed in the leader's group
/// would otherwise outlive the leg) while the unreaped leader still reserves
/// the group's id, and only then reap it: T5a's pattern
/// (`bounded_process::output_with_exact_deadline`,
/// `pipeline::run::wait_for_compiler_process`). A `trustd` is never a member
/// of a stop (`process_lifecycle::tree::is_trust_memory_daemon`), so the
/// sweep cannot reach the per-user daemon a leg started.
fn wait_then_sweep(child: &mut Child) -> io::Result<ExitStatus> {
    const POLL: Duration = Duration::from_millis(50);
    loop {
        match crate::bounded_process::exited_without_reaping(child) {
            Ok(true) => break,
            Ok(false) => std::thread::sleep(POLL),
            Err(error) => {
                let _ = process_lifecycle::stop_child(child, StopCause::Error);
                let _ = child.wait();
                return Err(error);
            }
        }
    }
    // A signal that stopped the verb may be why the leg exited: its records
    // are no reading, and the stop owns the exit.
    process_lifecycle::signals::hold_if_interrupted();
    #[cfg(unix)]
    let _ = process_lifecycle::stop_tree(child.id(), StopCause::LeaderExited);
    child.wait()
}

/// The load generator's size: two busy loops per logical CPU, at most 256
/// (the stop path enumerates at most 512 members of one tree).
pub(crate) fn load_generator_loops() -> usize {
    let cores = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    cores.saturating_mul(2).min(256)
}

/// How long the generator may take to have every busy loop running: a hang
/// detector, not a budget.
const LOAD_READY_WITHIN: Duration = Duration::from_secs(60);

/// `loops` busy loops in one process group, a child the verb owns from its
/// spawn until [`LoadGenerator::stop`] (or its drop) stops it through the one
/// stop path (`process_lifecycle::stop_tree`, cause `released`) and reaps it.
/// A signal to the verb, or the verb's death, stops it like any owned child.
pub(crate) struct LoadGenerator {
    child: Child,
    pid: u32,
    loops: usize,
    stopped: bool,
    _ownership: Ownership,
}

/// One shell that starts `$1` busy subshells and waits; SIGTERM ends each.
#[cfg(unix)]
const LOAD_SCRIPT: &str =
    "i=0; while [ \"$i\" -lt \"$1\" ]; do (while :; do :; done) & i=$((i+1)); done; wait";

impl LoadGenerator {
    /// Start `loops` busy loops.
    #[cfg(unix)]
    pub(crate) fn start(loops: usize) -> io::Result<Self> {
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", LOAD_SCRIPT, "trust-stability-load", &loops.to_string()])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let (child, ownership) = process_lifecycle::spawn_owned(&mut command)?;
        let pid = child.id();
        Ok(Self { child, pid, loops, stopped: false, _ownership: ownership })
    }

    #[cfg(not(unix))]
    pub(crate) fn start(_loops: usize) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "the load generator needs process groups (Unix)",
        ))
    }

    /// The generator's own pid (the leader of its process group).
    #[cfg(test)]
    pub(crate) fn pid_for_test(&self) -> u32 {
        self.pid
    }

    /// The busy loops asked for.
    pub(crate) fn loops(&self) -> usize {
        self.loops
    }

    /// The busy loops running now: the other running members of the
    /// generator's process group.
    pub(crate) fn running(&self) -> usize {
        let mut members = Vec::new();
        if !process_lifecycle::tree::collect_process_group(self.pid, &mut members) {
            return 0;
        }
        members
            .into_iter()
            .filter(|&pid| pid != self.pid && process_lifecycle::tree::still_running(pid, None))
            .count()
    }

    /// Wait until every busy loop runs; `false` when they do not within
    /// [`LOAD_READY_WITHIN`].
    pub(crate) fn await_ready(&self) -> bool {
        let deadline = Instant::now() + LOAD_READY_WITHIN;
        loop {
            if self.running() >= self.loops {
                return true;
            }
            if Instant::now() >= deadline {
                return false;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    /// Stop the generator through the one stop path and reap it.
    pub(crate) fn stop(mut self) -> io::Result<()> {
        self.stop_and_reap()
    }

    fn stop_and_reap(&mut self) -> io::Result<()> {
        if self.stopped {
            return Ok(());
        }
        self.stopped = true;
        let stopped = process_lifecycle::stop_child(&mut self.child, StopCause::Released);
        self.child.wait()?;
        stopped
    }
}

impl Drop for LoadGenerator {
    fn drop(&mut self) {
        // The busy loops run until they are stopped: a generator whose owner
        // lets go of it (an early return, a panic) is stopped and reaped here.
        let _ = self.stop_and_reap();
    }
}

/// Run one leg: prepare its checkout, start the load generator if it is a
/// loaded leg, run its check, stop the generator, read its records, and (unless
/// `keep`) remove its target directory. `recorded` matters to the `bumped` leg
/// alone: the packages the `moved` leg recorded, whose versions it bumps.
pub(crate) fn run_leg(
    leg: Leg,
    plan: &Plan,
    keep: bool,
    checkouts: &mut BTreeMap<Checkout, Result<PathBuf, String>>,
    runner: &mut dyn LegRunner,
    recorded: &BTreeSet<String>,
) -> LegRun {
    let started = Instant::now();
    let leg_dir = plan.scratch.join("legs").join(leg.label());
    let mut run = LegRun {
        leg,
        cwd: PathBuf::new(),
        exit: None,
        side: Side {
            label: leg.label().to_string(),
            failure: None,
            units: BTreeMap::new(),
            cargo_configs: None,
        },
        load: None,
        stderr_tail: None,
        seconds: 0.0,
    };
    let finish = |mut run: LegRun, failure: Option<String>| {
        if failure.is_some() {
            run.side.failure = failure;
        }
        run.seconds = started.elapsed().as_secs_f64();
        run
    };
    let checkout = match prepare_checkout(leg, plan, checkouts, recorded) {
        Ok(checkout) => checkout,
        Err(error) => return finish(run, Some(error)),
    };
    // The configuration above the copy's root is the leg's to compare; what
    // is below it, on the way to the workspace, the copy carries.
    run.side.cargo_configs = Some(ancestor_cargo_configs(&checkout));
    run.cwd = [&plan.closure.workspace, &plan.relative_cwd]
        .into_iter()
        .filter(|part| !part.as_os_str().is_empty())
        .fold(checkout, |dir, part| dir.join(part));
    if let Err(error) = std::fs::create_dir_all(&leg_dir) {
        return finish(run, Some(format!("cannot create `{}`: {error}", leg_dir.display())));
    }
    let spec = leg_spec(leg, run.cwd.clone(), &leg_dir, &plan.check_args);
    let generator = if leg.loaded() {
        match LoadGenerator::start(plan.load_loops) {
            Ok(generator) if generator.await_ready() => Some(generator),
            Ok(generator) => {
                let (running, loops) = (generator.running(), generator.loops());
                drop(generator);
                return finish(
                    run,
                    Some(format!(
                        "the load generator had {running} of {loops} busy loops running after \
                         {}s",
                        LOAD_READY_WITHIN.as_secs()
                    )),
                );
            }
            Err(error) => {
                return finish(run, Some(format!("cannot start the load generator: {error}")));
            }
        }
    } else {
        None
    };
    let exit = runner.run(&spec);
    let mut failure = None;
    if let Some(generator) = generator {
        let (loops, held) = (generator.loops(), generator.running());
        run.load = Some((loops, held));
        if let Err(error) = generator.stop() {
            failure = Some(format!("the load generator could not be stopped cleanly: {error}"));
        }
        if held < loops {
            failure = Some(format!(
                "only {held} of the load generator's {loops} busy loops ran through the leg"
            ));
        }
    }
    match exit {
        LegExit::Exited(code) => {
            run.exit = Some(code);
            if code == i32::from(super::EXIT_USAGE) {
                failure.get_or_insert_with(|| "the check exited 2 (usage or setup)".to_string());
            }
        }
        LegExit::Signalled => {
            failure.get_or_insert_with(|| "the check was ended by a signal".to_string());
        }
        LegExit::Failed(error) => {
            failure.get_or_insert(error);
        }
    }
    if failure.is_none() {
        match read_records(&spec.target_dir) {
            Ok(units) => run.side.units = units,
            Err(error) => failure = Some(error),
        }
    }
    if failure.is_some() || run.side.units.is_empty() {
        run.stderr_tail = stderr_tail(&spec.stderr);
    }
    if !keep {
        let _ = std::fs::remove_dir_all(&spec.target_dir);
    }
    finish(run, failure)
}

/// The check one leg runs: the caller's check options, with the serial leg's
/// worker-thread cap before any `--`, the leg's target directory, and the job
/// count the leg runs at.
pub(crate) fn leg_spec(leg: Leg, cwd: PathBuf, leg_dir: &Path, check_args: &[String]) -> LegSpec {
    let mut args = check_args.to_vec();
    let mut env = Vec::new();
    if leg.serial() {
        let separator = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
        args.splice(separator..separator, ["--worker-threads".to_string(), "1".to_string()]);
        env.push(("CARGO_BUILD_JOBS".to_string(), Some("1".to_string())));
    } else {
        // "The defaults": the job count Cargo's configuration gives the
        // checkout (a `[build] jobs` in a `.cargo/config.toml` the checkout
        // reads, else the host's), not one the caller's environment happened
        // to carry.
        env.push(("CARGO_BUILD_JOBS".to_string(), None));
    }
    LegSpec {
        leg,
        cwd,
        target_dir: leg_dir.join("target"),
        args,
        env,
        stdout: leg_dir.join("stdout.log"),
        stderr: leg_dir.join("stderr.log"),
    }
}

/// The last lines of a leg's stderr, escaped for the terminal.
fn stderr_tail(path: &Path) -> Option<String> {
    const LINES: usize = 20;
    let text = crate::input_limits::read_bounded_utf8_file(path, 64 * 1024 * 1024).ok()?;
    let lines: Vec<&str> = text.lines().collect();
    let tail = &lines[lines.len().saturating_sub(LINES)..];
    (!tail.is_empty()).then(|| {
        tail.iter().map(|line| crate::escape_terminal_controls(line)).collect::<Vec<_>>().join("\n")
    })
}

/// The checkout `leg` runs in, made the first time a leg needs it: the root of
/// the workspace's path closure (`closure::PathClosure`) in the caller's own
/// tree, or a copy of that closure under the scratch directory. The `bumped`
/// leg's is the `moved` copy with the version of every package the `moved`
/// leg `recorded` bumped, done once, after the `moved` leg (legs run in
/// [`Leg`] order).
fn prepare_checkout(
    leg: Leg,
    plan: &Plan,
    checkouts: &mut BTreeMap<Checkout, Result<PathBuf, String>>,
    recorded: &BTreeSet<String>,
) -> Result<PathBuf, String> {
    let kind = leg.checkout();
    let path = checkouts.entry(kind).or_insert_with(|| make_checkout(kind, plan)).clone()?;
    if leg == Leg::Bumped {
        let bumped = plan.scratch.join("checkouts").join(".bumped");
        if !bumped.exists() {
            let changed = bump_versions(&path, &plan.closure, recorded)?;
            let lines: Vec<String> = changed
                .iter()
                .map(|(file, old, new)| format!("{} {old} -> {new}", file.display()))
                .collect();
            std::fs::write(&bumped, lines.join("\n") + "\n")
                .map_err(|error| format!("cannot record the version bump: {error}"))?;
        }
    }
    Ok(path)
}

fn make_checkout(kind: Checkout, plan: &Plan) -> Result<PathBuf, String> {
    let closure = &plan.closure;
    let name = closure
        .root
        .file_name()
        .map_or_else(|| std::ffi::OsString::from("workspace"), std::ffi::OsStr::to_os_string);
    let checkouts = plan.scratch.join("checkouts");
    let to = match kind {
        Checkout::Original => return Ok(closure.root.clone()),
        Checkout::Moved => checkouts.join("moved").join("elsewhere").join("deeper").join(&name),
        Checkout::Control => checkouts.join("control").join(&name),
        Checkout::Effort => checkouts.join("effort").join(&name),
    };
    super::closure::copy_closure(closure, &to, &[plan.scratch.as_path()]).map_err(|error| {
        format!("cannot copy `{}` to `{}`: {error}", closure.root.display(), to.display())
    })?;
    let workspace = to.join(&closure.workspace);
    let root_manifest = crate::config::discover_manifest(&workspace).ok_or_else(|| {
        format!("the copy at `{}` has no workspace root manifest", workspace.display())
    })?;
    match kind {
        Checkout::Control => set_trust_key(&root_manifest, "backstop", 1)?,
        Checkout::Effort => set_trust_key(&root_manifest, "effort", 1)?,
        Checkout::Original | Checkout::Moved => {}
    }
    Ok(to)
}

/// Whether `dir` is a directory a checkout copy leaves out: version-control
/// state (`.git`, a directory or a worktree's file) and Cargo's build output
/// (a directory holding `CACHEDIR.TAG`).
fn left_out(path: &Path, is_dir: bool) -> bool {
    path.file_name().is_some_and(|name| name == ".git")
        || (is_dir && path.join("CACHEDIR.TAG").is_file())
}

/// The Cargo configuration files above `dir` that Cargo reads for a command
/// run there: `.cargo/config.toml` and `.cargo/config` in every proper
/// ancestor, nearest first, but `$CARGO_HOME`'s, which Cargo reads wherever it
/// runs. What is in `dir` and below is the checkout's own, which a copy
/// carries; what is above is not. Two legs that read different files vary
/// Cargo's configuration (`[build] jobs`, `rustflags`, `[env]`) beside their
/// axis's condition, which `judge::judge_axis` refuses to compare.
pub(crate) fn ancestor_cargo_configs(dir: &Path) -> Vec<PathBuf> {
    let home = crate::config::cargo_home().map(|home| home.canonicalize().unwrap_or(home));
    dir.ancestors()
        .skip(1)
        .map(|ancestor| ancestor.join(".cargo"))
        .filter(|cargo_dir| home.as_ref() != Some(cargo_dir))
        .flat_map(|cargo_dir| ["config.toml", "config"].map(|name| cargo_dir.join(name)))
        .filter(|path| path.is_file())
        .collect()
}

/// Copy the directory `from` into `to` (created if missing): every file,
/// directory and symlink (as a symlink), but version-control state, Cargo's
/// build output and the `exclude`d directories. A file is copied by
/// `std::fs::copy`, which clones it where the file system can (APFS's
/// `fclonefileat`), so a copy shares the original's blocks until one is
/// written. A symlink to an absolute path inside `within` (the tree the copy
/// is made of) is refused, naming it: every copy would read the original
/// there, so no axis could move what it reads.
pub(crate) fn copy_tree(
    from: &Path,
    to: &Path,
    exclude: &[&Path],
    within: &Path,
) -> io::Result<()> {
    std::fs::create_dir_all(to)?;
    let mut pending = vec![(from.to_path_buf(), to.to_path_buf())];
    while let Some((source, destination)) = pending.pop() {
        for entry in std::fs::read_dir(&source)? {
            let entry = entry?;
            let path = entry.path();
            let target = destination.join(entry.file_name());
            let kind = entry.file_type()?;
            if left_out(&path, kind.is_dir()) || exclude.iter().any(|skip| path == *skip) {
                continue;
            }
            if kind.is_symlink() {
                refuse_absolute_link_into(&path, within)?;
                copy_symlink(&path, &target)?;
            } else if kind.is_dir() {
                std::fs::create_dir(&target)?;
                pending.push((path, target));
            } else if kind.is_file() {
                std::fs::copy(&path, &target)?;
            }
            // Sockets, FIFOs and devices are no part of a source tree.
        }
    }
    Ok(())
}

/// Refuse the symlink at `path` when it names an absolute path inside
/// `within`, as written or as the file system resolves either.
fn refuse_absolute_link_into(path: &Path, within: &Path) -> io::Result<()> {
    let link = std::fs::read_link(path)?;
    if !link.is_absolute() {
        return Ok(());
    }
    let normalized = crate::project_root::lexically_normalized(&link);
    let resolved = normalized.canonicalize().unwrap_or_else(|_| normalized.clone());
    let roots = [Some(within.to_path_buf()), within.canonicalize().ok()];
    let inside = roots
        .iter()
        .flatten()
        .any(|root| normalized.starts_with(root) || resolved.starts_with(root));
    if inside {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "`{}` is a symlink to the absolute path `{}`, inside `{}`: every copy would read \
                 the original there, so no axis could move it; make the link relative",
                path.display(),
                link.display(),
                within.display()
            ),
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn copy_symlink(path: &Path, target: &Path) -> io::Result<()> {
    std::os::unix::fs::symlink(std::fs::read_link(path)?, target)
}

#[cfg(not(unix))]
fn copy_symlink(path: &Path, target: &Path) -> io::Result<()> {
    if path.is_dir() {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            format!("cannot copy the directory symlink `{}` here", path.display()),
        ))
    } else {
        std::fs::copy(path, target).map(|_| ())
    }
}

/// Read a manifest as a TOML table.
fn read_manifest(path: &Path) -> Result<toml::Table, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read `{}`: {error}", path.display()))?;
    text.parse::<toml::Table>().map_err(|error| format!("`{}`: {error}", path.display()))
}

fn write_manifest(path: &Path, table: &toml::Table) -> Result<(), String> {
    let text = toml::to_string(table)
        .map_err(|error| format!("cannot write `{}`: {error}", path.display()))?;
    std::fs::write(path, text)
        .map_err(|error| format!("cannot write `{}`: {error}", path.display()))
}

/// Set `[trust] <key> = <value>` in a copy's root manifest, keeping every other
/// key of the table it may already have. The manifest is rewritten from its
/// parsed form: its meaning is kept, its comments and layout are not (it is
/// the verb's copy, never the caller's file).
pub(crate) fn set_trust_key(manifest: &Path, key: &str, value: i64) -> Result<(), String> {
    let mut table = read_manifest(manifest)?;
    let trust = table
        .entry("trust")
        .or_insert_with(|| toml::Value::Table(toml::Table::new()))
        .as_table_mut()
        .ok_or_else(|| format!("`{}`: `trust` is not a table", manifest.display()))?;
    trust.insert(key.to_string(), toml::Value::Integer(value));
    write_manifest(manifest, &table)
}

/// `MAJOR.MINOR.PATCH[-pre][+build]` with its patch component one higher; the
/// smallest change, so a caret requirement on it still matches (except on a
/// `0.0.x` version, which a caret pins exactly).
pub(crate) fn bump_patch(version: &str) -> Option<String> {
    let split = version.find(['-', '+']).unwrap_or(version.len());
    let (core, rest) = version.split_at(split);
    let parts: Vec<&str> = core.split('.').collect();
    let [major, minor, patch] = parts.as_slice() else { return None };
    if [major, minor, patch]
        .iter()
        .any(|part| part.is_empty() || !part.bytes().all(|byte| byte.is_ascii_digit()))
    {
        return None;
    }
    let patch = patch.parse::<u64>().ok()?.checked_add(1)?;
    Some(format!("{major}.{minor}.{patch}{rest}"))
}

/// Where a package's version is declared: its own `[package] version`, or,
/// for `version.workspace = true`, its workspace root's `[workspace.package]
/// version`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct VersionSite {
    manifest: PathBuf,
    workspace: bool,
}

impl VersionSite {
    fn table_path(&self) -> &'static [&'static str] {
        if self.workspace { &["workspace", "package"] } else { &["package"] }
    }
}

/// Where the package whose manifest is `manifest` declares its version.
/// `Ok(None)`: the package declares no version (Cargo reads 0.0.0).
fn version_site(root: &Path, manifest: &Path) -> Result<Option<VersionSite>, String> {
    let table = read_manifest(manifest)?;
    let site = match table
        .get("package")
        .and_then(toml::Value::as_table)
        .and_then(|package| package.get("version"))
    {
        Some(toml::Value::String(_)) => {
            VersionSite { manifest: manifest.to_path_buf(), workspace: false }
        }
        Some(toml::Value::Table(inherit))
            if inherit.get("workspace").and_then(toml::Value::as_bool) == Some(true) =>
        {
            let root_manifest = crate::config::policy_manifest(manifest.parent().unwrap_or(root))
                .map_err(|error| error.to_string())?
                .unwrap_or_else(|| manifest.to_path_buf());
            VersionSite { manifest: root_manifest, workspace: true }
        }
        Some(other) => {
            return Err(format!(
                "`{}`: version `{other}` is neither a version nor `version.workspace = true`",
                manifest.display()
            ));
        }
        None => return Ok(None),
    };
    Ok(Some(site))
}

/// Bump the patch component of the version of every package in `packages` in
/// the copy at `root` of `closure` — the package's own `[package] version`,
/// or the `[workspace.package] version` it inherits — and its entry in the
/// `Cargo.lock` of the copy's workspace (the one the legs resolve with,
/// [`bump_in_lock`]), so a `--locked` leg still resolves. A recorded package is
/// the package of that name the closure read (`PathClosure::packages`, the
/// manifests the resolve reads), the workspace member among several. A
/// workspace version moves every package of the closure that inherits it, so
/// their lock entries move too, recorded or not; Cargo writes one lock entry
/// per path package name and version, so the entry names the package. Nothing
/// else changes: not a vendored crate (whose `.cargo-checksum.json` a bump
/// would break), not a fixture the resolve does not read, and nothing outside
/// the copy. Every package must have its version moved, or the axis would
/// compare a copy with itself: a package no package of the closure names, a
/// name several non-members share, a package that declares no version (Cargo
/// reads it as 0.0.0), and one whose version is declared outside the copy (a
/// workspace root Cargo's search found above it) are each an error. Returns
/// each change as `(file, old, new)`.
pub(crate) fn bump_versions(
    root: &Path,
    closure: &PathClosure,
    packages: &BTreeSet<String>,
) -> Result<Vec<(PathBuf, String, String)>, String> {
    if packages.is_empty() {
        return Err("the moved leg recorded no package, so no version could be bumped".to_string());
    }
    // Each package whose lock entry moves, by its manifest in the copy: its
    // name, and where its version is declared.
    let mut sites: BTreeMap<PathBuf, (String, VersionSite)> = BTreeMap::new();
    for package in packages {
        let manifest = root.join(&recorded_package(closure, root, package)?.manifest);
        let Some(site) = version_site(root, &manifest)? else {
            return Err(format!(
                "package `{package}` (`{}`) declares no version, which Cargo reads as 0.0.0: the \
                 version axis has no version of it to move",
                manifest.display()
            ));
        };
        if !site.manifest.starts_with(root) {
            return Err(format!(
                "package `{package}` (`{}`) inherits its version from `{}`, outside the copy at \
                 `{}`: the version axis bumps nothing outside the copy",
                manifest.display(),
                site.manifest.display(),
                root.display()
            ));
        }
        sites.insert(manifest, (package.clone(), site));
    }
    let mut changed = Vec::new();
    let mut moved: BTreeMap<VersionSite, (String, String)> = BTreeMap::new();
    for (_, site) in sites.values() {
        if moved.contains_key(site) {
            continue;
        }
        let mut table = read_manifest(&site.manifest)?;
        let mut current = Some(&mut table);
        for part in site.table_path() {
            current =
                current.and_then(|table| table.get_mut(*part)).and_then(toml::Value::as_table_mut);
        }
        let version = current
            .and_then(|table| table.get_mut("version"))
            .filter(|value| value.is_str())
            .ok_or_else(|| {
                format!(
                    "`{}` declares no `{}` version",
                    site.manifest.display(),
                    site.table_path().join(".")
                )
            })?;
        let old = version.as_str().unwrap_or_default().to_string();
        let new = bump_patch(&old).ok_or_else(|| {
            format!("`{}`: version `{old}` is not MAJOR.MINOR.PATCH", site.manifest.display())
        })?;
        *version = toml::Value::String(new.clone());
        write_manifest(&site.manifest, &table)?;
        changed.push((site.manifest.clone(), old.clone(), new.clone()));
        moved.insert(site.clone(), (old, new));
    }
    // A package of the closure the legs did not record that inherits a moved
    // workspace version moved with it, so its lock entry moves too.
    let moved_workspaces: BTreeSet<&PathBuf> =
        moved.keys().filter(|site| site.workspace).map(|site| &site.manifest).collect();
    if !moved_workspaces.is_empty() {
        for package in &closure.packages {
            let manifest = root.join(&package.manifest);
            if sites.contains_key(&manifest) {
                continue;
            }
            if let Ok(Some(site)) = version_site(root, &manifest) {
                if site.workspace && moved_workspaces.contains(&site.manifest) {
                    sites.insert(manifest, (package.name.clone(), site));
                }
            }
        }
    }
    let lock = root.join(&closure.workspace).join("Cargo.lock");
    let mut text = match std::fs::read_to_string(&lock) {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(changed),
        Err(error) => return Err(format!("cannot read `{}`: {error}", lock.display())),
    };
    for (package, site) in sites.values() {
        if let Some((old, new)) = moved.get(site) {
            let (bumped, present) = bump_in_lock(&text, package, old, new);
            text = bumped;
            if present {
                changed.push((
                    lock.clone(),
                    format!("{package} {old}"),
                    format!("{package} {new}"),
                ));
            }
        }
    }
    std::fs::write(&lock, text)
        .map_err(|error| format!("cannot write `{}`: {error}", lock.display()))?;
    Ok(changed)
}

/// The package of `closure` a record of `package` is of: the one the closure
/// names so, or the workspace member among several (Cargo refuses two members
/// of one name). Several non-members, or none, are refused: which of them the
/// legs built is not known.
fn recorded_package<'a>(
    closure: &'a PathClosure,
    root: &Path,
    package: &str,
) -> Result<&'a ClosurePackage, String> {
    let named: Vec<&ClosurePackage> =
        closure.packages.iter().filter(|candidate| candidate.name == package).collect();
    let members: Vec<&ClosurePackage> =
        named.iter().copied().filter(|candidate| candidate.member).collect();
    match (named.as_slice(), members.as_slice()) {
        ([only], _) | (_, [only]) => Ok(*only),
        ([], _) => Err(format!(
            "no package of the path closure copied to `{}` is named `{package}`, so its version \
             cannot be bumped",
            root.display()
        )),
        (several, _) => Err(format!(
            "{} packages of the path closure copied to `{}` are named `{package}` ({}), and no \
             single workspace member among them: which of them the legs built is not known",
            several.len(),
            root.display(),
            several
                .iter()
                .map(|candidate| candidate.manifest.display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// Move path package `name` from version `old` to `new` in the text of a
/// `Cargo.lock`, as Cargo writes it: the `version` line of its `[[package]]`
/// block (one with no `source` line, which a path package never has), and
/// every dependency entry `"<name> <old>"` (a path package's entry carries no
/// source). Every other byte is kept, so the text Cargo re-renders for the
/// bumped workspace is the text `--locked` compares it with. Returns the text
/// and whether the package's block was there.
pub(crate) fn bump_in_lock(text: &str, name: &str, old: &str, new: &str) -> (String, bool) {
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let name_line = format!("name = \"{name}\"");
    let old_version_line = format!("version = \"{old}\"");
    let (old_entry, new_entry) = (format!("\"{name} {old}\""), format!("\"{name} {new}\""));
    let entry = |line: &str| {
        let trimmed = line.trim();
        if trimmed == old_entry || trimmed.strip_suffix(',') == Some(old_entry.as_str()) {
            line.replacen(&old_entry, &new_entry, 1)
        } else {
            line.to_string()
        }
    };
    let mut out = String::with_capacity(text.len());
    let mut found = false;
    let mut index = 0;
    while index < lines.len() {
        if lines[index].trim_end() != "[[package]]" {
            out.push_str(&entry(lines[index]));
            index += 1;
            continue;
        }
        let end = (index + 1..lines.len())
            .find(|&next| lines[next].starts_with('['))
            .unwrap_or(lines.len());
        let block = &lines[index..end];
        let ours = block.iter().any(|line| line.trim_end() == name_line)
            && block.iter().any(|line| line.trim_end() == old_version_line)
            && !block.iter().any(|line| line.starts_with("source = "));
        found |= ours;
        for line in block {
            if ours && line.trim_end() == old_version_line {
                out.push_str(&line.replacen(&old_version_line, &format!("version = \"{new}\""), 1));
            } else {
                out.push_str(&entry(line));
            }
        }
        index = end;
    }
    (out, found)
}

/// The packages a check recorded, read from its target directory: every
/// `trust.package.v1` record under `trust/packages`, each with its
/// `trust.obligations.v1` record. A leg's target directory is its own and
/// fresh, so every record in it is the leg's; another host's (`--against`) is
/// the directory its check wrote, carried here. The two records of a package
/// are rendered from one value; a pair that disagrees is refused.
pub(crate) fn read_records(target_dir: &Path) -> Result<BTreeMap<String, UnitFacts>, String> {
    let packages_dir = crate::package_record::package_records_dir(target_dir);
    let obligations_dir = crate::obligations::records_dir(target_dir);
    let mut units = BTreeMap::new();
    let entries = match std::fs::read_dir(&packages_dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(units),
        Err(error) => return Err(format!("cannot read `{}`: {error}", packages_dir.display())),
    };
    let mut paths: Vec<PathBuf> = entries
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "json"))
        .collect();
    paths.sort();
    for path in paths {
        let text = crate::input_limits::read_bounded_utf8_file(
            &path,
            crate::input_limits::MAX_RELEASE_METADATA_BYTES,
        )
        .map_err(|error| format!("cannot read `{}`: {error}", path.display()))?;
        let record: PackageRecordView = serde_json::from_str(&text)
            .map_err(|error| format!("`{}` is not a package record: {error}", path.display()))?;
        if record.schema != crate::package_record::PACKAGE_RECORD_SCHEMA {
            return Err(format!(
                "`{}` names schema `{}`, not `{}`",
                path.display(),
                record.schema,
                crate::package_record::PACKAGE_RECORD_SCHEMA
            ));
        }
        let obligations = crate::obligations::read_package_obligations(
            &crate::obligations::obligation_record_path(&obligations_dir, &record.package),
        )?;
        let unit = UnitFacts::of_records(record.into_facts(), obligations)
            .map_err(|error| format!("`{}`: {error}", path.display()))?;
        units.insert(unit.package.clone(), unit);
    }
    Ok(units)
}

/// The fields of a `trust.package.v1` record the verb reads.
#[derive(serde::Deserialize)]
struct PackageRecordView {
    schema: String,
    package: String,
    outcome: String,
    profile: String,
    vector: String,
    worker_threads: u64,
    stop_causes: trust_types::determinism::StopCauseTally,
    noted_stops: Vec<trust_types::determinism::NotedStop>,
    conflicting_def_paths: usize,
}

/// What the package record adds to the obligation record's header.
pub(crate) struct PackageRecordFacts {
    pub(crate) package: String,
    pub(crate) outcome: String,
    pub(crate) profile: String,
    pub(crate) vector: String,
    pub(crate) worker_threads: u64,
    pub(crate) stop_causes: trust_types::determinism::StopCauseTally,
    pub(crate) noted_stops: Vec<trust_types::determinism::NotedStop>,
    pub(crate) conflicting_def_paths: usize,
}

impl PackageRecordView {
    fn into_facts(self) -> PackageRecordFacts {
        PackageRecordFacts {
            package: self.package,
            outcome: self.outcome,
            profile: self.profile,
            vector: self.vector,
            worker_threads: self.worker_threads,
            stop_causes: self.stop_causes,
            noted_stops: self.noted_stops,
            conflicting_def_paths: self.conflicting_def_paths,
        }
    }
}
