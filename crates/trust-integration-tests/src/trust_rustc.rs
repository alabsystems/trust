//! The Trust rustc that the real-compiler tests in `tests/` measure.
//!
//! One resolver for every test that compiles through the Trust fork
//! (`e2e_real_rustc`, `functional_postcondition_mir_loop`,
//! `real_kernel_fn_trust_loop`): [`require_trust_rustc`] returns a compiler that
//! passed the capability probe, or PANICS saying what was searched and how to
//! get one. Nothing here skips, and nothing reports a test as run when no
//! compiler ran it.
//!
//! Resolution:
//! 1. `TRUST_RUSTC`, when set and non-empty. It is AUTHORITATIVE: it names the
//!    compiler the caller asked about, so one that is not an executable file, or
//!    fails the probe, is an error instead of a fallback to a discovered
//!    compiler. It is measured whatever its age; a stale one fails the test
//!    that needs the newer revision, and its identity says it is stale.
//! 2. Otherwise `build/<dir>/stage{1,2}/bin/rustc` for every `<dir>` under
//!    `build/`: a sysroot with libstd first, then stage1 before stage2, then
//!    `build/host`. A fork this checkout's history shows to predate
//!    [`FLAG_SURFACE`], or the caller's `min_fix`, is passed over; the first
//!    remaining one is selected and must pass the probe. A selected fork that
//!    fails the probe is NOT passed over for the next candidate: that would hide
//!    a regression in it behind another's pass.
//!
//! The probe ([`probe_trust_capability`]) compiles an unguarded divide under
//! [`ADVISORY_JSON_ARGS`] and requires a `function_result` transport line for it
//! that THIS tree's `trust_types` parses: a stock rustc, a fork without the
//! verify pass, and a fork speaking an older transport schema all fail it.
//!
//! History: `e2e_real_rustc.rs` grew this resolver on 2026-09-30, after its
//! capability probe had found "no Trust rustc" on every host and every test had
//! printed SKIPPING and passed. `functional_postcondition_mir_loop.rs` and
//! `real_kernel_fn_trust_loop.rs` kept their own searches, which returned green
//! (SKIPPING, NOT RUN) when nothing was found, tried a stale stage2 before a
//! current stage1, and in `real_kernel`'s case passed over every fork older
//! than its fix with NOT RUN. Hoisted here 2026-10-09. Since TRUST_RUSTC-1
//! (2026-11-03) every test that needs a Trust rustc goes through
//! [`require_trust_rustc`] and runs with its crate's other tests: none is
//! `#[ignore]`d for want of a compiler, and the land gate's crates-tests leg
//! hands a member whose closure holds this crate this tree's stage 1 as
//! `TRUST_RUSTC` (scripts/land_gate.py, `stage1_crates_members`).

use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_types::{
    FunctionTransportResult, TRANSPORT_PREFIX, TransportMessage, parse_transport_payload,
};

/// The flags every transport / MIR-dump compile through a Trust rustc passes:
/// JSON transport on stderr, under the advisory policy (the strict default
/// refuses the probe's unguarded divide, on purpose).
pub const ADVISORY_JSON_ARGS: &[&str] =
    &["-Z", "trust-verify-output=json", "-Z", "trust-policy=advisory"];

/// The last of the `-Z` flags these tests pass to land: `-Ztrust-policy`
/// (576db732cd, 2026-07-24, "one flag surface"). `-Ztrust-dump=mir:<dir>`,
/// `-Ztrust-verify=off` and `-Ztrust-verify-output` exist at it too. A fork
/// built before it rejects [`ADVISORY_JSON_ARGS`] as unknown options, so a
/// discovered one is passed over rather than measured. Every resolution
/// requires it; `min_fix` adds a second revision.
pub const FLAG_SURFACE: &str = "576db732cdcfafc929fcae11eaeac38928f40671";

/// How to get a compiler, in every resolution failure.
const HOW: &str = "Build one with `./x.py build --stage 1` (under native build-tree ownership), \
     or set TRUST_RUSTC=/path/to/a/Trust/rustc";

/// What this checkout's history says about whether a fork's revision contains
/// a given commit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Provenance {
    /// The revision contains it.
    Contains,
    /// The revision does not contain it: the fork's verdict would be about its age.
    Predates,
    /// Not established, with the reason. Such a fork is measured, not passed over.
    Unknown(String),
}

/// One Trust rustc, identified.
#[derive(Clone, Debug)]
pub struct TrustRustc {
    pub path: PathBuf,
    /// `commit-hash` from `rustc -vV`, when the fork reports one.
    pub commit: Option<String>,
    /// Whether the fork's revision contains [`FLAG_SURFACE`].
    pub surface: Provenance,
    /// The caller's `min_fix`, and whether the fork's revision contains it.
    pub min_fix: Option<(String, Provenance)>,
    /// Commits in this checkout's HEAD that the fork lacks, when known.
    pub behind_head: Option<usize>,
}

impl TrustRustc {
    /// Read `path`'s revision from `rustc -vV` and place it in `repo`'s history.
    #[must_use]
    pub fn identify(repo: &Path, path: PathBuf, min_fix: Option<&str>) -> Self {
        let commit = compiler_commit(&path);
        let surface = provenance(repo, FLAG_SURFACE, commit.as_deref());
        let min_fix =
            min_fix.map(|fix| (fix.to_string(), provenance(repo, fix, commit.as_deref())));
        let behind_head = commit.as_deref().and_then(|c| commits_behind_head(repo, c));
        Self { path, commit, surface, min_fix, behind_head }
    }

    /// Whether this checkout's history shows the fork predates a revision the
    /// caller needs. Only a negative ancestry answer counts.
    #[must_use]
    pub fn is_stale(&self) -> bool {
        self.surface == Provenance::Predates
            || self.min_fix.as_ref().is_some_and(|(_, p)| *p == Provenance::Predates)
    }

    /// Path, revision and age, for every message that names this compiler: a
    /// stale fork's failure must say it is stale.
    #[must_use]
    pub fn identity(&self) -> String {
        let mut facts =
            vec![format!("commit-hash {}", self.commit.as_deref().unwrap_or("unknown"))];
        facts.push(describe(FLAG_SURFACE, &self.surface));
        if let Some((fix, provenance)) = &self.min_fix {
            facts.push(describe(fix, provenance));
        }
        if let Some(n) = self.behind_head {
            facts.push(format!("{n} commit(s) behind this checkout's HEAD"));
        }
        format!("{} ({})", self.path.display(), facts.join("; "))
    }
}

fn describe(fix: &str, provenance: &Provenance) -> String {
    let short = &fix[..fix.len().min(10)];
    match provenance {
        Provenance::Contains => format!("contains {short}"),
        Provenance::Predates => format!("PREDATES {short}"),
        Provenance::Unknown(why) => format!("{short} not established: {why}"),
    }
}

/// The Trust rustc a test measures, resolved once per test binary and
/// `min_fix`; panics with what was searched and how to get one when none is
/// usable. `min_fix` names a commit the test's verdict depends on (beyond
/// [`FLAG_SURFACE`]): a discovered fork that predates it is passed over.
#[must_use]
pub fn require_trust_rustc(min_fix: Option<&str>) -> TrustRustc {
    type Resolved = Vec<(Option<String>, Result<TrustRustc, String>)>;
    static RESOLVED: Mutex<Resolved> = Mutex::new(Vec::new());
    let key = min_fix.map(str::to_string);
    let result = {
        let mut resolved = RESOLVED.lock().unwrap_or_else(PoisonError::into_inner);
        match resolved.iter().find(|(known, _)| *known == key) {
            Some((_, result)) => result.clone(),
            None => {
                let result = resolve_trust_rustc_from(
                    &find_repo_root(),
                    std::env::var_os("TRUST_RUSTC"),
                    min_fix,
                );
                resolved.push((key, result.clone()));
                result
            }
        }
    };
    match result {
        Ok(rustc) => {
            // Printed per test (libtest captures per test thread), so every
            // failing test's output names the compiler it measured.
            eprintln!("Using Trust rustc: {}", rustc.identity());
            rustc
        }
        Err(why) => panic!("{why}"),
    }
}

/// [`require_trust_rustc`]'s resolution against an explicit repo root and
/// `TRUST_RUSTC` value, so the fail-closed paths are tested hermetically.
pub fn resolve_trust_rustc_from(
    repo_root: &Path,
    trust_rustc_env: Option<OsString>,
    min_fix: Option<&str>,
) -> Result<TrustRustc, String> {
    if let Some(path) = explicit_trust_rustc(trust_rustc_env)? {
        let rustc = TrustRustc::identify(repo_root, path, min_fix);
        return probe_trust_capability(&rustc).map(|()| rustc);
    }

    let candidates = trust_rustc_candidates(repo_root);
    let mut found: Vec<PathBuf> = Vec::new();
    let mut seen: Vec<PathBuf> = Vec::new();
    for candidate in candidates.iter().filter(|candidate| is_executable_file(candidate)) {
        // build/host is a symlink to build/<triple>: measure each binary once.
        let canonical = fs::canonicalize(candidate).unwrap_or_else(|_| candidate.clone());
        if !seen.contains(&canonical) {
            seen.push(canonical);
            found.push(candidate.clone());
        }
    }

    if found.is_empty() {
        let searched: Vec<String> =
            candidates.iter().map(|candidate| format!("  {}", candidate.display())).collect();
        return Err(format!(
            "No executable Trust rustc found and TRUST_RUSTC is unset. Searched:\n{}\n{HOW}",
            searched.join("\n")
        ));
    }

    found.sort_by_key(|candidate| {
        (
            usize::from(!candidate_has_libstd(candidate)),
            usize::from(
                !candidate
                    .parent()
                    .and_then(Path::parent)
                    .is_some_and(|stage| stage.file_name().is_some_and(|name| name == "stage1")),
            ),
            usize::from(!candidate.starts_with(repo_root.join("build/host"))),
            candidate.to_string_lossy().into_owned(),
        )
    });

    let discovered =
        found.into_iter().map(|path| TrustRustc::identify(repo_root, path, min_fix)).collect();
    let rustc = select(None, discovered)?;
    if !candidate_has_libstd(&rustc.path)
        && let Some(sysroot) = sysroot_from_rustc_path(&rustc.path)
    {
        eprintln!(
            "WARNING: selected rustc sysroot appears to lack libstd artifacts under {}. \
             Compilation failures will include full rustc diagnostics.",
            sysroot.join("lib/rustlib").display()
        );
    }
    probe_trust_capability(&rustc).map(|()| rustc)
}

/// `TRUST_RUSTC` as the caller set it. Unset or empty is `Ok(None)`. A value
/// that names no executable file is an error: dropping it would measure a
/// discovered compiler in its place, or report "TRUST_RUSTC is unset" when it
/// is set.
pub fn explicit_trust_rustc(value: Option<OsString>) -> Result<Option<PathBuf>, String> {
    let Some(value) = value.filter(|v| !v.is_empty()) else {
        return Ok(None);
    };
    let path = PathBuf::from(value);
    if is_executable_file(&path) {
        Ok(Some(path))
    } else {
        // cargo runs a test binary in its package directory, not where the
        // caller typed the command, so a repo-relative value misses.
        let relative = if path.is_relative() {
            let cwd = std::env::current_dir()
                .map_or_else(|e| format!("<unknown: {e}>"), |cwd| cwd.display().to_string());
            format!(
                " (a relative path, resolved against this test's working directory {cwd}: give an absolute one)"
            )
        } else {
            String::new()
        };
        Err(format!(
            "TRUST_RUSTC={} is not an executable file{relative}. TRUST_RUSTC is authoritative, so \
             no discovered compiler is measured in its place: point it at a Trust rustc, or unset \
             it to search build/*/stage{{1,2}}/bin/rustc",
            path.display()
        ))
    }
}

/// The fork to measure. An explicit `TRUST_RUSTC` always wins: it is the
/// compiler the caller asked about, so a stale one fails loudly with its
/// identity instead of being passed over. Otherwise the first discovered fork
/// (in the caller's order) that is not established to be stale.
pub fn select(
    explicit: Option<TrustRustc>,
    discovered: Vec<TrustRustc>,
) -> Result<TrustRustc, String> {
    if let Some(rustc) = explicit {
        return Ok(rustc);
    }
    if discovered.is_empty() {
        return Err(format!("No executable Trust rustc found and TRUST_RUSTC is unset. {HOW}"));
    }
    // Every revision some candidate was required to contain, for the message.
    let mut needed = vec![FLAG_SURFACE.to_string()];
    for (fix, _) in discovered.iter().filter_map(|rustc| rustc.min_fix.as_ref()) {
        if !needed.contains(fix) {
            needed.push(fix.clone());
        }
    }
    let mut passed_over = Vec::new();
    for rustc in discovered {
        if rustc.is_stale() {
            passed_over.push(rustc.identity());
            continue;
        }
        return Ok(rustc);
    }
    Err(format!(
        "every Trust rustc found predates a revision these tests need ({}), so measuring it \
         would judge its age, not this tree: {}. {HOW} (a TRUST_RUSTC naming one of them is \
         measured whatever its age)",
        needed.join(" and "),
        passed_over.join("; ")
    ))
}

/// Every place discovery looks, in search order before sorting.
#[must_use]
pub fn trust_rustc_candidates(repo_root: &Path) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    for stage in ["stage1", "stage2"] {
        for slot in
            ["host", "aarch64-apple-darwin", "x86_64-apple-darwin", "x86_64-unknown-linux-gnu"]
        {
            add_unique_candidate(
                &mut candidates,
                repo_root.join("build").join(slot).join(stage).join("bin/rustc"),
            );
        }
    }

    let build_dir = repo_root.join("build");
    let mut discovered = Vec::new();
    if let Ok(entries) = fs::read_dir(&build_dir) {
        for entry in entries.flatten() {
            discovered.push(entry.path().join("stage1/bin/rustc"));
            discovered.push(entry.path().join("stage2/bin/rustc"));
        }
    }
    discovered.sort();

    for candidate in discovered {
        add_unique_candidate(&mut candidates, candidate);
    }

    candidates
}

/// `commit-hash` from `rustc -vV`; `None` when the fork does not report one.
#[must_use]
pub fn compiler_commit(rustc: &Path) -> Option<String> {
    let output = Command::new(rustc).arg("-vV").output().ok()?;
    if !output.status.success() {
        return None;
    }
    commit_from_version_verbose(&String::from_utf8_lossy(&output.stdout))
}

/// The `commit-hash:` line of a `rustc -vV` report; `None` when it is absent,
/// empty or `unknown`.
#[must_use]
pub fn commit_from_version_verbose(text: &str) -> Option<String> {
    text.lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .map(str::trim)
        .filter(|hash| !hash.is_empty() && *hash != "unknown")
        .map(str::to_string)
}

/// Whether `commit` contains `fix`, by `git merge-base --is-ancestor` in `repo`.
///
/// Ancestry has one blind spot in the direction that passes a fork over: a
/// fork built from a branch that cherry-picked or backported the fix (a
/// different commit) still answers "not an ancestor", so it reads as
/// `Predates`. Accepted because the discovered forks are built from this
/// checkout, where a fix arrives only by ancestry; to measure such a fork
/// anyway, name it in TRUST_RUSTC, which is measured whatever this answers.
/// The positive direction is not proof either (docs/TOOLCHAIN_POSTURE.md:
/// ancestry is necessary, not sufficient, because a build tree can differ from
/// its HEAD), which is why a `Contains` fork is still probed and measured
/// rather than trusted.
#[must_use]
pub fn provenance(repo: &Path, fix: &str, commit: Option<&str>) -> Provenance {
    let Some(commit) = commit else {
        return Provenance::Unknown("the fork reports no commit-hash".to_string());
    };
    match Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["merge-base", "--is-ancestor", fix, commit])
        .output()
    {
        Ok(output) => {
            provenance_from_exit(output.status.code(), &String::from_utf8_lossy(&output.stderr))
        }
        Err(e) => Provenance::Unknown(format!("cannot run git: {e}")),
    }
}

/// `git merge-base --is-ancestor` exits 0 when the fix is in the revision, 1
/// when it is not, and anything else when git could not tell (for example a
/// revision this clone lacks). Only 1 passes a fork over.
#[must_use]
pub fn provenance_from_exit(code: Option<i32>, stderr: &str) -> Provenance {
    match code {
        Some(0) => Provenance::Contains,
        Some(1) => Provenance::Predates,
        other => Provenance::Unknown(format!(
            "git merge-base --is-ancestor exited {other:?}: {}",
            stderr.trim()
        )),
    }
}

fn commits_behind_head(repo: &Path, commit: &str) -> Option<usize> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["rev-list", "--count", &format!("{commit}..HEAD")])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8_lossy(&output.stdout).trim().parse().ok()
}

fn add_unique_candidate(candidates: &mut Vec<PathBuf>, candidate: PathBuf) {
    if !candidates.iter().any(|existing| existing == &candidate) {
        candidates.push(candidate);
    }
}

/// A regular file with an execute bit (any file, off unix).
#[must_use]
pub fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = fs::metadata(path) else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        metadata.permissions().mode() & 0o111 != 0
    }

    #[cfg(not(unix))]
    {
        true
    }
}

/// `<sysroot>` for `<sysroot>/bin/rustc`.
#[must_use]
pub fn sysroot_from_rustc_path(rustc: &Path) -> Option<PathBuf> {
    rustc.parent().and_then(|bin| bin.parent()).map(Path::to_path_buf)
}

/// Whether `rustc`'s path-derived sysroot holds a `libstd` rlib or rmeta.
#[must_use]
pub fn candidate_has_libstd(rustc: &Path) -> bool {
    sysroot_from_rustc_path(rustc).is_some_and(|sysroot| sysroot_has_libstd(&sysroot))
}

fn sysroot_has_libstd(sysroot: &Path) -> bool {
    let rustlib = sysroot.join("lib/rustlib");
    let Ok(targets) = fs::read_dir(&rustlib) else {
        return false;
    };

    targets.flatten().any(|target| {
        let lib_dir = target.path().join("lib");
        let Ok(files) = fs::read_dir(lib_dir) else {
            return false;
        };
        files.flatten().any(|file| {
            let name = file.file_name();
            let name = name.to_string_lossy();
            name.starts_with("libstd-") && (name.ends_with(".rlib") || name.ends_with(".rmeta"))
        })
    })
}

/// Prove the selected compiler is a Trust rustc that runs the verify pass
/// under the exact flags the tests pass ([`ADVISORY_JSON_ARGS`]): it must
/// compile the probe and emit a `function_result` transport line for it that
/// THIS tree's `trust_types` parses. The probe's divide is unguarded, so a
/// strict compile refuses it by design; that is why the probe runs in the
/// advisory lane.
pub fn probe_trust_capability(rustc: &TrustRustc) -> Result<(), String> {
    let label = "Trust rustc capability probe";
    let tmp = ProbeDir::new()
        .map_err(|error| format!("could not create a directory for the {label}: {error}"))?;
    let src_path = tmp.0.join("trust_probe.rs");
    let output_path = tmp.0.join("libtrust_probe.rlib");
    fs::write(&src_path, "pub fn trust_probe_div(a: u32, b: u32) -> u32 { a / b }\n")
        .map_err(|error| format!("could not write the {label} source: {error}"))?;

    let mut cmd =
        verified_lib_command_with_args(&rustc.path, &src_path, &output_path, ADVISORY_JSON_ARGS);
    let (output, command_line) = run_rustc_command(label, &mut cmd);
    if !output.status.success() {
        return Err(format!(
            "{} is not a usable Trust rustc: the {label} did not compile.\n{}",
            rustc.identity(),
            rustc_failure_diagnostic(label, &rustc.path, &command_line, &output)
        ));
    }

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    if extract_function_results(&messages)
        .iter()
        .any(|result| result.function.ends_with("trust_probe_div"))
    {
        return Ok(());
    }

    let raw_lines = stderr.lines().filter(|line| line.trim().starts_with(TRANSPORT_PREFIX)).count();
    Err(format!(
        "{} compiled the {label} but emitted no parseable `function_result` transport for \
         trust_probe_div ({raw_lines} raw {TRANSPORT_PREFIX} line(s), {} parsed by this tree's \
         trust_types). A fork with no lines lacks the Trust verify pass; one whose lines do not \
         parse speaks an older transport schema than this checkout. Rebuild it \
         (`./x.py build --stage 1`) or set TRUST_RUSTC to a current one.\n{}",
        rustc.identity(),
        messages.len(),
        rustc_failure_diagnostic(label, &rustc.path, &command_line, &output)
    ))
}

/// A fresh directory under the system temp dir, removed on drop. (The library
/// has no `tempfile` dependency; its tests do.) `create_dir`, not
/// `create_dir_all`: an existing path is an error, never reused.
struct ProbeDir(PathBuf);

impl ProbeDir {
    fn new() -> std::io::Result<Self> {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_nanos());
        let dir = std::env::temp_dir().join(format!(
            "trust-rustc-probe-{}-{nanos}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir)?;
        Ok(Self(dir))
    }
}

impl Drop for ProbeDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// The Trust repo root: two levels above this crate's manifest directory.
#[must_use]
pub fn find_repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/trust-integration-tests -> crates -> repo root
    manifest.parent().and_then(|p| p.parent()).map(|p| p.to_path_buf()).unwrap_or(manifest)
}

/// A `--crate-type lib` compile of `src_path` into `output_path` through
/// `rustc`, with `extra_args` first and cargo's environment scrubbed.
#[must_use]
pub fn verified_lib_command_with_args(
    rustc: &Path,
    src_path: &Path,
    output_path: &Path,
    extra_args: &[&str],
) -> Command {
    let mut cmd = Command::new(rustc);
    // Scrub cargo-injected env so the inner rustc runs as a bare rustc rather
    // than one that inherits the workspace `cargo test` is building. These
    // variables once chose trust_verify's proof-cache path
    // (`target/trust-proofs/<crate>.json` under cargo, `.trust-cache/` in the
    // cwd otherwise); that cache left the compiler in 2c9fdb1dd5e, and the
    // scrub stays so the inner compile never sees the outer cargo's identity.
    for var in [
        "CARGO_TARGET_DIR",
        "CARGO_MANIFEST_DIR",
        "CARGO_CRATE_NAME",
        "CARGO_PKG_NAME",
        "CARGO_PKG_VERSION",
        "CARGO",
        "TRUST_DUMP_MIR",
    ] {
        cmd.env_remove(var);
    }
    cmd.args(extra_args)
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(output_path)
        .arg(src_path);
    cmd
}

/// Run `cmd`, returning its output and a shell-quoted rendering of it; panics
/// only when the process cannot be spawned. The compiler borrows this test's
/// execution ([`lent_output`]).
pub fn run_rustc_command(label: &str, cmd: &mut Command) -> (Output, String) {
    let rendered = render_command(cmd);
    let output = lent_output(cmd)
        .unwrap_or_else(|e| panic!("failed to invoke {label}: {e}\nCommand: {rendered}"));
    (output, rendered)
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): run a compiler this test launches and
/// return its output, lending it the test's own execution when, and only
/// when, it is owed one ([`owed_a_lent_execution`]).
///
/// Targo hands a test binary no scheduler. In a strict custody context (any
/// `build-slot` admission marks one, and protocol 1 carries no GNU pool) a
/// compiler handed no GNU scheduler refuses: "native compiler work has no
/// captured inherited GNU scheduler". The lent scheduler is an owned GNU pool
/// holding NO token, so the compiler runs on the one execution of the test
/// thread that waits for it and gains no parallelism nobody admitted. A
/// process-wide guard runs one lent compiler at a time, whatever libtest's
/// thread count, and holds until that compiler is reaped. The descendant
/// handoff lets a process the compiler starts (Trust std hands it no
/// descriptor) recover the same pool from this live owner. No SDK, CPU or
/// fixed-claim custody is forwarded, so a compiler that requires it still
/// refuses.
///
/// Every other launch runs exactly as given: outside a strict context the
/// compiler is not owed a scheduler, and any GNU advertisement the child is
/// handed (valid, dangling or malformed) is forwarded unchanged, never
/// replaced, so the compiler's own capture still judges it and refuses a
/// broken one.
pub fn lent_output(cmd: &mut Command) -> std::io::Result<Output> {
    if !owed_a_lent_execution(cmd) {
        return cmd.output();
    }
    let loan = lend_execution(cmd)?;
    // `output` reaps the child before the loan drops. The command's spawn
    // hooks keep their own share of the owner until `cmd` itself drops.
    let output = cmd.output();
    drop(loan);
    output
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): one lent execution per process.
static ONE_LENT_EXECUTION: Mutex<()> = Mutex::new(());

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): the loan [`lent_output`] makes when it
/// is owed: an owned GNU pool holding ZERO tokens, advertised to one child with
/// the descendant handoff, and the process-wide guard that keeps it the only
/// loan until it drops. Keep it until that child is reaped. The owner drops
/// before the guard.
pub struct Loan {
    owner: jobserver_utils::Jobserver,
    _serial: MutexGuard<'static, ()>,
}

impl Loan {
    /// The lent pool's owner, for reading what it holds.
    pub fn owner(&self) -> &jobserver_utils::Jobserver {
        &self.owner
    }
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): lend `cmd`'s child this process's one
/// lent execution, waiting while another loan is held. A thread that already
/// holds a [`Loan`] must not ask for another.
pub fn lend_execution(cmd: &mut Command) -> std::io::Result<Loan> {
    let serial = ONE_LENT_EXECUTION.lock().unwrap_or_else(PoisonError::into_inner);
    let mut owner = jobserver_utils::Jobserver::new(0)?;
    owner.enable_descendant_handoff()?;
    owner.configure_make(cmd);
    Ok(Loan { owner, _serial: serial })
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): the markers that make a Trust compiler
/// strict (`strict_context` in compiler/rustc_data_structures/src/jobserver/early.rs),
/// less the descendant handoff, which is a GNU advertisement.
const STRICT_CUSTODY_MARKERS: [&str; 6] = [
    "BUILD_SLOT_CPU_PROTOCOL",
    "TRUST_CPU_HANDOFF",
    "TRUST_CPU_IMPLICIT_FD",
    "ATERM_SDK_LEASE_V3",
    "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1",
];

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): whether `cmd`'s child is owed a lent
/// execution. It is when its environment marks a strict custody context and
/// carries no GNU advertisement at all: no descendant handoff and none of
/// `CARGO_MAKEFLAGS`, `MAKEFLAGS` and `MFLAGS`, whatever their value. That is
/// the compiler's own reading (`capture` in jobserver/early.rs): a strict
/// compiler with any of these present judges the advertisement itself.
pub fn owed_a_lent_execution(cmd: &Command) -> bool {
    let advertised =
        [jobserver_utils::DESCENDANT_HANDOFF_ENV, "CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"]
            .into_iter()
            .any(|name| child_env(cmd, name).is_some());
    !advertised && STRICT_CUSTODY_MARKERS.into_iter().any(|name| child_env(cmd, name).is_some())
}

/// The value `name` takes in the environment `cmd` hands its child: the
/// command's own setting or removal, else this process's. (This crate never
/// clears a launched compiler's environment wholesale.)
fn child_env(cmd: &Command, name: &str) -> Option<OsString> {
    match cmd.get_envs().find(|(key, _)| *key == OsStr::new(name)) {
        Some((_, value)) => value.map(OsStr::to_os_string),
        None => std::env::var_os(name),
    }
}

/// Assert `output` succeeded, with [`rustc_failure_diagnostic`] as the message.
pub fn assert_rustc_success(label: &str, rustc: &Path, command_line: &str, output: &Output) {
    assert!(
        output.status.success(),
        "{}",
        rustc_failure_diagnostic(label, rustc, command_line, output)
    );
}

/// Status, compiler, sysroot, command line and both streams of a failed compile.
#[must_use]
pub fn rustc_failure_diagnostic(
    label: &str,
    rustc: &Path,
    command_line: &str,
    output: &Output,
) -> String {
    let sysroot = sysroot_from_rustc_path(rustc)
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "<unknown>".to_string());
    let std_status = if candidate_has_libstd(rustc) { "present" } else { "missing" };
    format!(
        "{label} failed\n\
         status: {}\n\
         rustc: {}\n\
         path-derived sysroot: {sysroot}\n\
         sysroot libstd artifacts: {std_status}\n\
         command: {command_line}\n\
         stdout:\n{}\n\
         stderr:\n{}",
        output.status,
        rustc.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    )
}

fn render_command(cmd: &Command) -> String {
    let mut parts = Vec::new();

    if let Some(current_dir) = cmd.get_current_dir() {
        parts.push("cd".to_string());
        parts.push(shell_quote(current_dir.as_os_str()));
        parts.push("&&".to_string());
    }

    for (key, value) in cmd.get_envs() {
        let key = key.to_string_lossy();
        match value {
            Some(value) => parts.push(format!("{key}={}", shell_quote(value))),
            None => parts.push(format!("env -u {key}")),
        }
    }

    parts.push(shell_quote(cmd.get_program()));
    parts.extend(cmd.get_args().map(shell_quote));
    parts.join(" ")
}

fn shell_quote(value: &OsStr) -> String {
    let value = value.to_string_lossy();
    if value.is_empty() {
        return "''".to_string();
    }
    if value
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '/' | '.' | '_' | '-' | ':' | '=' | '+'))
    {
        value.into_owned()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

/// Parse TRUST_JSON transport lines from compiler stderr output.
///
/// Each line matching `TRUST_JSON:{...}` is parsed as a TransportMessage.
/// Non-matching lines are silently skipped (they are regular compiler diagnostics).
#[must_use]
pub fn parse_transport_lines(stderr: &str) -> Vec<TransportMessage> {
    stderr
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            trimmed
                .strip_prefix(TRANSPORT_PREFIX)
                .and_then(|json| parse_transport_payload(json).ok())
        })
        .collect()
}

/// The `function_result` messages among `messages`.
#[must_use]
pub fn extract_function_results(messages: &[TransportMessage]) -> Vec<&FunctionTransportResult> {
    messages
        .iter()
        .filter_map(|msg| match msg {
            TransportMessage::FunctionResult(r) => Some(r),
            _ => None,
        })
        .collect()
}
