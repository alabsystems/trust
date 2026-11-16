//! The real-solver tests drive the `ay` the compiler would: an explicit path,
//! or the one in the sysroot of the Trust compiler under test. Never an `ay`
//! found on `PATH`, and never the file that merely sits beside the compiler's
//! name.
//!
//! Until 2026-09-30 `ay_test_support` searched `PATH` whenever the checkout had
//! no stage2 build, which on the machine that found it meant a published `ay`
//! compiled by stock rustc, a month older than the toolchain's own (stock-Rust
//! audit M4). Every case below re-runs this test binary as a child, under an
//! environment it sets completely, because resolution reads the process
//! environment once per process. The child resolves the solver through
//! `require_ay()` and sends one query through the session it returns, so each
//! case observes the `ay` the session SPAWNED, not only the one announced.
//! Every stand-in `ay` logs its runs; one sits first on the child's `PATH`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
#![cfg(unix)]

use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_integration_tests::ay_test_support::require_ay;
use trust_router::VerificationBackend as _;
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

/// Set by the parent half; the probe is a no-op without it.
const PROBE_ENV: &str = "TRUST_AY_RESOLUTION_PROBE";

/// The child half: resolve the solver exactly as every real-solver test does,
/// then solve one query on it (`x > 0 ∧ ¬(x > 0)`), as they do. `Fixture::probe`
/// re-executes it with `--ignored --exact`; it is `#[ignore]`d because without
/// `PROBE_ENV` it does nothing, and a plain run would count that as a pass.
#[test]
#[ignore = "subprocess child: re-executed by Fixture::probe (every test in this file)"]
fn resolution_probe() {
    if std::env::var_os(PROBE_ENV).is_some() {
        let x = Formula::Var("x".into(), Sort::Int);
        let positive = Formula::Gt(Box::new(x), Box::new(Formula::Int(0)));
        let vc = VerificationCondition {
            kind: VcKind::Precondition { callee: "probe".to_string() },
            function: "probe".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![positive.clone(), Formula::Not(Box::new(positive))]),
            contract_metadata: None,
            obligation: None,
        };
        let verdict = require_ay().with_timeout(20_000).verify(&vc);
        eprintln!("probe verdict: {verdict:?}");
    }
}

/// A stand-in `ay`: `path` runs it, `log` holds one line of arguments per run.
struct StandIn {
    path: PathBuf,
    log: PathBuf,
}

impl StandIn {
    /// The runs that were not `--version`: the session spawning it as a solver.
    fn solver_runs(&self) -> Vec<String> {
        std::fs::read_to_string(&self.log)
            .unwrap_or_default()
            .lines()
            .filter(|args| *args != "--version")
            .map(str::to_string)
            .collect()
    }

    fn ran(&self) -> bool {
        self.log.exists()
    }
}

struct Fixture {
    root: PathBuf,
    path_trap: StandIn,
}

impl Fixture {
    fn new(label: &str) -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let root = std::env::temp_dir()
            .join(format!("trust-ay-resolution-{label}-{}-{nonce:x}", std::process::id()));
        let path_trap = Self::stand_in_at(&root, "path/ay", "ay 9.9.9-path");
        Self { root, path_trap }
    }

    fn script_at(root: &Path, rel: &str, body: &str) -> PathBuf {
        let path = root.join(rel);
        std::fs::create_dir_all(path.parent().expect("parent")).expect("fixture dir");
        std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write script");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))
            .expect("make script executable");
        path
    }

    /// An `ay` that answers `--version` with `version` and logs every run. Run
    /// as a solver it exits at once, so the session's query ends Unknown.
    fn stand_in_at(root: &Path, rel: &str, version: &str) -> StandIn {
        let log = root.join(format!("{}.runs", rel.replace('/', "-")));
        let body = format!(
            "printf '%s\\n' \"$*\" >> '{}'\n[ \"$1\" = --version ] && echo '{version}'\nexit 0",
            log.display()
        );
        StandIn { path: Self::script_at(root, rel, &body), log }
    }

    fn script(&self, rel: &str, body: &str) -> PathBuf {
        Self::script_at(&self.root, rel, body)
    }

    fn stand_in(&self, rel: &str, version: &str) -> StandIn {
        Self::stand_in_at(&self.root, rel, version)
    }

    /// A Trust toolchain at `rel` (its `bin/trustc` answers `-vV` with a
    /// `trust:` line and `--print sysroot` with `rel`) and its `ay`.
    fn trust_toolchain(&self, rel: &str, version: &str) -> (PathBuf, StandIn) {
        let sysroot = self.root.join(rel);
        self.script(
            &format!("{rel}/bin/trustc"),
            &format!(
                "case \"$1\" in\n  -vV) printf 'rustc 1.99.0\\nbinary: trustc\\ntrust: 0.1.0\\n' \
                 ;;\n  --print) echo '{}' ;;\n  *) exit 1 ;;\nesac",
                sysroot.display()
            ),
        );
        (sysroot.join("bin"), self.stand_in(&format!("{rel}/bin/ay"), version))
    }

    /// Run the probe with only `PATH` (the trap first) and `vars` set.
    fn probe(&self, vars: &[(&str, &Path)]) -> (bool, String) {
        let exe = std::env::current_exe().expect("test binary path");
        let path = format!("{}:/usr/bin:/bin", self.root.join("path").display());
        // The probe is `#[ignore]`d: `--ignored` selects it, `--exact` only it.
        let out = Command::new(exe)
            .args(["--ignored", "--exact", "resolution_probe", "--nocapture", "--test-threads=1"])
            .env_clear()
            .env("PATH", path)
            .env(PROBE_ENV, "1")
            .envs(vars.iter().map(|(k, v)| (*k, *v)))
            .output()
            .expect("run the probe");
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        // A filter that selects no test also exits 0, and `ok || NOT RUN:`
        // below would read that as a pass: the probe must have been selected.
        assert!(text.contains("running 1 test"), "the probe did not run:\n{text}");
        assert!(!self.path_trap.ran(), "the ay on PATH was run:\n{text}");
        assert!(!text.contains(&self.path_trap.path.display().to_string()), "{text}");
        (out.status.success(), text)
    }

    /// The probe ran `chosen` as its solver, announced as `version`.
    fn assert_spawned(&self, chosen: &StandIn, version: &str, text: &str) {
        let detected = format!("ay detected: {version} at {}", chosen.path.display());
        assert!(text.contains(&detected), "expected `{detected}`:\n{text}");
        assert!(
            !chosen.solver_runs().is_empty(),
            "the session never spawned the chosen ay:\n{text}"
        );
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

#[test]
fn an_ay_on_path_is_neither_run_nor_picked() {
    let fixture = Fixture::new("path");
    let (ok, text) = fixture.probe(&[]);
    // With no explicit solver the child either finds this checkout's own
    // stage build or fails, NAMED. It never skips and never takes PATH's.
    assert!(ok || text.contains("NOT RUN:"), "{text}");
}

#[test]
fn trust_test_ay_is_the_solver_the_session_spawns() {
    let fixture = Fixture::new("explicit");
    let chosen = fixture.stand_in("chosen/ay", "ay 1.2.3-chosen");
    let (ok, text) = fixture.probe(&[("TRUST_TEST_AY", &chosen.path)]);
    assert!(ok, "{text}");
    fixture.assert_spawned(&chosen, "ay 1.2.3-chosen", &text);
}

#[test]
fn trust_stage2_bin_lends_its_compilers_ay() {
    let fixture = Fixture::new("stage2-bin");
    let (bin, chosen) = fixture.trust_toolchain("tc", "ay 4.5.6-toolchain");
    let (ok, text) = fixture.probe(&[("TRUST_STAGE2_BIN", &bin)]);
    assert!(ok, "{text}");
    fixture.assert_spawned(&chosen, "ay 4.5.6-toolchain", &text);
}

/// atpkg's `bin/`: a `trustc` that execs a Trust compiler elsewhere, beside
/// an `ay` for a different solver (on the machine that found this, ay 8256,
/// built by stock rustc). The compiler behind the shim drives its own
/// toolchain's ay, and so must the tests, by either route to the shim.
#[test]
fn an_exec_shim_trustc_lends_its_compilers_ay_not_the_ay_beside_it() {
    let fixture = Fixture::new("exec-shim");
    let (bin, chosen) = fixture.trust_toolchain("tc", "ay 4.5.6-toolchain");
    let shim =
        fixture.script("shim/bin/trustc", &format!("exec '{}/trustc' \"$@\"", bin.display()));
    let decoy = fixture.stand_in("shim/bin/ay", "ay 8.2.5-beside-the-shim");
    let shim_bin = fixture.root.join("shim/bin");
    for var in [("RUSTC", shim.as_path()), ("TRUST_STAGE2_BIN", shim_bin.as_path())] {
        let _ = std::fs::remove_file(&chosen.log);
        let (ok, text) = fixture.probe(&[var]);
        assert!(ok, "{text}");
        fixture.assert_spawned(&chosen, "ay 4.5.6-toolchain", &text);
        assert!(!decoy.ran(), "the ay beside the shim was run ({}):\n{text}", var.0);
    }
}

#[test]
fn a_missing_solver_is_a_named_failure() {
    let fixture = Fixture::new("missing");
    let missing = fixture.root.join("missing/ay");
    let (ok, text) = fixture.probe(&[("TRUST_TEST_AY", &missing)]);
    assert!(!ok, "a named solver that does not exist must fail the test:\n{text}");
    assert!(text.contains("NOT RUN:"), "{text}");
    assert!(text.contains(&format!("TRUST_TEST_AY={}: no such file", missing.display())), "{text}");
}
