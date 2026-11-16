// trust-router/ay_discovery.rs: which `ay` binary a process outside the
// compiler spawns.
//
// ONE RULE, ONCE THE COMPILER'S. Until plan P4 / T4.1 (2026-10-10), `trustc`
// spawned an `ay` for its Liskov checks: an explicit path when one was given,
// and that path was authoritative (an unusable one failed closed on that path;
// it never fell back), and otherwise the `ay` beside the running `trustc`'s own
// executable (`current_exe()`). `trustc` now links its ay and spawns none. This
// module keeps that rule for the places that still spawn `ay`: a Trust tool
// shipped in the toolchain's `bin/` (`ay_beside_current_exe`) and the
// real-solver tests (`resolve_test_ay`), whose "running trustc" is the Trust
// compiler under test.
//
// The tests are handed a NAME for that compiler, and the file beside the name
// is not always the file beside the executable that runs. An exec shim (atpkg's
// `bin/trustc` is one) runs a compiler in another directory and sits beside an
// `ay` shim for a different solver. So the tests ask the compiler where it
// lives (`--print sysroot`) and take `<sysroot>/bin/ay`, which is the file its
// `current_exe()` rule spawns. `ay_of_trust_compiler` has the one layout where
// the two still differ, and refuses it.
//
// `PATH` is never searched and nothing is built. The `ay` first on `PATH` is
// whatever was installed last, not the solver of the toolchain under test:
// when this module was written it was a published solver compiled by stock
// rustc, a month older than the toolchain's own, and 32 of 35 trust checkouts
// on that machine judged Trust's verifier against it (stock-Rust audit M4,
// 2026-09-29).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// The solver's file name on this host.
pub const AY_EXE: &str = if cfg!(windows) { "ay.exe" } else { "ay" };

const TRUSTC_EXE: &str = if cfg!(windows) { "trustc.exe" } else { "trustc" };

/// Names the exact `ay` the real-solver tests drive. Authoritative when set.
pub const TEST_AY_ENV: &str = "TRUST_TEST_AY";

/// Names the Trust toolchain `bin/` under test (the gates' hand-off to their
/// children). Authoritative when set: the tests drive the `ay` beside its
/// `trustc`.
pub const STAGE2_BIN_ENV: &str = "TRUST_STAGE2_BIN";

/// The `ay` a Trust tool installed in a toolchain's `bin/` spawns: the one
/// beside it, as the compiler does. `None` only when the running executable's
/// own path is unknown.
#[must_use]
pub fn ay_beside_current_exe() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    Some(exe.parent()?.join(AY_EXE))
}

/// True when `compiler` is a Trust compiler: its `-vV` carries the `trust:`
/// line stock rustc never prints.
#[must_use]
pub fn is_trust_compiler(compiler: &Path) -> bool {
    Command::new(compiler).arg("-vV").stdin(Stdio::null()).stderr(Stdio::null()).output().is_ok_and(
        |out| {
            out.status.success()
                && String::from_utf8_lossy(&out.stdout).lines().any(|l| l.starts_with("trust:"))
        },
    )
}

/// The solver the real-solver tests drive.
#[derive(Debug, Clone)]
pub struct TestAy {
    pub path: PathBuf,
    /// The first line of `ay --version`.
    pub version: String,
    /// The rule that chose it, e.g. `TRUST_STAGE2_BIN=/…/bin`.
    pub source: String,
}

impl fmt::Display for TestAy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {} ({})", self.version, self.path.display(), self.source)
    }
}

/// No usable solver: the real-solver tests did NOT run. Carries every place
/// the resolver looked and why each was refused, so the failure names its fix.
#[derive(Debug, Clone)]
pub struct TestAyNotRun {
    pub tried: Vec<String>,
}

impl fmt::Display for TestAyNotRun {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "NOT RUN: no Trust `ay` for the real-solver tests (PATH is never searched and \
             nothing is built). Looked at:"
        )?;
        for tried in &self.tried {
            writeln!(f, "  - {tried}")?;
        }
        write!(
            f,
            "Set {TEST_AY_ENV}=<absolute path of an ay>, or {STAGE2_BIN_ENV}=<the bin/ of a Trust \
             toolchain that ships ay>, or run the tests with a Trust toolchain that ships ay."
        )
    }
}

impl std::error::Error for TestAyNotRun {}

/// The real-solver tests' `ay`, read from this process's environment.
/// `checkout_root` is the trust checkout the tests were built from; its
/// `build/host/stage{2,1}/bin` holds the checkout's own compiler.
pub fn resolve_test_ay(checkout_root: &Path) -> Result<TestAy, TestAyNotRun> {
    resolve_test_ay_from(&|name| std::env::var_os(name), checkout_root)
}

/// `resolve_test_ay` for a real-solver test: the solver, after printing the
/// `ay detected:` line the logs are read for, or the NOT RUN diagnostic. The
/// test turns an `Err` into its own failure
/// (`.unwrap_or_else(|not_run| panic!("{not_run}"))`), so the panic lives in
/// test code and not in this production module (TCB panic gate, 2026-10-10).
pub fn detect_test_ay(checkout_root: &Path) -> Result<TestAy, TestAyNotRun> {
    let ay = resolve_test_ay(checkout_root)?;
    eprintln!("ay detected: {ay}");
    Ok(ay)
}

/// `resolve_test_ay` over an explicit environment, in precedence order:
///
/// 1. `TRUST_TEST_AY`: that absolute path, and nothing else.
/// 2. `TRUST_STAGE2_BIN`: the `ay` of that directory's `trustc`, and nothing
///    else.
/// 3. The `ay` of a Trust compiler, first usable wins: `$RUSTC` (the compiler
///    of this run, when it is set); this checkout's `build/host/stage2` and
///    `stage1`; the `trustc` beside `$CARGO` (the toolchain running the tests,
///    which compiles them with that `trustc` when `$RUSTC` is unset).
///
/// "The `ay` of a compiler" is [`ay_of_trust_compiler`]'s: the solver in the
/// sysroot the compiler reports, never merely the file beside its name.
pub fn resolve_test_ay_from(
    env: &dyn Fn(&str) -> Option<OsString>,
    checkout_root: &Path,
) -> Result<TestAy, TestAyNotRun> {
    let var = |name: &str| env(name).filter(|value| !value.is_empty()).map(PathBuf::from);

    if let Some(path) = var(TEST_AY_ENV) {
        let source = format!("{TEST_AY_ENV}={}", path.display());
        let checked = if path.is_absolute() {
            ay_version(&path).map(|version| (path, version))
        } else {
            Err("not an absolute path".to_string())
        };
        return checked
            .map(|(path, version)| TestAy { path, version, source: source.clone() })
            .map_err(|why| TestAyNotRun { tried: vec![format!("{source}: {why}")] });
    }
    if let Some(bin) = var(STAGE2_BIN_ENV) {
        let source = format!("{STAGE2_BIN_ENV}={}", bin.display());
        return ay_of_trust_compiler(&bin.join(TRUSTC_EXE))
            .map(|(path, version)| TestAy { path, version, source: source.clone() })
            .map_err(|why| TestAyNotRun { tried: vec![format!("{source}: {why}")] });
    }

    let mut compilers: Vec<(String, PathBuf)> = Vec::new();
    if let Some(rustc) = var("RUSTC") {
        compilers.push((format!("RUSTC={}", rustc.display()), rustc));
    }
    for stage in ["stage2", "stage1"] {
        let bin = checkout_root.join("build/host").join(stage).join("bin");
        compilers.push((format!("this checkout's {stage}"), bin.join(TRUSTC_EXE)));
    }
    if let Some(cargo) = var("CARGO") {
        let source = format!("the trustc beside CARGO={}", cargo.display());
        compilers.push((source, cargo.with_file_name(TRUSTC_EXE)));
    }

    let mut tried = Vec::new();
    for (source, compiler) in compilers {
        match ay_of_trust_compiler(&compiler) {
            Ok((path, version)) => return Ok(TestAy { path, version, source }),
            Err(why) => tried.push(format!("{source}: {why}")),
        }
    }
    Err(TestAyNotRun { tried })
}

/// The `ay` the Trust compiler named `compiler` spawns: `<sysroot>/bin/ay`,
/// where `<sysroot>` is the compiler's own answer to `--print sysroot`.
///
/// The compiler takes the `ay` beside its `current_exe()`, the executable that
/// actually runs, which need not sit beside the name it was run by. An exec
/// shim runs a compiler somewhere else: atpkg's `bin/trustc` execs the store's
/// trust 9192, and the `ay` beside that shim is another shim, for the store's
/// ay 8256, which stock rustc built. Taking the file beside the name drove ay
/// 8256 while the compiler behind the same name drives 9192's own ay. The
/// compiler's sysroot report follows shims and directory links to the
/// toolchain that runs, and its `bin/` is the `current_exe()` directory.
///
/// One layout still separates the two: `compiler` is itself a symlink placed
/// outside its toolchain's `bin/`. macOS's `current_exe()` keeps the link's
/// path, so the compiler run through that link looks for `ay` beside the link
/// (measured 2026-09-30), while `--print sysroot` names the toolchain. That
/// compiler is refused rather than guessed at.
fn ay_of_trust_compiler(compiler: &Path) -> Result<(PathBuf, String), String> {
    if !compiler.is_absolute() {
        return Err(format!(
            "{} is not an absolute path; finding its directory would take a PATH search",
            compiler.display()
        ));
    }
    if !compiler.is_file() {
        return Err(format!("no compiler at {}", compiler.display()));
    }
    if !is_trust_compiler(compiler) {
        return Err(format!(
            "{} is not a Trust compiler (its -vV has no `trust:` line)",
            compiler.display()
        ));
    }
    let sysroot = compiler_sysroot(compiler)?;
    let bin = sysroot.join("bin");
    let is_link = std::fs::symlink_metadata(compiler).is_ok_and(|meta| meta.is_symlink());
    if is_link && !same_directory(compiler.parent(), &bin) {
        return Err(format!(
            "{} is a link from outside its toolchain's {}; the compiler run through it takes \
             the ay beside the link, not its toolchain's, so neither is a sound choice: name \
             the toolchain's own trustc",
            compiler.display(),
            bin.display()
        ));
    }
    let ay = bin.join(AY_EXE);
    let version = ay_version(&ay).map_err(|why| format!("{}: {why}", ay.display()))?;
    Ok((ay, version))
}

/// The compiler's own report of its sysroot: one absolute path on one line.
fn compiler_sysroot(compiler: &Path) -> Result<PathBuf, String> {
    let shown = compiler.display();
    let out = Command::new(compiler)
        .args(["--print", "sysroot"])
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .map_err(|error| format!("cannot run `{shown} --print sysroot`: {error}"))?;
    if !out.status.success() {
        return Err(format!("`{shown} --print sysroot` failed ({})", out.status));
    }
    let text = String::from_utf8(out.stdout)
        .map_err(|_| format!("`{shown} --print sysroot` is not UTF-8"))?;
    let line = text.strip_suffix('\n').unwrap_or(&text);
    let line = line.strip_suffix('\r').unwrap_or(line);
    let sysroot = PathBuf::from(line);
    if line.is_empty() || line.contains('\n') || !sysroot.is_absolute() || !sysroot.is_dir() {
        return Err(format!(
            "`{shown} --print sysroot` is not one existing absolute directory: {text:?}"
        ));
    }
    Ok(sysroot)
}

/// True when `a` and `b` resolve to the same directory. Unresolvable is false.
fn same_directory(a: Option<&Path>, b: &Path) -> bool {
    match (a.map(std::fs::canonicalize), std::fs::canonicalize(b)) {
        (Some(Ok(a)), Ok(b)) => a == b,
        _ => false,
    }
}

/// The first line of `ay --version`, which must name `ay`.
fn ay_version(ay: &Path) -> Result<String, String> {
    if !ay.is_file() {
        return Err("no such file".to_string());
    }
    let out = Command::new(ay)
        .arg("--version")
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .map_err(|error| format!("cannot run it: {error}"))?;
    if !out.status.success() {
        return Err(format!("`--version` failed ({})", out.status));
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let first = stdout.lines().next().unwrap_or("").trim();
    if first.split_whitespace().next() != Some("ay") {
        return Err(format!("`--version` does not name ay: {first:?}"));
    }
    Ok(first.to_string())
}

#[cfg(all(test, unix))]
mod tests {
    use std::collections::HashMap;
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;

    /// A private directory of stand-in executables, removed on drop.
    struct Fixture {
        root: PathBuf,
    }

    impl Fixture {
        fn new(label: &str) -> Self {
            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos();
            let root = std::env::temp_dir()
                .join(format!("trust-ay-discovery-{label}-{}-{nonce:x}", std::process::id()));
            std::fs::create_dir_all(&root).expect("create fixture");
            Self { root }
        }

        fn script(&self, rel: &str, body: &str) -> PathBuf {
            let path = self.root.join(rel);
            std::fs::create_dir_all(path.parent().expect("parent")).expect("fixture dir");
            std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write script");
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))
                .expect("make script executable");
            path
        }

        /// A `bin/` holding a compiler (Trust or stock) and, optionally, an ay.
        /// The compiler reports `bin/..` as its sysroot, as a real one does.
        fn toolchain(&self, rel: &str, trust: bool, with_ay: bool) -> PathBuf {
            let bin = self.root.join(rel);
            let sysroot = bin.parent().expect("sysroot").display().to_string();
            self.compiler(&format!("{rel}/{TRUSTC_EXE}"), trust, &format!("echo '{sysroot}'"));
            if with_ay {
                self.script(&format!("{rel}/{AY_EXE}"), &format!("echo 'ay 0.0.0-{rel}'"));
            }
            bin
        }

        /// A stand-in compiler: `-vV` (with a `trust:` line when `trust`), and
        /// `print_sysroot` as its answer to `--print sysroot`.
        fn compiler(&self, rel: &str, trust: bool, print_sysroot: &str) -> PathBuf {
            let vv = if trust { "binary: trustc\\ntrust: 0.1.0" } else { "binary: rustc" };
            self.script(
                rel,
                &format!(
                    "case \"$1\" in\n  -vV) printf 'rustc 1.99.0\\n{vv}\\n' ;;\n  --print) \
                     {print_sysroot} ;;\n  *) exit 1 ;;\nesac"
                ),
            )
        }

        /// An `ay` that must never run: it records being run.
        fn decoy_ay(&self, rel: &str) -> (PathBuf, PathBuf) {
            let marker = self.root.join(format!("{}.ran", rel.replace('/', "-")));
            let ay =
                self.script(rel, &format!(": > '{}'\necho 'ay 8.2.5-decoy'", marker.display()));
            (ay, marker)
        }

        /// An `ay` on a PATH directory that records being run.
        fn path_trap(&self) -> (PathBuf, PathBuf) {
            let marker = self.root.join("path-ay-ran");
            let dir = self.root.join("path");
            self.script(
                &format!("path/{AY_EXE}"),
                &format!(": > '{}'\necho 'ay 9.9.9-path'", marker.display()),
            );
            (dir, marker)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.root);
        }
    }

    fn resolve(vars: &[(&str, &Path)], checkout: &Path) -> Result<TestAy, TestAyNotRun> {
        let env: HashMap<String, OsString> =
            vars.iter().map(|(k, v)| (k.to_string(), v.as_os_str().to_owned())).collect();
        resolve_test_ay_from(&|name| env.get(name).cloned(), checkout)
    }

    #[test]
    fn a_path_only_ay_is_neither_picked_nor_run() {
        let fx = Fixture::new("path-only");
        let (path_dir, marker) = fx.path_trap();
        let err = resolve(&[("PATH", &path_dir)], &fx.root.join("checkout")).unwrap_err();
        assert!(!marker.exists(), "the resolver ran the ay on PATH");
        let text = err.to_string();
        assert!(text.starts_with("NOT RUN:"), "{text}");
        assert!(text.contains("this checkout's stage2") && text.contains(TEST_AY_ENV), "{text}");
    }

    #[test]
    fn an_explicit_ay_is_authoritative_and_never_falls_back() {
        let fx = Fixture::new("explicit");
        let (path_dir, marker) = fx.path_trap();
        let chosen = fx.script("chosen/ay", "echo 'ay 1.2.3'");
        let bin = fx.toolchain("tc/bin", true, true);
        let ok = resolve(
            &[(TEST_AY_ENV, &chosen), (STAGE2_BIN_ENV, &bin), ("PATH", &path_dir)],
            &fx.root,
        )
        .expect("explicit ay");
        assert_eq!((ok.path.as_path(), ok.version.as_str()), (chosen.as_path(), "ay 1.2.3"));

        // Unusable explicit values fail closed on themselves: a missing file, a
        // relative name (which would be a PATH search), a binary that is not ay.
        let not_ay = fx.script("other/ay", "echo 'z3 4.13'");
        for bad in [fx.root.join("missing/ay"), PathBuf::from("ay"), not_ay] {
            let err =
                resolve(&[(TEST_AY_ENV, &bad), (STAGE2_BIN_ENV, &bin)], &fx.root).unwrap_err();
            assert_eq!(err.tried.len(), 1, "{err}");
            assert!(err.tried[0].starts_with(&format!("{TEST_AY_ENV}={}", bad.display())), "{err}");
        }
        assert!(!marker.exists());
    }

    #[test]
    fn stage2_bin_names_the_toolchain_whose_ay_is_used() {
        let fx = Fixture::new("stage2-bin");
        let bin = fx.toolchain("tc/bin", true, true);
        let ok = resolve(&[(STAGE2_BIN_ENV, &bin)], &fx.root).expect("toolchain ay");
        assert_eq!(ok.path, bin.join(AY_EXE));
        assert_eq!(ok.version, "ay 0.0.0-tc/bin");

        // A toolchain without ay, or whose compiler is not Trust, is refused
        // even though a usable toolchain exists elsewhere (the checkout's).
        fx.toolchain("build/host/stage2/bin", true, true);
        let bare = fx.toolchain("bare/bin", true, false);
        let stock = fx.toolchain("stock/bin", false, true);
        for refused in [bare, stock] {
            let err = resolve(&[(STAGE2_BIN_ENV, &refused)], &fx.root).unwrap_err();
            assert_eq!(err.tried.len(), 1, "{err}");
        }
    }

    #[test]
    fn implicit_candidates_are_trust_compilers_in_order() {
        let fx = Fixture::new("implicit");
        let checkout = fx.root.join("checkout");
        let running = fx.toolchain("running/bin", true, true);
        let cargo = running.join("targo");
        let ok = resolve(&[("CARGO", &cargo)], &checkout).expect("running toolchain");
        assert_eq!(ok.path, running.join(AY_EXE));

        // This checkout's stage1, then stage2, outrank the running toolchain.
        fx.toolchain("checkout/build/host/stage1/bin", true, true);
        let ok = resolve(&[("CARGO", &cargo)], &checkout).expect("checkout stage1");
        assert!(ok.path.ends_with("stage1/bin/ay"), "{ok:?}");
        fx.toolchain("checkout/build/host/stage2/bin", true, true);
        let ok = resolve(&[("CARGO", &cargo)], &checkout).expect("checkout stage2");
        assert!(ok.path.ends_with("stage2/bin/ay"), "{ok:?}");

        // $RUSTC, the compiler of this run, outranks both when it is Trust.
        let rustc_bin = fx.toolchain("rustc/bin", true, true);
        let ok = resolve(&[("RUSTC", &rustc_bin.join(TRUSTC_EXE)), ("CARGO", &cargo)], &checkout)
            .expect("RUSTC sibling");
        assert_eq!(ok.path, rustc_bin.join(AY_EXE));

        // A stock or relative $RUSTC is passed over, never searched for.
        let stock = fx.toolchain("stock/bin", false, true);
        for rustc in [stock.join(TRUSTC_EXE), PathBuf::from("rustc")] {
            let ok = resolve(&[("RUSTC", &rustc)], &checkout).expect("next candidate");
            assert!(ok.path.ends_with("stage2/bin/ay"), "{ok:?}");
        }
    }

    #[test]
    fn a_stock_toolchain_running_the_tests_lends_no_ay() {
        let fx = Fixture::new("stock-cargo");
        let stock = fx.toolchain("stock/bin", false, true);
        let err = resolve(&[("CARGO", &stock.join("cargo"))], &fx.root).unwrap_err();
        assert!(err.to_string().contains("is not a Trust compiler"), "{err}");
    }

    /// atpkg's layout: `shim/bin/trustc` execs a Trust compiler in another
    /// toolchain, and the `ay` beside the shim is a different solver. The
    /// compiler behind the shim spawns its own toolchain's ay, and so do the
    /// tests, whichever route names the shim.
    #[test]
    fn an_exec_shim_lends_its_compilers_ay_not_the_ay_beside_it() {
        let fx = Fixture::new("exec-shim");
        let tc = fx.toolchain("tc/bin", true, true);
        let shim = fx.script(
            &format!("shim/bin/{TRUSTC_EXE}"),
            &format!("exec '{}' \"$@\"", tc.join(TRUSTC_EXE).display()),
        );
        let (_, decoy_ran) = fx.decoy_ay(&format!("shim/bin/{AY_EXE}"));
        let shim_bin = shim.parent().expect("shim bin").to_path_buf();
        let shim_targo = shim_bin.join("targo");
        let checkout = fx.root.join("checkout");
        for var in [
            ("RUSTC", shim.as_path()),
            (STAGE2_BIN_ENV, shim_bin.as_path()),
            ("CARGO", shim_targo.as_path()),
        ] {
            let ok = resolve(&[var], &checkout).expect("the shimmed compiler's ay");
            assert_eq!((ok.path, ok.version.as_str()), (tc.join(AY_EXE), "ay 0.0.0-tc/bin"));
        }
        assert!(!decoy_ran.exists(), "the ay beside the shim was run");
    }

    /// A link to `trustc` placed outside its toolchain: the compiler run
    /// through it looks beside the link (macOS `current_exe()` keeps the link's
    /// path), its sysroot names the toolchain. Refused, never guessed. A link
    /// inside the toolchain's own `bin/`, or a linked directory, is the
    /// toolchain itself and resolves normally.
    #[test]
    fn a_link_to_trustc_from_outside_its_toolchain_is_refused() {
        use std::os::unix::fs::symlink;

        let fx = Fixture::new("link");
        let tc = fx.toolchain("tc/bin", true, true);
        std::fs::create_dir_all(fx.root.join("link/bin")).expect("link dir");
        let link = fx.root.join("link/bin").join(TRUSTC_EXE);
        symlink(tc.join(TRUSTC_EXE), &link).expect("link trustc");
        let (_, decoy_ran) = fx.decoy_ay(&format!("link/bin/{AY_EXE}"));
        let err = resolve(&[(STAGE2_BIN_ENV, &fx.root.join("link/bin"))], &fx.root).unwrap_err();
        assert_eq!(err.tried.len(), 1, "{err}");
        assert!(err.tried[0].contains("is a link from outside its toolchain"), "{err}");
        assert!(!decoy_ran.exists(), "the ay beside the link was run");

        let inner = tc.join("rustc");
        symlink(tc.join(TRUSTC_EXE), &inner).expect("link rustc");
        let linked_dir = fx.root.join("tc-link");
        symlink(&tc, &linked_dir).expect("link the bin directory");
        for rustc in [inner, linked_dir.join(TRUSTC_EXE)] {
            let ok = resolve(&[("RUSTC", &rustc)], &fx.root).expect("the toolchain's ay");
            assert_eq!(ok.path, tc.join(AY_EXE), "{rustc:?}");
        }
    }

    /// The sysroot report is the compiler's word on where it lives; an
    /// unusable one lends no ay, even with an ay beside the compiler's name.
    #[test]
    fn a_compiler_without_a_usable_sysroot_report_lends_no_ay() {
        let fx = Fixture::new("sysroot-report");
        let missing = fx.root.join("no-such-sysroot").display().to_string();
        for (label, print) in [
            ("fails", "exit 3".to_string()),
            ("relative", "echo 'tc'".to_string()),
            ("missing", format!("echo '{missing}'")),
            ("two-lines", format!("printf '%s\\n%s\\n' '{0}' '{0}'", fx.root.display())),
        ] {
            let compiler = fx.compiler(&format!("{label}/bin/{TRUSTC_EXE}"), true, &print);
            fx.script(&format!("{label}/bin/{AY_EXE}"), "echo 'ay 0.0.0'");
            let err = resolve(&[("RUSTC", &compiler)], &fx.root).unwrap_err();
            assert!(err.tried[0].contains("--print sysroot"), "{label}: {err}");
        }
    }
}
