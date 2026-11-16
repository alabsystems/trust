//! Trust (platform protocols, plan L1a; adversarial check of the inertness claim): the
//! `-Ztrust-platform-*` controls change no byte the compiler writes, and they are tracked
//! exactly as `[TRACKED_NO_CRATE_HASH]` promises, end to end.
//!
//! `trust-platform-flags-inert` pins the rlib and the object of a crate with no policy site.
//! This recipe attacks the claim where it is weakest:
//!
//! * Part 1, every output the compiler can be asked for. With verification on, the
//!   `fork` + strip + `execv` subject (a site the pass will analyse from L1d) is compiled with
//!   `--emit=link,obj,metadata,llvm-ir,asm,mir,dep-info`, the trust-ir dump
//!   (`-Ztrust-dump=ir:`, which the THIR retention `-Ztrust-platform-properties` turns on could
//!   reach) and the JSON verification transport, twice plain (a determinism CONTROL) and once
//!   with every control off its default. Every file the compile writes, and its stdout and
//!   stderr, must be byte-identical (dep-info after its own output paths are normalized). The
//!   facts sink points at a file that already exists: it must be left exactly as it was, not
//!   created, truncated or rewritten.
//! * Part 2, incremental reuse. The unit test pins the dep-tracking hash; this drives a real
//!   incremental session through `-Zassert-incr-state` (verification off, where reuse works).
//!   Moving any control must discard the session (so from L1d a cache built without the pass
//!   can never answer for a compile that asks for it), and a value-equal respelling (a
//!   duplicated property, the option repeated, explicit defaults, a leading zero) must reuse
//!   it, so the tracking is by value and not by spelling. The object written in every step
//!   must be the same bytes.
//!
//! Part 1's "no diagnostic, sink not written" pins are L1a-only; plan L1d changes them on
//! purpose (the pass prints its summary note and fills the sink).
//@ ignore-cross-compile

use std::path::{Path, PathBuf};

use run_make_support::{CompletedProcess, bin_name, cmd, cwd, rfs, rustc_path};

/// Set by compiletest's `--trust-vanilla` replay, which runs the stock rustc: no Trust options,
/// nothing to pin.
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

/// Every control moved off its default, the facts sink included.
fn all_controls(facts: &Path) -> Vec<String> {
    vec![
        "-Ztrust-platform-properties=fd-inherit".to_string(),
        "-Ztrust-platform-unanalysed=deny".to_string(),
        "-Ztrust-platform-budget=1".to_string(),
        "-Ztrust-platform-report=verbose".to_string(),
        format!("-Ztrust-platform-dump-facts={}", facts.display()),
    ]
}

fn trustc() -> PathBuf {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    if trustc.exists() { trustc } else { rustc }
}

/// Every regular file under `dir`, as (path relative to `dir`, bytes), sorted.
fn tree(dir: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    fn walk(root: &Path, dir: &Path, out: &mut Vec<(PathBuf, Vec<u8>)>) {
        let mut entries: Vec<PathBuf> =
            rfs::read_dir(dir).map(|entry| entry.expect("dir entry").path()).collect();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                walk(root, &path, out);
            } else {
                let relative = path.strip_prefix(root).expect("under root").to_path_buf();
                out.push((relative, rfs::read(&path)));
            }
        }
    }
    let mut out = Vec::new();
    walk(dir, dir, &mut out);
    out
}

/// Part 1: one verified compile writing every output kind into `out`.
fn compile_everything(out: &str, extra: &[String]) -> CompletedProcess {
    rfs::create_dir(out);
    let ir = format!("-Ztrust-dump=ir:{}", cwd().join(out).join("ir").display());
    let mut compiler = cmd(trustc());
    compiler
        .arg("lib.rs")
        .args([
            "--crate-type=rlib",
            "--crate-name=platform_adv",
            "--edition=2021",
            "--emit=link,obj,metadata,llvm-ir,asm,mir,dep-info",
            "-Copt-level=0",
            "-Ccodegen-units=1",
            "-Cdebuginfo=0",
            "-Ztrust-verify=on",
            "-Ztrust-policy=advisory",
            "-Ztrust-ir-lower=on",
            "-Ztrust-verify-output=json",
            "--out-dir",
            out,
        ])
        .arg(ir)
        .args(extra);
    compiler.run()
}

/// The outputs of a Part 1 compile, with the dep-info file's own output paths (which name the
/// output directory) normalized so two output directories can be compared.
fn outputs(out: &str) -> Vec<(PathBuf, Vec<u8>)> {
    tree(Path::new(out))
        .into_iter()
        .map(|(path, bytes)| {
            if path.extension().is_some_and(|ext| ext == "d") {
                let text = String::from_utf8(bytes).expect("dep-info is UTF-8");
                let text = text.replace(&format!("{out}/"), "<out>/");
                (path, text.into_bytes())
            } else {
                (path, bytes)
            }
        })
        .collect()
}

fn part1_every_output_is_byte_identical() {
    const SENTINEL: &[u8] = b"pre-existing facts file: an inert sink must not touch it\n";
    let facts = cwd().join("facts.preexisting");
    rfs::write(&facts, SENTINEL);

    let plain = compile_everything("plain", &[]);
    let control = compile_everything("control", &[]);
    let flagged = compile_everything("flagged", &all_controls(&facts));

    let plain_tree = outputs("plain");
    let names = |tree: &[(PathBuf, Vec<u8>)]| tree.iter().map(|(p, _)| p.clone()).collect::<Vec<_>>();
    for kind in ["rlib", "o", "rmeta", "ll", "s", "mir", "d"] {
        assert!(
            plain_tree.iter().any(|(p, _)| p.extension().is_some_and(|e| e == kind)),
            "no .{kind} output among {:?}: the comparison would not cover it",
            names(&plain_tree),
        );
    }
    assert!(
        plain_tree.iter().any(|(p, _)| p.starts_with("ir")),
        "the trust-ir dump wrote nothing: {:?}",
        names(&plain_tree),
    );

    let control_tree = outputs("control");
    assert_eq!(
        names(&plain_tree),
        names(&control_tree),
        "CONTROL: two plain compiles wrote different file sets",
    );
    for ((path, bytes), (_, other)) in plain_tree.iter().zip(&control_tree) {
        assert!(
            bytes == other,
            "CONTROL: two plain compiles wrote different {}; a byte comparison with the flagged \
             compile would prove nothing",
            path.display(),
        );
    }
    assert!(plain.stdout() == control.stdout(), "CONTROL: stdout differs");
    assert!(plain.stderr() == control.stderr(), "CONTROL: stderr differs");

    let flagged_tree = outputs("flagged");
    assert_eq!(
        names(&plain_tree),
        names(&flagged_tree),
        "-Ztrust-platform-* changed which files the compile writes",
    );
    for ((path, bytes), (_, other)) in plain_tree.iter().zip(&flagged_tree) {
        assert!(bytes == other, "-Ztrust-platform-* changed the emitted {}", path.display());
    }
    assert!(
        plain.stdout() == flagged.stdout(),
        "-Ztrust-platform-* changed stdout (the JSON verification transport):\n{}",
        flagged.stdout_utf8(),
    );
    assert!(
        plain.stderr() == flagged.stderr(),
        "-Ztrust-platform-* changed stderr:\n{}",
        flagged.stderr_utf8(),
    );
    assert_eq!(
        rfs::read(&facts),
        SENTINEL,
        "L1a: the facts sink touched a pre-existing file with no pass to fill it",
    );
}

/// Part 2: one incremental compile, verification off, asserting whether the session from the
/// previous step was loaded.
fn compile_incremental(step: &str, loaded: bool, extra: &[&str]) -> Vec<u8> {
    let mut compiler = cmd(trustc());
    compiler
        .arg("lib.rs")
        .args([
            "--crate-type=rlib",
            "--crate-name=platform_adv_incr",
            "--edition=2021",
            "--emit=link,obj",
            "-Copt-level=0",
            "-Ccodegen-units=1",
            "-Cdebuginfo=0",
            "-Ztrust-verify=off",
            "-Cincremental=incr-cache",
            "--out-dir",
            "incr-out",
        ])
        .arg(format!("-Zassert-incr-state={}", if loaded { "loaded" } else { "not-loaded" }))
        .args(extra)
        .context(step);
    compiler.run();
    rfs::read(Path::new("incr-out").join("platform_adv_incr.o"))
}

fn part2_incremental_tracking_is_by_value() {
    const FD: &str = "-Ztrust-platform-properties=fd-inherit";
    // (step, the session must be loaded, flags). Each step is compared with the step before it.
    let steps: &[(&str, bool, &[&str])] = &[
        ("cold", false, &[]),
        // CONTROL: an unchanged command line reuses the session at all.
        ("control: unchanged", true, &[]),
        ("properties set", false, &[FD]),
        ("property listed twice", true, &["-Ztrust-platform-properties=fd-inherit,fd-inherit"]),
        ("option given twice", true, &[FD, FD]),
        (
            "explicit defaults",
            true,
            &[
                FD,
                "-Ztrust-platform-unanalysed=warn",
                "-Ztrust-platform-budget=1000000",
                "-Ztrust-platform-report=summary",
            ],
        ),
        ("budget with a leading zero", true, &[FD, "-Ztrust-platform-budget=01000000"]),
        ("unanalysed=deny", false, &[FD, "-Ztrust-platform-unanalysed=deny"]),
        // A later `warn` wins over an earlier `deny` (rustc's last-wins), so this is the
        // default again and must not reuse the deny session.
        (
            "deny then warn",
            false,
            &[FD, "-Ztrust-platform-unanalysed=deny", "-Ztrust-platform-unanalysed=warn"],
        ),
        ("budget=1", false, &[FD, "-Ztrust-platform-budget=1"]),
        ("report=verbose", false, &[FD, "-Ztrust-platform-report=verbose"]),
        ("dump-facts", false, &[FD, "-Ztrust-platform-dump-facts=incr.facts"]),
        ("properties removed", false, &[]),
    ];
    let mut first_object: Option<Vec<u8>> = None;
    for (step, loaded, flags) in steps {
        let object = compile_incremental(step, *loaded, flags);
        match &first_object {
            None => first_object = Some(object),
            Some(first) => assert!(
                *first == object,
                "step `{step}`: the object differs from the cold compile's (the control step \
                 shows whether incremental output is deterministic at all)",
            ),
        }
    }
    assert!(!Path::new("incr.facts").exists(), "L1a: the facts sink was written");
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }
    part1_every_output_is_byte_identical();
    part2_incremental_tracking_is_by_value();
}
