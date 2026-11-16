#![cfg(any(target_os = "linux", target_os = "macos"))]

//! Successful native output receipts require this attempt's compiler reports.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const PROXY: &str = r###"
use std::io::Write;
use std::process::{Command, Stdio};
fn forward(bytes: &[u8], stderr: bool) {
    if stderr { std::io::stderr().write_all(bytes).unwrap(); }
    else { std::io::stdout().write_all(bytes).unwrap(); }
}
fn main() {
    let mut args = std::env::args_os().skip(1);
    let compiler = args.next().unwrap();
    let mut args: Vec<_> = args.collect();
    let name = args.windows(2).find(|pair| pair[0] == "--crate-name")
        .and_then(|pair| pair[1].to_str());
    let actual = name == Some("observed_output") && !args.iter().any(|word|
        word == "-vV" || word.to_string_lossy().starts_with("--print"));
    if !actual {
        let status = Command::new(compiler).args(args)
            .env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS")
            .env_remove("CARGO_JOBSERVER_HANDOFF").status().unwrap();
        std::process::exit(status.code().unwrap_or(101));
    }
    let control = std::path::PathBuf::from(std::env::var_os("OUTPUT_CONTROL").unwrap());
    let mode = std::env::var("OUTPUT_MODE").unwrap();
    let encoded = |args: &[std::ffi::OsString]| {
        let mut bytes = Vec::new();
        for arg in args { bytes.extend_from_slice(arg.as_encoded_bytes()); bytes.push(0); }
        bytes
    };
    std::fs::write(control.join("argv.before"), encoded(&args)).unwrap();
    if mode == "redirect" {
        let path = std::env::var_os("OUTPUT_REDIRECT").unwrap();
        let path = std::path::Path::new(&path).to_str().unwrap();
        args.push(format!("--emit=metadata={path}").into());
    }
    std::fs::write(control.join("argv.after"), encoded(&args)).unwrap();
    let result = Command::new(compiler).args(args)
        .env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS")
        .env_remove("CARGO_JOBSERVER_HANDOFF").stdout(Stdio::piped()).stderr(Stdio::piped())
        .output().unwrap();
    std::fs::write(control.join("raw.stdout"), &result.stdout).unwrap();
    std::fs::write(control.join("raw.stderr"), &result.stderr).unwrap();
    std::fs::write(control.join("status"), result.status.code().unwrap_or(101).to_string()).unwrap();
    if !result.status.success() {
        forward(&result.stdout, false); forward(&result.stderr, true);
        std::process::exit(result.status.code().unwrap_or(101));
    }
    let text = String::from_utf8(result.stderr.clone()).unwrap();
    let prefix = "{\"$message_type\":\"artifact\",\"artifact\":\"";
    let suffix = "\",\"emit\":\"metadata\"}";
    let mut sent = Vec::new();
    for line in text.lines() {
        let metadata = line.starts_with(prefix) && line.ends_with(suffix);
        if mode != "suppress" || !metadata {
            sent.extend_from_slice(line.as_bytes()); sent.push(b'\n');
        }
    }
    assert!(matches!(mode.as_str(), "exact" | "suppress" | "redirect"));
    std::fs::write(control.join("sent.stderr"), &sent).unwrap();
    forward(&result.stdout, false); forward(&sent, true);
}
"###;

const LABELS: &[&str] = &[
    "proxy", "cold", "warm", "changed", "repeat", "repaired", "rewarm",
];

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture selects the caller's genuine compiler and PATH without project configuration"
)]
fn command(root: &Path, world: &Path, mode: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit native fixture compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching fixture rustdoc"),
        )
        .args([
            "--unverified",
            mode,
            "--offline",
            "-j1",
            "--message-format=json",
        ]);
    if root.join("Cargo.lock").is_file() {
        command.arg("--locked");
    }
    command
}

fn artifacts(bytes: &[u8]) -> Vec<serde_json::Value> {
    String::from_utf8(bytes.to_vec())
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect()
}

struct Fixture {
    world: PathBuf,
    project: PathBuf,
    proxy: PathBuf,
    redirect: PathBuf,
}

impl Fixture {
    fn new(name: &str) -> Self {
        Self::with_incremental(name, false)
    }

    fn with_incremental(name: &str, incremental: bool) -> Self {
        let base = std::env::current_dir()
            .unwrap()
            .join(".ubd/native-output-observation.noindex");
        fs::create_dir_all(&base).unwrap();
        let world = tempfile::Builder::new()
            .prefix(name)
            .tempdir_in(base)
            .unwrap()
            .keep();
        for label in LABELS {
            let control = world.join("control").join(label);
            fs::create_dir_all(&control).unwrap();
            for name in [
                "raw.stdout",
                "raw.stderr",
                "status",
                "argv.before",
                "argv.after",
                "sent.stderr",
            ] {
                fs::write(control.join(name), []).unwrap();
            }
            for suffix in ["stdout", "stderr", "status", "command.json"] {
                fs::write(world.join(format!("{label}.{suffix}")), []).unwrap();
            }
        }
        for name in [
            "observed.json",
            "default.before.rmeta",
            "default.after.rmeta",
            "redirect.after.rmeta",
        ] {
            fs::write(world.join(name), []).unwrap();
        }
        let proxy_root = world.join("proxy");
        fs::create_dir_all(proxy_root.join("src")).unwrap();
        fs::write(proxy_root.join("Cargo.toml"), "[package]\nname='output_proxy'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
        fs::write(proxy_root.join("src/main.rs"), PROXY).unwrap();
        let output = command(&proxy_root, &world, "build").output().unwrap();
        record(&world, "proxy", &output);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let proxy = artifacts(&output.stdout)
            .into_iter()
            .find(|row| row["target"]["name"] == "output_proxy")
            .and_then(|row| row["executable"].as_str().map(PathBuf::from))
            .unwrap();
        let project = world.join("project");
        fs::create_dir_all(project.join("src")).unwrap();
        fs::create_dir_all(project.join(".cargo")).unwrap();
        fs::write(project.join("Cargo.toml"), format!("[package]\nname='observed_output'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental={incremental}\n")).unwrap();
        fs::write(project.join("src/lib.rs"), "pub fn value() -> u32 { 9 }\n").unwrap();
        fs::write(
            project.join(".cargo/config.toml"),
            format!(
                "[build]\nrustflags={}\n",
                serde_json::to_string(&[format!(
                    "--remap-path-prefix={}=/fixture",
                    project.display()
                )])
                .unwrap()
            ),
        )
        .unwrap();
        let redirect = world.join("target/redirect/chosen.rmeta");
        fs::create_dir_all(redirect.parent().unwrap()).unwrap();
        fs::write(&redirect, []).unwrap();
        Self {
            world,
            project,
            proxy,
            redirect,
        }
    }

    fn execute(&self, label: &str, mode: &str, behavior: &str) -> std::process::Output {
        let mut command = command(&self.project, &self.world, mode);
        command
            .arg("--lib")
            .env("RUSTC_WRAPPER", &self.proxy)
            .env("OUTPUT_CONTROL", self.world.join("control").join(label))
            .env("OUTPUT_MODE", behavior)
            .env("OUTPUT_REDIRECT", &self.redirect);
        fs::write(
            self.world.join(format!("{label}.command.json")),
            serde_json::to_vec(&serde_json::json!({
                "targo": command.get_program().to_string_lossy(),
                "args": command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
                "wrapper": self.proxy, "mode": behavior, "redirect": self.redirect,
            }))
            .unwrap(),
        )
        .unwrap();
        let output = command.output().unwrap();
        record(&self.world, label, &output);
        output
    }

    fn run(&self, label: &str, mode: &str, behavior: &str) -> serde_json::Value {
        let output = self.execute(label, mode, behavior);
        assert!(
            output.status.success(),
            "world={}\n{}",
            self.world.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        let rows = artifacts(&output.stdout);
        assert_eq!(rows.len(), 1, "{rows:?}");
        assert_eq!(rows[0]["target"]["name"], "observed_output");
        rows.into_iter().next().unwrap()
    }

    fn reports(&self, label: &str, sent: bool) -> Vec<serde_json::Value> {
        assert_eq!(
            fs::read_to_string(self.world.join("control").join(label).join("status")).unwrap(),
            "0"
        );
        let file = if sent { "sent.stderr" } else { "raw.stderr" };
        String::from_utf8(fs::read(self.world.join("control").join(label).join(file)).unwrap())
            .unwrap()
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .filter(|row| row["$message_type"] == "artifact")
            .collect()
    }

    fn receipt(&self) -> Option<PathBuf> {
        let paths: Vec<_> = walkdir::WalkDir::new(self.world.join("target"))
            .into_iter()
            .map(Result::unwrap)
            .filter(|entry| entry.file_name() == "outputs-lib-observed_output.json")
            .map(|entry| entry.into_path())
            .collect();
        assert!(paths.len() <= 1, "{paths:?}");
        paths.into_iter().next()
    }

    fn save(&self, observed: &serde_json::Value) {
        fs::write(
            self.world.join("observed.json"),
            serde_json::to_vec_pretty(observed).unwrap(),
        )
        .unwrap();
    }
}

fn record(world: &Path, label: &str, output: &std::process::Output) {
    fs::write(world.join(format!("{label}.stdout")), &output.stdout).unwrap();
    fs::write(world.join(format!("{label}.stderr")), &output.stderr).unwrap();
    fs::write(
        world.join(format!("{label}.status")),
        output.status.to_string(),
    )
    .unwrap();
}

fn file(row: &serde_json::Value, suffix: &str) -> PathBuf {
    row["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|v| v.as_str())
        .find(|name| name.ends_with(suffix))
        .map(PathBuf::from)
        .unwrap()
}

fn metadata_report(reports: &[serde_json::Value]) -> PathBuf {
    let metadata: Vec<_> = reports
        .iter()
        .filter(|row| row["emit"] == "metadata")
        .collect();
    assert_eq!(metadata.len(), 1, "{reports:?}");
    let path = PathBuf::from(metadata[0]["artifact"].as_str().unwrap());
    assert!(path.is_absolute() && path.is_file(), "{reports:?}");
    path
}

#[test]
fn missing_check_metadata_report_keeps_successful_compilation_uncacheable() {
    let fixture = Fixture::new("missing");
    let cold = fixture.run("cold", "check", "suppress");
    assert_eq!(cold["fresh"], false);
    assert_eq!(
        metadata_report(&fixture.reports("cold", false)),
        file(&cold, ".rmeta")
    );
    assert!(
        fixture
            .reports("cold", true)
            .iter()
            .all(|row| row["emit"] != "metadata")
    );
    let receipt = fixture.receipt();
    let repeat = fixture.run("repeat", "check", "suppress");
    let after_repeat = fixture.receipt();
    let observed = serde_json::json!({"cold":cold,"repeat":repeat,"receipt_before_repeat":receipt,"receipt_after_repeat":after_repeat});
    fixture.save(&observed);
    assert!(
        after_repeat.is_none(),
        "missing live metadata report cannot publish receipt: {observed}"
    );
    assert_eq!(
        repeat["fresh"], false,
        "missing live report must remain dirty: {observed}"
    );
    metadata_report(&fixture.reports("repeat", false));
}

#[test]
fn hidden_wrapper_redirect_cannot_bless_surviving_check_metadata() {
    let fixture = Fixture::new("redirect");
    let first = fixture.run("cold", "check", "exact");
    assert_eq!(first["fresh"], false);
    let metadata = file(&first, ".rmeta");
    assert_eq!(metadata_report(&fixture.reports("cold", false)), metadata);
    assert!(fixture.receipt().is_some());
    let original = fs::read(&metadata).unwrap();
    fs::write(fixture.world.join("default.before.rmeta"), &original).unwrap();
    assert_eq!(fixture.run("warm", "check", "exact")["fresh"], true);
    fs::write(
        fixture.project.join("src/lib.rs"),
        "pub fn value() -> u64 { 9 }\n",
    )
    .unwrap();
    let changed = fixture.run("changed", "check", "redirect");
    assert_eq!(changed["fresh"], false);
    assert_eq!(changed["filenames"], first["filenames"]);
    let before = fs::read(fixture.world.join("control/cold/argv.before")).unwrap();
    let original_args = fs::read(fixture.world.join("control/changed/argv.before")).unwrap();
    assert_eq!(
        before, original_args,
        "only the wrapper changes actual child routing"
    );
    let mut redirected_args = original_args;
    redirected_args
        .extend_from_slice(format!("--emit=metadata={}\0", fixture.redirect.display()).as_bytes());
    assert_eq!(
        fs::read(fixture.world.join("control/changed/argv.after")).unwrap(),
        redirected_args
    );
    assert_eq!(
        metadata_report(&fixture.reports("changed", false)),
        fixture.redirect
    );
    let default_after = fs::read(&metadata).unwrap();
    let redirected = fs::read(&fixture.redirect).unwrap();
    fs::write(fixture.world.join("default.after.rmeta"), &default_after).unwrap();
    fs::write(fixture.world.join("redirect.after.rmeta"), &redirected).unwrap();
    assert_eq!(default_after, original);
    assert_ne!(redirected, original);
    let receipt = fixture.receipt();
    let repeat = fixture.run("repeat", "check", "redirect");
    let after_repeat = fixture.receipt();
    let observed = serde_json::json!({"first":first,"changed":changed,"repeat":repeat,
        "receipt_before_repeat":receipt,"receipt_after_repeat":after_repeat,
        "default_unchanged":default_after==original,"redirect_different":redirected!=original});
    fixture.save(&observed);
    assert!(
        after_repeat.is_none(),
        "hidden redirected report cannot bless default metadata: {observed}"
    );
    assert_eq!(
        repeat["fresh"], false,
        "hidden redirected output must remain dirty: {observed}"
    );
    metadata_report(&fixture.reports("repeat", false));
}

#[test]
fn exact_build_link_report_reuses_warm_outputs_and_repairs_corrupt_bytes() {
    let fixture = Fixture::new("exact");
    let cold = fixture.run("cold", "build", "exact");
    assert_eq!(cold["fresh"], false);
    // Cargo also exposes a target-primary alias. The real compiler reports
    // the unit-owned archive beside its unit-owned metadata output instead.
    let primary = file(&cold, ".rlib");
    let archive = file(&cold, ".rmeta").with_extension("rlib");
    assert!(
        fixture
            .reports("cold", false)
            .iter()
            .any(|row| row["emit"] == "link" && row["artifact"] == archive.to_str().unwrap())
    );
    assert_eq!(fs::read(primary).unwrap(), fs::read(&archive).unwrap());
    assert!(fixture.receipt().is_some());
    assert_eq!(fixture.run("warm", "build", "exact")["fresh"], true);
    let mut damaged = fs::read(&archive).unwrap();
    let time = filetime::FileTime::from_last_modification_time(&fs::metadata(&archive).unwrap());
    damaged[..8].copy_from_slice(b"BROKEN!!");
    fs::write(&archive, &damaged).unwrap();
    filetime::set_file_mtime(&archive, time).unwrap();
    let repaired = fixture.run("repaired", "build", "exact");
    assert_eq!(repaired["fresh"], false);
    assert!(fs::read(&archive).unwrap().starts_with(b"!<arch>\n"));
    assert!(fixture.receipt().is_some());
    let warm = fixture.run("rewarm", "build", "exact");
    assert_eq!(warm["fresh"], true);
    fixture.save(&serde_json::json!({"cold":cold,"repaired":repaired,"warm":warm}));
}

#[test]
fn exact_incremental_check_reports_source_edits_and_reuses_warm_metadata() {
    let fixture = Fixture::with_incremental("incremental", true);
    let cold = fixture.run("cold", "check", "exact");
    assert_eq!(cold["fresh"], false);
    let metadata = file(&cold, ".rmeta");
    assert_eq!(metadata_report(&fixture.reports("cold", false)), metadata);
    assert!(fixture.receipt().is_some());
    let original = fs::read(&metadata).unwrap();
    assert_eq!(fixture.run("warm", "check", "exact")["fresh"], true);
    fs::write(
        fixture.project.join("src/lib.rs"),
        "pub fn value() -> u64 { 9 }\n",
    )
    .unwrap();
    let changed = fixture.run("changed", "check", "exact");
    assert_eq!(changed["fresh"], false);
    assert_eq!(changed["filenames"], cold["filenames"]);
    assert_eq!(
        metadata_report(&fixture.reports("changed", false)),
        metadata
    );
    assert_ne!(fs::read(&metadata).unwrap(), original);
    assert!(fixture.receipt().is_some());
    let warm = fixture.run("rewarm", "check", "exact");
    assert_eq!(warm["fresh"], true);
    fixture.save(&serde_json::json!({"cold":cold,"changed":changed,"warm":warm}));
}

#[test]
fn dirty_incremental_check_with_unchanged_inputs_reports_current_metadata() {
    let fixture = Fixture::with_incremental("unchanged", true);
    let cold = fixture.run("cold", "check", "exact");
    assert_eq!(cold["fresh"], false);
    let metadata = file(&cold, ".rmeta");
    assert_eq!(metadata_report(&fixture.reports("cold", false)), metadata);
    assert_eq!(fixture.run("warm", "check", "exact")["fresh"], true);

    let source_before = fs::read(fixture.project.join("src/lib.rs")).unwrap();
    let metadata_before = fs::read(&metadata).unwrap();
    let argv_before = fs::read(fixture.world.join("control/cold/argv.before")).unwrap();
    fs::write(fixture.world.join("default.before.rmeta"), &metadata_before).unwrap();
    let receipt_path = fixture.receipt().expect("honest warm receipt");
    let receipt_before = fs::read(&receipt_path).unwrap();
    // Native fingerprint_file_path uses the same ordinary target name, with
    // `outputs-` and `.json` added only for the output receipt.
    let ordinary_name = receipt_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .strip_prefix("outputs-")
        .unwrap()
        .strip_suffix(".json")
        .unwrap();
    let short = receipt_path.parent().unwrap().join(ordinary_name);
    assert!(fs::symlink_metadata(&short).unwrap().file_type().is_file());
    let short_before = fs::read(&short).unwrap();
    assert!(!short_before.is_empty());
    let detailed = short.with_extension("json");
    let detailed_before = fs::read(&detailed).unwrap();

    // Lose only the small Cargo freshness record. Keep the receipt, actual
    // outputs and incremental compiler cache, then use the identical command.
    fs::remove_file(&short).unwrap();
    assert!(!short.exists());
    assert_eq!(fs::read(&receipt_path).unwrap(), receipt_before);
    assert_eq!(fs::read(&detailed).unwrap(), detailed_before);
    assert_eq!(fs::read(&metadata).unwrap(), metadata_before);
    assert_eq!(
        fs::read(fixture.project.join("src/lib.rs")).unwrap(),
        source_before
    );

    let dirty = fixture.run("changed", "check", "exact");
    let reports = fixture.reports("changed", false); // requires actual child exit 0
    let source_after = fs::read(fixture.project.join("src/lib.rs")).unwrap();
    let argv_after = fs::read(fixture.world.join("control/changed/argv.before")).unwrap();
    let actual_argv = fs::read(fixture.world.join("control/changed/argv.after")).unwrap();
    let metadata_after = fs::read(&metadata).unwrap();
    fs::write(fixture.world.join("default.after.rmeta"), &metadata_after).unwrap();
    let receipt_after_dirty = fixture.receipt();
    let warm = fixture.run("rewarm", "check", "exact");
    let observed = serde_json::json!({"cold":cold,"dirty":dirty,"warm":warm,
        "short_fingerprint":short,"removed_short_bytes":short_before,
        "source_before":source_before,"source_after":source_after,
        "argv_unchanged":argv_before==argv_after,"actual_argv_unchanged":argv_after==actual_argv,
        "metadata_bytes_equal":metadata_before==metadata_after,
        "current_reports":reports,"receipt_after_dirty":receipt_after_dirty});
    fixture.save(&observed);

    assert_eq!(dirty["fresh"], false, "{observed}");
    assert_eq!(dirty["filenames"], cold["filenames"], "{observed}");
    assert_eq!(source_after, source_before, "{observed}");
    assert_eq!(argv_after, argv_before, "{observed}");
    assert_eq!(actual_argv, argv_before, "{observed}");
    assert_eq!(metadata_report(&reports), metadata, "{observed}");
    assert!(receipt_after_dirty.is_some(), "{observed}");
    assert_eq!(warm["fresh"], true, "{observed}");
}

#[test]
fn constant_build_script_trigger_preserves_honest_incremental_check_reuse() {
    let fixture = Fixture::with_incremental("buildscript", true);
    // Instrument execution outside the package and OUT_DIR. The script's
    // actual Cargo output stays constant, and the library never reads this log.
    let runs = fixture.world.join("control/script-runs");
    fs::write(&runs, []).unwrap();
    let script = format!(
        r#"
use std::io::Write;
fn main() {{
    std::fs::OpenOptions::new().append(true).open({:?}).unwrap()
        .write_all(b"ran\n").unwrap();
    println!("cargo:rerun-if-changed=trigger");
}}
"#,
        runs.to_str().unwrap()
    );
    fs::write(fixture.project.join("build.rs"), &script).unwrap();
    fs::write(fixture.project.join("trigger"), b"one\n").unwrap();
    let source_before = fs::read(fixture.project.join("src/lib.rs")).unwrap();
    let script_before = fs::read(fixture.project.join("build.rs")).unwrap();

    let run = |label| {
        let output = fixture.execute(label, "check", "exact");
        assert!(
            output.status.success(),
            "world={}\n{}",
            fixture.world.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        let all = artifacts(&output.stdout);
        let libraries: Vec<_> = all
            .iter()
            .filter(|row| row["target"]["name"] == "observed_output")
            .collect();
        assert_eq!(libraries.len(), 1, "{all:?}");
        let scripts: Vec<_> = String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .filter(|row| row["reason"] == "build-script-executed")
            .collect();
        assert_eq!(scripts.len(), 1, "{scripts:?}");
        ((*libraries[0]).clone(), scripts[0].clone(), all)
    };
    let semantic_output = |row: &serde_json::Value| {
        let fields = ["linked_libs", "linked_paths", "cfgs", "env", "out_dir"];
        serde_json::Value::Object(
            fields
                .into_iter()
                .map(|key| {
                    (
                        key.to_owned(),
                        row.get(key)
                            .expect("build-script semantic output field")
                            .clone(),
                    )
                })
                .collect(),
        )
    };
    let (cold, cold_script, cold_all) = run("cold");
    let after_cold = fs::read(&runs).unwrap();
    let metadata = file(&cold, ".rmeta");
    let metadata_before = fs::read(&metadata).unwrap();
    let cold_argv = fs::read(fixture.world.join("control/cold/argv.before")).unwrap();
    let receipt_before = fixture.receipt().expect("honest initial library receipt");
    let receipt_before_bytes = fs::read(&receipt_before).unwrap();

    // Locate the actual cached stdout by its associated root-output record,
    // supporting both maintained BuildScriptRunFiles layouts.
    let out_dir = cold_script["out_dir"].as_str().unwrap();
    let roots: Vec<_> = walkdir::WalkDir::new(fixture.world.join("target"))
        .into_iter()
        .map(Result::unwrap)
        .filter(|entry| entry.file_name() == "root-output" && entry.file_type().is_file())
        .filter(|entry| fs::read(entry.path()).unwrap() == out_dir.as_bytes())
        .map(|entry| entry.path().parent().unwrap().to_path_buf())
        .collect();
    assert_eq!(roots.len(), 1, "{roots:?}");
    let stdout_paths: Vec<_> = [roots[0].join("output"), roots[0].join("stdout")]
        .into_iter()
        .filter(|path| path.is_file())
        .collect();
    assert_eq!(stdout_paths.len(), 1, "{stdout_paths:?}");
    let script_stdout_before = fs::read(&stdout_paths[0]).unwrap();

    let (warm, warm_script, warm_all) = run("warm");
    let after_warm = fs::read(&runs).unwrap();
    // This is the sole input edit. Do not delete any freshness/output record
    // or change compiler flags to manufacture a dirty library job.
    fs::write(fixture.project.join("trigger"), b"two\n").unwrap();
    let (changed, changed_script, changed_all) = run("changed");
    let after_trigger = fs::read(&runs).unwrap();
    let library_dirty = changed["fresh"] == false;
    let child_status = fs::read_to_string(fixture.world.join("control/changed/status")).unwrap();
    let changed_argv = fs::read(fixture.world.join("control/changed/argv.before")).unwrap();
    let actual_argv = fs::read(fixture.world.join("control/changed/argv.after")).unwrap();
    let reports = if library_dirty {
        fixture.reports("changed", false)
    } else {
        Vec::new()
    };
    let receipt_after = fixture.receipt();
    let receipt_after_bytes = receipt_after.as_ref().map(|path| fs::read(path).unwrap());
    let script_stdout_after = fs::read(&stdout_paths[0]).unwrap();
    let source_after = fs::read(fixture.project.join("src/lib.rs")).unwrap();
    let script_after = fs::read(fixture.project.join("build.rs")).unwrap();
    let metadata_after = fs::read(&metadata).unwrap();
    let (rewarm, rewarm_script, rewarm_all) = run("rewarm");
    let after_rewarm = fs::read(&runs).unwrap();
    let observed = serde_json::json!({"cold":cold,"warm":warm,"changed":changed,"rewarm":rewarm,
        "cold_all":cold_all,"warm_all":warm_all,"changed_all":changed_all,"rewarm_all":rewarm_all,
        "cold_script":cold_script,"warm_script":warm_script,"changed_script":changed_script,"rewarm_script":rewarm_script,
        "execution_log_after_cold":after_cold,"execution_log_after_warm":after_warm,
        "execution_log_after_trigger":after_trigger,"execution_log_after_rewarm":after_rewarm,
        "script_stdout_before":script_stdout_before,"script_stdout_after":script_stdout_after,
        "source_before":source_before,"source_after":source_after,"script_source_unchanged":script_before==script_after,
        "library_dirty":library_dirty,"library_child_status":child_status,
        "compiler_argv_unchanged":library_dirty.then_some(cold_argv==changed_argv),
        "actual_argv_unchanged":library_dirty.then_some(changed_argv==actual_argv),
        "current_reports":reports,"receipt_after_trigger":receipt_after,
        "receipt_bytes_changed":receipt_after_bytes.as_ref().map(|bytes| bytes!=&receipt_before_bytes),
        "metadata_bytes_equal":metadata_before==metadata_after});
    fixture.save(&observed);

    assert_eq!(after_cold, b"ran\n", "{observed}");
    assert_eq!(after_warm, after_cold, "{observed}");
    assert_eq!(after_trigger, b"ran\nran\n", "{observed}");
    assert_eq!(after_rewarm, after_trigger, "{observed}");
    assert_eq!(
        script_stdout_before, b"cargo:rerun-if-changed=trigger\n",
        "{observed}"
    );
    assert_eq!(script_stdout_after, script_stdout_before, "{observed}");
    for row in [&warm_script, &changed_script, &rewarm_script] {
        assert_eq!(
            semantic_output(row),
            semantic_output(&cold_script),
            "{observed}"
        );
    }
    assert_eq!(source_after, source_before, "{observed}");
    assert_eq!(script_after, script_before, "{observed}");
    assert!(
        warm_all.iter().all(|row| row["fresh"] == true),
        "{observed}"
    );
    assert!(
        rewarm_all.iter().all(|row| row["fresh"] == true),
        "{observed}"
    );
    assert!(
        changed_all
            .iter()
            .filter(|row| row["target"]["name"] != "observed_output")
            .all(|row| row["fresh"] == true),
        "script compilation must not retrigger: {observed}"
    );
    if library_dirty {
        assert_eq!(child_status, "0", "{observed}");
        assert_eq!(changed_argv, cold_argv, "{observed}");
        assert_eq!(actual_argv, cold_argv, "{observed}");
        assert_eq!(metadata_report(&reports), metadata, "{observed}");
        assert!(receipt_after.is_some(), "{observed}");
    } else {
        assert_eq!(changed["fresh"], true, "{observed}");
        assert!(
            child_status.is_empty() && changed_argv.is_empty() && actual_argv.is_empty(),
            "{observed}"
        );
        assert_eq!(
            receipt_after_bytes.as_ref(),
            Some(&receipt_before_bytes),
            "{observed}"
        );
    }
}

#[test]
fn failed_dirty_check_removes_prior_receipt_before_honest_retry() {
    let fixture = Fixture::new("retry");
    let cold = fixture.run("cold", "check", "exact");
    assert_eq!(cold["fresh"], false);
    metadata_report(&fixture.reports("cold", false));
    assert!(fixture.receipt().is_some());
    assert_eq!(fixture.run("warm", "check", "exact")["fresh"], true);
    fs::write(
        fixture.project.join("src/lib.rs"),
        "pub fn value() -> u32 { missing_name }\n",
    )
    .unwrap();
    let failure = fixture.execute("changed", "check", "exact");
    assert!(!failure.status.success());
    let control = fixture.world.join("control/changed");
    let child_status = fs::read_to_string(control.join("status")).unwrap();
    assert_eq!(child_status, "1");
    let raw = fs::read(control.join("raw.stderr")).unwrap();
    assert!(
        String::from_utf8(raw)
            .unwrap()
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .any(|row| row["level"] == "error" && row["code"]["code"] == "E0425")
    );
    let failed_receipt = fixture.receipt();
    fs::write(
        fixture.project.join("src/lib.rs"),
        "pub fn value() -> u64 { 9 }\n",
    )
    .unwrap();
    let repaired = fixture.run("repaired", "check", "exact");
    assert_eq!(repaired["fresh"], false);
    metadata_report(&fixture.reports("repaired", false));
    assert!(fixture.receipt().is_some());
    let warm = fixture.run("rewarm", "check", "exact");
    assert_eq!(warm["fresh"], true);
    let observed = serde_json::json!({"cold":cold,"failed_targo_status":failure.status.code(),
        "failed_child_status":child_status,"receipt_after_failure":failed_receipt,
        "repaired":repaired,"warm":warm});
    fixture.save(&observed);
    assert!(
        failed_receipt.is_none(),
        "failed actual work must retire its old receipt: {observed}"
    );
}
