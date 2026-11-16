//! Real native cache acceptance, with an unchanged dependency's bytes damaged.

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture needs the caller's actual PATH and explicitly selected compiler tools, without project configuration"
)]
fn compile_with_args(
    root: &Path,
    mode: &str,
    options: &[&str],
    compiler_args: &[String],
) -> Vec<serde_json::Value> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit test compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching test rustdoc"),
        )
        .current_dir(root)
        .args([
            "--unverified",
            mode,
            "--offline",
            "-j1",
            "--message-format=json",
        ])
        .args(options);
    if root.join("Cargo.lock").is_file() {
        command.arg("--locked");
    }
    if !compiler_args.is_empty() {
        command.arg("--").args(compiler_args);
    }
    let result = command.output().expect("run native Targo");
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    String::from_utf8(result.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect()
}

fn compile(root: &Path, mode: &str) -> Vec<serde_json::Value> {
    compile_with_args(root, mode, &[], &[])
}

fn build(root: &Path) -> Vec<serde_json::Value> {
    compile(root, "build")
}

fn dependency(rows: &[serde_json::Value]) -> &serde_json::Value {
    rows.iter()
        .find(|row| row["target"]["name"] == "dep")
        .expect("dependency artifact")
}

fn dependency_archive(row: &serde_json::Value) -> PathBuf {
    row["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|path| path.as_str())
        .find(|path| path.ends_with(".rlib"))
        .map(PathBuf::from)
        .expect("dependency archive")
}

fn read_json(path: &Path) -> serde_json::Value {
    serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
}

/// Trust: one native fixture, kept under a test-owned directory of this
/// checkout rather than a world-writable /tmp target, inside the `.ubd/`
/// retention area that `src/tools/targo/.gitignore` ignores, so it is never an
/// untracked directory of the source tree. A passing test removes it; a failing
/// one keeps it at its original input path and prints where
/// (TARGO-TEST-TMP-HYGIENE-1; `tests/fixture_retention.rs` guards the rule).
struct Fixture(Option<tempfile::TempDir>);

impl Fixture {
    fn new() -> Self {
        let base = std::env::current_dir()
            .unwrap()
            .join(".ubd/native-output-integrity.noindex");
        fs::create_dir_all(&base).unwrap();
        Self(Some(tempfile::tempdir_in(base).unwrap()))
    }

    fn path(&self) -> &Path {
        self.0.as_ref().unwrap().path()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let Some(fixture) = self.0.take() else {
            return;
        };
        if std::thread::panicking() {
            eprintln!(
                "kept failed output-integrity fixture: {}",
                fixture.keep().display()
            );
        } else {
            let path = fixture.path().to_path_buf();
            fixture.close().unwrap_or_else(|error| {
                panic!("remove passed fixture {}: {error}", path.display())
            });
        }
    }
}

#[test]
fn split_output_file_cannot_bless_surviving_check_metadata() {
    assert_output_file_check_is_uncacheable(OutputFileArgument::Split);
}

#[test]
fn attached_output_file_cannot_bless_surviving_check_metadata() {
    assert_output_file_check_is_uncacheable(OutputFileArgument::Attached);
}

#[test]
fn clustered_split_output_file_cannot_bless_surviving_check_metadata() {
    assert_output_file_check_is_uncacheable(OutputFileArgument::ClusteredSplit);
}

#[test]
fn clustered_attached_output_file_cannot_bless_surviving_check_metadata() {
    assert_output_file_check_is_uncacheable(OutputFileArgument::ClusteredAttached);
}

#[derive(Clone, Copy, Debug)]
enum OutputFileArgument {
    Split,
    Attached,
    ClusteredSplit,
    ClusteredAttached,
}

fn assert_output_file_check_is_uncacheable(spelling: OutputFileArgument) {
    let fixture = Fixture::new();
    let root = fixture.path();
    fs::create_dir_all(root.join("src")).unwrap();
    let redirect = root.join("target/redirect");
    fs::create_dir_all(&redirect).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='output_routed'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[lints.rust]\nunexpected_cfgs={level='warn',check-cfg=['cfg(changed)']}\n",
    )
    .unwrap();
    let source = b"#[cfg(not(changed))] pub fn value() -> u32 { 9 }\n#[cfg(changed)] pub fn value() -> u64 { 9 }\n";
    fs::write(root.join("src/lib.rs"), source).unwrap();
    let remap = format!("--remap-path-prefix={}=/fixture", root.display());
    let options = ["--lib", "--profile", "check"];
    let first = compile_with_args(&root, "rustc", &options, std::slice::from_ref(&remap));
    assert_eq!(first.len(), 1, "fixture: {}", root.display());
    assert_eq!(first[0]["fresh"], false);
    let metadata = first[0]["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|path| path.as_str())
        .find(|path| path.ends_with(".rmeta"))
        .map(PathBuf::from)
        .expect("default metadata output");
    let original = fs::read(&metadata).unwrap();
    assert_eq!(
        compile_with_args(&root, "rustc", &options, std::slice::from_ref(&remap))[0]["fresh"],
        true
    );
    let mut args = vec![remap, "--cfg=changed".into()];
    let chosen = redirect.join("chosen.rmeta");
    match spelling {
        OutputFileArgument::Split => args.extend(["-o".into(), chosen.to_str().unwrap().into()]),
        OutputFileArgument::Attached => args.push(format!("-o{}", chosen.display())),
        OutputFileArgument::ClusteredSplit => {
            args.extend(["-go".into(), chosen.to_str().unwrap().into()])
        }
        OutputFileArgument::ClusteredAttached => args.push(format!("-go{}", chosen.display())),
    }
    let custom = compile_with_args(&root, "rustc", &options, &args);
    assert_eq!(custom[0]["fresh"], false);
    assert_eq!(
        custom[0]["filenames"], first[0]["filenames"],
        "Cargo's reported output inventory must still be the old default layout"
    );
    assert_eq!(fs::read(root.join("src/lib.rs")).unwrap(), source);
    assert_eq!(fs::read(&metadata).unwrap(), original);
    // Multiple requested output types adapt -o's basename. Inspect the real
    // metadata in its directory, rather than assuming the chosen leaf exists.
    let redirected: Vec<_> = walkdir::WalkDir::new(&redirect)
        .into_iter()
        .map(Result::unwrap)
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "rmeta"))
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(redirected.len(), 1, "fixture: {}", root.display());
    assert_ne!(fs::read(&redirected[0]).unwrap(), original);
    assert_eq!(
        compile_with_args(&root, "rustc", &options, &args)[0]["fresh"],
        false,
        "caller -o must not bless an old default output; spelling={spelling:?}, fixture: {}",
        root.display()
    );
    assert!(
        !walkdir::WalkDir::new(root.join("target"))
            .into_iter()
            .map(Result::unwrap)
            .any(|entry| entry.file_name() == OsString::from("outputs-lib-output_routed.json")),
        "caller -o cannot publish a receipt for the surviving default output"
    );
}

#[test]
fn redirected_check_metadata_cannot_bless_surviving_default_output() {
    assert_redirected_check_is_uncacheable(false);
}

#[test]
fn response_file_cannot_hide_redirected_check_metadata() {
    assert_redirected_check_is_uncacheable(true);
}

#[test]
fn response_file_content_changes_cannot_reuse_previous_metadata() {
    let fixture = Fixture::new();
    let root = fixture.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir_all(root.join(".cargo")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='response_changed'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        root.join("src/lib.rs"),
        "#[cfg(not(test))] pub fn value() -> u32 { 9 }\n#[cfg(test)] pub fn value() -> u64 { 9 }\n",
    )
    .unwrap();
    let response = root.join("compiler.args");
    fs::write(&response, "--cfg=initial\n").unwrap();
    let flags = [
        format!("--remap-path-prefix={}=/fixture", root.display()),
        format!("@{}", response.display()),
    ];
    fs::write(
        root.join(".cargo/config.toml"),
        format!(
            "[build]\nrustflags={}\n",
            serde_json::to_string(&flags).unwrap()
        ),
    )
    .unwrap();
    let first = compile(&root, "check");
    assert_eq!(first.len(), 1);
    assert_eq!(first[0]["fresh"], false);
    let metadata = first[0]["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|path| path.as_str())
        .find(|path| path.ends_with(".rmeta"))
        .map(PathBuf::from)
        .expect("default metadata output");
    let original = fs::read(&metadata).unwrap();
    // Leave every outer argument and source byte unchanged. The real compiler
    // reads this file before Session construction and changes the public API.
    fs::write(&response, "--cfg=test\n").unwrap();
    assert_eq!(
        compile(&root, "check")[0]["fresh"],
        false,
        "changed response contents must rerun the compiler; fixture: {}",
        root.display()
    );
    assert_ne!(fs::read(&metadata).unwrap(), original);
}

fn assert_redirected_check_is_uncacheable(response_file: bool) {
    // Preserve a failed native fixture for inspection. This compiles metadata
    // only; the compiler itself runs from the explicitly selected SDK in place.
    let fixture = Fixture::new();
    let root = fixture.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir_all(root.join(".cargo")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='routed'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "pub fn value() -> u32 { 9 }\n").unwrap();
    // Allocate the redirect before input observation, so its first write does
    // not change the source directory's membership during the compiler run.
    let redirected = root.join("redirect.rmeta");
    fs::write(&redirected, []).unwrap();
    let response = root.join("emit.args");
    let emission = format!("--emit=metadata={}", redirected.display());
    fs::write(&response, format!("{emission}\n")).unwrap();
    let remap = format!("--remap-path-prefix={}=/fixture", root.display());
    let configure = |flags: &[String]| {
        fs::write(
            root.join(".cargo/config.toml"),
            format!(
                "[build]\nrustflags={}\n",
                serde_json::to_string(flags).unwrap()
            ),
        )
        .unwrap();
    };
    configure(std::slice::from_ref(&remap));
    let first = compile(&root, "check");
    assert_eq!(first.len(), 1, "fixture: {}", root.display());
    assert_eq!(first[0]["fresh"], false);
    let metadata = first[0]["filenames"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|path| path.as_str())
        .find(|path| path.ends_with(".rmeta"))
        .map(PathBuf::from)
        .expect("default metadata output");
    let original = fs::read(&metadata).unwrap();
    assert_eq!(compile(&root, "check")[0]["fresh"], true);

    fs::write(root.join("src/lib.rs"), "pub fn value() -> u64 { 9 }\n").unwrap();
    // A remap-containing flags vector keeps the same output layout even when
    // its input fingerprint changes. Later --emit overrides Cargo's metadata
    // destination, leaving the previous default metadata file in that layout.
    let argument = if response_file {
        format!("@{}", response.display())
    } else {
        emission
    };
    configure(&[remap, argument]);
    assert_eq!(compile(&root, "check")[0]["fresh"], false);
    assert_eq!(fs::read(&metadata).unwrap(), original);
    assert_ne!(fs::read(&redirected).unwrap(), original);
    assert_eq!(
        compile(&root, "check")[0]["fresh"],
        false,
        "custom metadata routing must not bless an old default output; response_file={response_file}, fixture: {}",
        root.display()
    );
    assert!(
        !walkdir::WalkDir::new(root.join("target"))
            .into_iter()
            .filter_map(Result::ok)
            .any(|entry| entry.file_name() == OsString::from("outputs-lib-routed.json")),
        "custom emission cannot publish a receipt for the surviving default output"
    );
}

#[test]
fn native_cache_rebuilds_corrupt_bytes_and_receipts_without_recompiling_warm_inputs() {
    // Keep the fixture under a test-owned directory of this checkout, not a
    // world-writable /tmp target (see `Fixture`). No registry or network
    // inputs are involved.
    let fixture = Fixture::new();
    let root = fixture.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir_all(root.join("dep/src")).unwrap();
    fs::write(root.join("Cargo.toml"), "[package]\nname='consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\ndep={path='dep'}\n").unwrap();
    fs::write(
        root.join("src/main.rs"),
        "fn main() { assert_eq!(dep::value(), 9); }\n",
    )
    .unwrap();
    fs::write(
        root.join("dep/Cargo.toml"),
        "[package]\nname='dep'\nversion='0.0.0'\nedition='2021'\n",
    )
    .unwrap();
    fs::write(root.join("dep/src/lib.rs"), "pub fn value() -> u32 { 9 }\n").unwrap();

    let first = build(root);
    assert_eq!(dependency(&first)["fresh"], false);
    let archive = dependency_archive(dependency(&first));
    let pristine = fs::read(&archive).unwrap();
    let warm = build(root);
    assert!(warm.iter().all(|row| row["fresh"] == true), "{warm:?}");

    let time = filetime::FileTime::from_last_modification_time(&fs::metadata(&archive).unwrap());
    let mut damaged = pristine.clone();
    damaged[..8].copy_from_slice(b"BROKEN!!");
    fs::write(&archive, &damaged).unwrap();
    filetime::set_file_mtime(&archive, time).unwrap();
    let repaired = build(root);
    assert_eq!(
        dependency(&repaired)["fresh"],
        false,
        "damaged bytes must not be fresh"
    );
    let repaired_archive = fs::read(&archive).unwrap();
    assert!(
        repaired_archive.starts_with(b"!<arch>\n"),
        "a valid archive was regenerated"
    );
    assert!(
        repaired_archive != damaged,
        "the damaged archive must be replaced"
    );
    let executable = root.join("target/debug").join(if cfg!(windows) {
        "consumer.exe"
    } else {
        "consumer"
    });
    assert!(Command::new(executable).status().unwrap().success());

    let receipt = walkdir::WalkDir::new(root.join("target"))
        .into_iter()
        .filter_map(Result::ok)
        .find(|entry| entry.file_name() == OsString::from("outputs-lib-dep.json"))
        .expect("native output receipt")
        .into_path();
    let original = read_json(&receipt);
    let fingerprint = receipt.parent().unwrap().join("lib-dep.json");
    let fingerprint_bytes = fs::read(&fingerprint).unwrap();
    let fingerprint_json: serde_json::Value = serde_json::from_slice(&fingerprint_bytes).unwrap();
    assert_eq!(original["schema"], 3);
    let compiler_outputs = original["compiler_outputs"].as_array().unwrap();
    assert!(!compiler_outputs.is_empty());
    for output in compiler_outputs {
        let mut keys: Vec<_> = output
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect();
        keys.sort_unstable();
        assert_eq!(keys, ["emit", "path_sha256"]);
        assert!(matches!(output["emit"].as_str(), Some("link" | "metadata")));
        let path = output["path_sha256"].as_str().unwrap();
        assert_eq!(path.len(), 64);
        assert!(path.bytes().all(|byte| byte.is_ascii_hexdigit()));
    }
    assert!(
        compiler_outputs
            .iter()
            .any(|output| output["emit"] == "link")
    );
    let compiler = &original["compiler"];
    assert!(compiler["rustc_key"].as_u64().is_some());
    assert_eq!(compiler["rustc_key"], fingerprint_json["rustc"]);
    assert_eq!(compiler["workspace"], true);
    assert_eq!(compiler["mode"], "build");
    assert_eq!(compiler["build_script"], false);
    let content = compiler["content_blake3"].as_array().unwrap();
    assert_eq!(content.len(), 32);
    assert!(
        content
            .iter()
            .all(|byte| byte.as_u64().is_some_and(|value| value <= 255))
    );
    assert!(content.iter().any(|byte| byte != 0));

    // Every mutation starts from the receipt and bytes accepted by its own
    // preceding warm run. Recompilation need not reproduce identical bytes.
    let snapshot = || {
        (
            read_json(&receipt),
            fs::read(&archive).unwrap(),
            fs::read(&fingerprint).unwrap(),
        )
    };
    let unchanged = |before: &(serde_json::Value, Vec<u8>, Vec<u8>)| {
        assert_eq!(fs::read(&archive).unwrap(), before.1);
        assert_eq!(fs::read(&fingerprint).unwrap(), before.2);
    };

    // Keep the real files and ordinary artifact key unchanged. A changed
    // recorded compiler-output path cannot stand for the current inventory.
    let before_output = snapshot();
    let mut changed_output = before_output.0.clone();
    let digest = changed_output["compiler_outputs"][0]["path_sha256"]
        .as_str()
        .unwrap();
    let replacement = if digest.starts_with('0') { "1" } else { "0" };
    changed_output["compiler_outputs"][0]["path_sha256"] =
        format!("{replacement}{}", &digest[1..]).into();
    assert_eq!(
        changed_output["fingerprint"],
        before_output.0["fingerprint"]
    );
    fs::write(&receipt, serde_json::to_vec(&changed_output).unwrap()).unwrap();
    unchanged(&before_output);
    assert_eq!(
        dependency(&build(root))["fresh"],
        false,
        "changed compiler-output coverage must miss"
    );
    assert_eq!(
        read_json(&receipt)["compiler_outputs"],
        before_output.0["compiler_outputs"]
    );
    assert!(build(root).iter().all(|row| row["fresh"] == true));

    // The previous production schema had no live-report coverage. It must be
    // regenerated, never silently upgraded by trusting the old output bytes.
    let before_legacy = snapshot();
    let mut legacy = before_legacy.0.clone();
    legacy["schema"] = 2.into();
    assert!(
        legacy
            .as_object_mut()
            .unwrap()
            .remove("compiler_outputs")
            .is_some()
    );
    fs::write(&receipt, serde_json::to_vec(&legacy).unwrap()).unwrap();
    unchanged(&before_legacy);
    assert_eq!(
        dependency(&build(root))["fresh"],
        false,
        "legacy output receipts must miss"
    );
    assert_eq!(read_json(&receipt)["schema"], 3);
    assert!(build(root).iter().all(|row| row["fresh"] == true));

    // Change only the recorded compiler observation. The real outputs and
    // ordinary input fingerprint are unchanged; this must still be a miss.
    let before_compiler = snapshot();
    let mut changed_compiler = before_compiler.0.clone();
    let selected_byte = changed_compiler["compiler"]["content_blake3"][0]
        .as_u64()
        .unwrap();
    changed_compiler["compiler"]["content_blake3"][0] = (selected_byte ^ 1).into();
    assert_eq!(
        changed_compiler["fingerprint"],
        before_compiler.0["fingerprint"]
    );
    fs::write(&receipt, serde_json::to_vec(&changed_compiler).unwrap()).unwrap();
    unchanged(&before_compiler);
    assert_eq!(
        dependency(&build(root))["fresh"],
        false,
        "a changed compiler observation must not be fresh"
    );
    assert_eq!(
        read_json(&receipt)["compiler"],
        before_compiler.0["compiler"]
    );
    assert!(build(root).iter().all(|row| row["fresh"] == true));

    // A receipt with the old field inventory cannot silently acquire a
    // current compiler observation. Keep the schema and artifact key intact
    // so this control specifically exercises the mandatory field.
    let before_missing = snapshot();
    let mut missing_compiler = before_missing.0.clone();
    assert!(
        missing_compiler
            .as_object_mut()
            .unwrap()
            .remove("compiler")
            .is_some()
    );
    assert_eq!(
        missing_compiler["fingerprint"],
        before_missing.0["fingerprint"]
    );
    fs::write(&receipt, serde_json::to_vec(&missing_compiler).unwrap()).unwrap();
    unchanged(&before_missing);
    assert_eq!(
        dependency(&build(root))["fresh"],
        false,
        "a receipt without a compiler observation must not be fresh"
    );
    assert_eq!(
        read_json(&receipt)["compiler"],
        before_missing.0["compiler"]
    );
    assert!(build(root).iter().all(|row| row["fresh"] == true));

    for bytes in [Some(b"{".as_slice()), None] {
        let before_malformed = snapshot();
        match bytes {
            Some(bytes) => fs::write(&receipt, bytes).unwrap(),
            None => fs::remove_file(&receipt).unwrap(),
        }
        unchanged(&before_malformed);
        assert_eq!(dependency(&build(root))["fresh"], false);
        assert!(build(root).iter().all(|row| row["fresh"] == true));
    }
}
