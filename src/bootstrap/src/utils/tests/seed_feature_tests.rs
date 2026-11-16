//! Trust: merge regressions in compiler feature declarations must fail before a full self-build.

use std::fs;
use std::path::Path;
use std::process::Command;

use super::TestCtx;

/// Read the crate header, retaining actual feature declarations rather than a
/// second handwritten copy of their version/bootstrap conditions.
fn features(source: &str) -> String {
    let mut result = String::new();
    let mut attribute = String::new();
    let mut depth = 0_i32;
    for line in source.lines() {
        let trimmed = line.trim();
        if depth == 0 {
            if trimmed.is_empty() || trimmed.starts_with("//") {
                continue;
            }
            if !trimmed.starts_with("#![") {
                break;
            }
        }
        attribute.push_str(line);
        attribute.push('\n');
        depth += line.bytes().filter(|&byte| byte == b'[').count() as i32;
        depth -= line.bytes().filter(|&byte| byte == b']').count() as i32;
        if depth == 0 {
            if attribute.contains("feature(") {
                result.push_str(&attribute);
            }
            attribute.clear();
        }
    }
    assert_eq!(depth, 0, "incomplete compiler crate attribute");
    result
}

/// Trust: the one probe compile, built apart so its environment is testable.
fn seed_probe_command(
    rustc: &Path,
    input: &Path,
    proc_macro: bool,
    out_dir: &Path,
    bootstrap: bool,
) -> Command {
    let mut command = Command::new(rustc);
    // Trust: these declarations belong to compiler/tool crates, not
    // Bootstrap itself. Keep its compiler shim and scheduling authority,
    // but do not inherit Bootstrap's per-crate feature list or host cfgs.
    // The probe supplies the two bootstrap modes explicitly below.
    command
        .env_remove("RUSTC_ALLOW_FEATURES")
        .env_remove("RUSTC_HOST_FLAGS")
        // Trust: the compiler here is Bootstrap's rustc shim, whose
        // `maybe_dump` appends to `$DUMP_BOOTSTRAP_SHIMS` and unwraps the open.
        // That variable is process-global, and the parallel test
        // `shim_utils_tests::maybe_dump_creates_dump_directory` points it at a
        // `TempDir` it then deletes. A probe spawned in that window inherits
        // the path and panics in the shim (`Os { code: 22 }` at
        // shared_helpers.rs:116, land gate 20261102T083817). A probe has no
        // use for a dump, so it never inherits the variable.
        .env_remove("DUMP_BOOTSTRAP_SHIMS")
        .arg(input)
        .args(["--crate-type", if proc_macro { "proc-macro" } else { "lib" }])
        .args(["--emit=metadata", "--cfg", "feature=\"nightly\""])
        .arg("--out-dir")
        .arg(out_dir)
        .env("RUSTC_BOOTSTRAP", "1");
    if bootstrap {
        command.args(["--cfg", "bootstrap"]);
    }
    command
}

// Trust: regression for the race above. Deterministic: whatever the test
// process's environment holds when a probe is spawned, the probe's command
// removes the dump variable, so the shim's dump hook cannot fire in a probe.
#[test]
fn seed_probe_never_inherits_the_shim_dump_directory() {
    use std::ffi::OsStr;
    for (proc_macro, bootstrap) in [(false, false), (false, true), (true, false), (true, true)] {
        let command = seed_probe_command(
            Path::new("rustc"),
            Path::new("seed_features.rs"),
            proc_macro,
            Path::new("out"),
            bootstrap,
        );
        let dump = command
            .get_envs()
            .find(|(key, _)| *key == OsStr::new("DUMP_BOOTSTRAP_SHIMS"))
            .map(|(_, value)| value);
        assert_eq!(
            dump,
            Some(None),
            "a seed probe must REMOVE DUMP_BOOTSTRAP_SHIMS, not inherit it \
             (proc_macro={proc_macro}, bootstrap={bootstrap})"
        );
        let wants_bootstrap_cfg = command.get_args().any(|arg| arg == OsStr::new("bootstrap"));
        assert_eq!(wants_bootstrap_cfg, bootstrap, "the probe carries exactly its own mode's cfg");
    }
}

fn check_actual_feature_declarations(bootstrap: bool) {
    let context = TestCtx::new();
    let config = context.config("check").create_config();
    let compiler = config.src.join("compiler");
    let mut manifests = fs::read_dir(compiler)
        .unwrap()
        .map(|entry| entry.unwrap().path().join("Cargo.toml"))
        .filter(|path| path.is_file())
        .collect::<Vec<_>>();
    // Trust: compiler checks also consume tool crates outside compiler/.
    for path in [
        "src/librustdoc/Cargo.toml",
        "src/tools/tippy/clippy_lints/Cargo.toml",
        "src/tools/tippy/clippy_utils/Cargo.toml",
    ] {
        manifests.push(config.src.join(path));
    }
    manifests.sort();
    let mut checked = 0;
    // Trust: what the walk READ, apart from what carried a gate. Which headers
    // carry a `bootstrap` twin follows upstream, which retires its twins at
    // each stage0 bump (DQ SEED-BRIDGE-1), so the walk's reach is held here
    // instead: a broken `lib.path` or tool path must fail, not skip.
    let mut read_proc_macro = false;
    let mut read_tools = Vec::new();
    let mut failures = Vec::new();
    for manifest_path in manifests {
        let manifest: toml::Value =
            toml::from_str(&fs::read_to_string(&manifest_path).unwrap()).unwrap();
        let package = manifest["package"]["name"].as_str().unwrap_or_default().to_owned();
        let lib_path =
            manifest.get("lib").and_then(|lib| lib.get("path")).and_then(toml::Value::as_str);
        let source = manifest_path.parent().unwrap().join(lib_path.unwrap_or("src/lib.rs"));
        let tool = matches!(package.as_str(), "rustdoc" | "clippy_lints" | "clippy_utils");
        if !source.is_file() {
            // Only a binary crate (no `[lib]`, no `src/lib.rs`) has no header to read.
            assert!(
                lib_path.is_none() && !tool,
                "{} names a library source that does not exist: {}",
                manifest_path.display(),
                source.display(),
            );
            continue;
        }
        read_proc_macro |= package == "rustc_proc_macro";
        if tool {
            read_tools.push(package.clone());
        }
        let declarations = features(&fs::read_to_string(&source).unwrap());
        if !declarations.contains("bootstrap") && !declarations.contains("version(") {
            continue;
        }
        checked += 1;
        let proc_macro = manifest
            .get("lib")
            .and_then(|lib| lib.get("proc-macro"))
            .and_then(toml::Value::as_bool)
            .unwrap_or(false);
        let input = context.dir().join("seed_features.rs");
        let stability = if declarations.contains("feature(staged_api)") {
            "#![unstable(feature = \"seed_feature_test\", issue = \"none\")]"
        } else {
            ""
        };
        // Trust: also prove that each probe receives its requested cfg;
        // bootstrap's tool-host flags otherwise silently enable both cases.
        let wrong_cfg = if bootstrap { "not(bootstrap)" } else { "bootstrap" };
        fs::write(
                &input,
                format!(
                    "#![allow(internal_features, stable_features)]\n#![deny(duplicate_features)]\n{declarations}\n{stability}\n#[cfg({wrong_cfg})]\ncompile_error!(\"incorrect bootstrap cfg in seed feature probe\");\nextern crate proc_macro;\nfn marker() {{}}\n"
                ),
            )
            .unwrap();
        let mut command = seed_probe_command(
            config.external_rustc.as_ref().expect("test config selects a compiler"),
            &input,
            proc_macro,
            context.dir(),
            bootstrap,
        );
        let output = crate::utils::metadata_scheduler::output(&mut command, true, true).unwrap();
        // Trust: report every broken header in this pass instead of making
        // each latent merge error wait for a separate compiler rebuild.
        if !output.status.success() {
            failures.push(format!(
                "{} fails with bootstrap={bootstrap}:\n{}",
                source.display(),
                String::from_utf8_lossy(&output.stderr),
            ));
        }
    }
    assert!(read_proc_macro, "the walk must follow a manifest's `lib.path` (rustc_proc_macro)");
    read_tools.sort();
    assert_eq!(
        read_tools,
        ["clippy_lints", "clippy_utils", "rustdoc"],
        "the walk must read the tool headers"
    );
    // Trust: an empty inventory would prove nothing. Once upstream retires its
    // last gated header, delete this regression; never weaken it to pass empty.
    assert!(checked > 0, "the regression must reach a gated compiler or tool feature declaration");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// Trust: give each mode its own temporary inputs and native test-harness task.
// Both inventories and all probes remain mandatory; the existing harness's
// thread limit owns concurrency, without an additional worker pool.
#[test]
fn seed_compiles_actual_bootstrap_feature_declarations() {
    check_actual_feature_declarations(true);
}

#[test]
fn seed_compiles_actual_non_bootstrap_feature_declarations() {
    check_actual_feature_declarations(false);
}
