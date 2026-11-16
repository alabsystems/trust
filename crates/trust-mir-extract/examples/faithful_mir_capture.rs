// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Diagnostic Cargo workspace wrapper for the ACTUAL Clean literal helper.
//!
//! Build against a byte-matched rustc-private driver, then run from Clean:
//! ```text
//! TRUST_FAITHFUL_CAPTURE_CLEAN_ROOT=/absolute/clean
//! TRUST_FAITHFUL_CAPTURE_TRUST_ROOT=/absolute/trust-main
//! TRUST_FAITHFUL_CAPTURE_DRIVER=/actual/linked/librustc_driver.dylib
//! TRUST_FAITHFUL_CAPTURE_OUTPUT=/fresh/directory/capture.json
//! RUSTC_WORKSPACE_WRAPPER=/absolute/faithful_mir_capture
//! CARGO_TARGET_DIR=/absolute/clean/target.noindex/FRESH-capture
//! targo --unverified check --release --locked -j 1 -p clean-kernel --lib
//! ```
//! These are environment assignments for ONE invocation, not configuration
//! edits. Use a fresh target directory: disabling incremental compilation does
//! not defeat Cargo's primary-unit freshness check. The caller must require the
//! capture file after Cargo succeeds; this process cannot observe a cached unit
//! that Cargo never invokes. Nothing in this diagnostic grants proof authority.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

#[path = "faithful_mir_capture/callees.rs"]
mod callees;
#[path = "faithful_mir_capture/support.rs"]
mod support;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::{Arc, Mutex};
use std::{fs, io};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::{FileLoader, RealFileLoader};
use serde_json::{Value, json};
use trust_types::VerifiableFunction;

const OWNER: &str = "clean_kernel::tc::infer::infer_literal_type";

type Reads = Arc<Mutex<BTreeMap<PathBuf, String>>>;

struct RecordingLoader {
    reads: Reads,
}

impl RecordingLoader {
    fn remember(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let mut reads = self.reads.lock().map_err(|_| io::Error::other("poisoned read ledger"))?;
        support::record_read(&mut reads, path, bytes).map_err(io::Error::other)
    }
}

impl FileLoader for RecordingLoader {
    fn file_exists(&self, path: &Path) -> bool {
        RealFileLoader.file_exists(path)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        let contents = RealFileLoader.read_file(path)?;
        self.remember(path, contents.as_bytes())?;
        Ok(contents)
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        let contents = RealFileLoader.read_binary_file(path)?;
        self.remember(path, &contents)?;
        Ok(contents)
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        RealFileLoader.current_directory()
    }
}

#[derive(Default)]
struct Capture {
    reads: Reads,
    function: Option<VerifiableFunction>,
    identity: Option<Value>,
    optimized_mir_debug: Option<String>,
    optimized_mir_text: Option<String>,
    callee_inventory: Option<Value>,
    file_dependencies: Vec<String>,
    environment_dependencies: Vec<(String, Option<String>)>,
    error: Option<String>,
}

impl Callbacks for Capture {
    fn config(&mut self, config: &mut Config) {
        // Real filesystem, not an in-memory fixture or rewritten source.
        config.file_loader = Some(Box::new(RecordingLoader { reads: self.reads.clone() }));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        let owners: Vec<_> = tcx
            .hir_body_owners()
            .filter(|owner| trust_mir_extract::safe_def_path_str(tcx, owner.to_def_id()) == OWNER)
            .collect();
        if let Err(error) = support::require_one_owner(owners.len()) {
            self.error = Some(error);
            return Compilation::Stop;
        }
        let owner = owners[0].to_def_id();
        let body = tcx.optimized_mir(owner);
        self.optimized_mir_debug = Some(format!("{body:#?}"));
        let mut mir_text = Vec::new();
        if let Err(error) =
            rustc_middle::mir::pretty::MirWriter::new(tcx).write_mir_fn(body, &mut mir_text)
        {
            self.error = Some(format!("cannot render actual optimized MIR: {error}"));
            return Compilation::Stop;
        }
        self.optimized_mir_text = match String::from_utf8(mir_text) {
            Ok(text) => Some(text),
            Err(error) => {
                self.error = Some(format!("optimized MIR rendering is not UTF-8: {error}"));
                return Compilation::Stop;
            }
        };
        let (function, allocation_functions) =
            trust_mir_extract::instance_body::extract_faithful_body_with_function_allocations(
                tcx, body,
            );
        if function.def_path != OWNER {
            self.error = Some(format!("extractor returned unexpected owner {}", function.def_path));
            return Compilation::Stop;
        }
        self.callee_inventory = match callees::capture(tcx, body, &function, allocation_functions) {
            Ok(inventory) => Some(inventory),
            Err(error) => {
                self.error = Some(error);
                return Compilation::Stop;
            }
        };
        self.identity = Some(json!({
            "def_path": OWNER,
            "def_path_hash_debug": format!("{:?}", tcx.def_path_hash(owner)),
            "stable_crate_id_debug": format!("{:?}", tcx.stable_crate_id(owner.krate)),
            "crate_name": tcx.crate_name(owner.krate).to_string(),
            "mir_phase_debug": format!("{:?}", body.phase),
            "source_span": function.span,
            "mir_basic_blocks": body.basic_blocks.len(),
            "mir_local_declarations": body.local_decls.len(),
        }));
        self.file_dependencies =
            tcx.sess.file_depinfo.lock().iter().map(ToString::to_string).collect();
        self.environment_dependencies = tcx
            .sess
            .env_depinfo
            .lock()
            .iter()
            .map(|(name, value)| (name.to_string(), value.map(|value| value.to_string())))
            .collect();
        self.file_dependencies.sort();
        self.environment_dependencies.sort();
        self.function = Some(function);
        // Finish the actual Cargo compilation; do not forge a successful unit
        // whose requested metadata/rlib was never produced.
        Compilation::Continue
    }
}

fn required_path(name: &str) -> Result<PathBuf, String> {
    let value = std::env::var_os(name).ok_or_else(|| format!("missing {name}"))?;
    let path = PathBuf::from(value);
    fs::canonicalize(&path).map_err(|error| format!("{name} {}: {error}", path.display()))
}

fn command_text(program: &Path, args: &[&str]) -> Result<String, String> {
    let output = Command::new(program).args(args).output().map_err(|error| error.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "{} {args:?} failed: {}",
            program.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| error.to_string())
}

fn run() -> Result<ExitCode, String> {
    let mut raw = std::env::args_os().skip(1);
    let compiler = PathBuf::from(raw.next().ok_or("expected Cargo's original compiler argument")?);
    let raw: Vec<_> = raw.collect();
    let args: Vec<_> = raw
        .iter()
        .map(|arg| {
            arg.to_str()
                .map(str::to_owned)
                .ok_or_else(|| "non-UTF-8 compiler argument is outside this diagnostic".to_owned())
        })
        .collect::<Result<_, _>>()?;
    support::reject_response_files(&args)?;
    let crate_name = support::single_option(&args, "--crate-name")?;
    let manifest = std::env::var_os("CARGO_MANIFEST_DIR").map(PathBuf::from);
    let clean_root = if crate_name.as_deref() == Some("clean_kernel") {
        Some(required_path("TRUST_FAITHFUL_CAPTURE_CLEAN_ROOT")?)
    } else {
        None
    };
    if !support::select_primary(&args, manifest.as_deref(), clean_root.as_deref())? {
        let status =
            Command::new(&compiler).args(&raw).status().map_err(|error| error.to_string())?;
        return Ok(ExitCode::from(u8::try_from(status.code().unwrap_or(1)).unwrap_or(1)));
    }

    let clean_root = clean_root.ok_or("selected primary has no Clean root")?;
    let trust_root = required_path("TRUST_FAITHFUL_CAPTURE_TRUST_ROOT")?;
    let driver = required_path("TRUST_FAITHFUL_CAPTURE_DRIVER")?;
    let compiler = fs::canonicalize(compiler).map_err(|error| error.to_string())?;
    let output = PathBuf::from(
        std::env::var_os("TRUST_FAITHFUL_CAPTURE_OUTPUT")
            .ok_or("missing TRUST_FAITHFUL_CAPTURE_OUTPUT")?,
    );
    support::require_fresh_output(&output)?;
    let sysroot = fs::canonicalize(command_text(&compiler, &["--print", "sysroot"])?.trim())
        .map_err(|error| error.to_string())?;
    let compiler_version = command_text(&compiler, &["-vV"])?;
    let embedded_version = rustc_interface::util::rustc_version_str()
        .ok_or("embedded driver did not report its compiler version")?;
    if !compiler_version.contains(embedded_version) {
        return Err(format!(
            "embedded driver {embedded_version} does not match {compiler_version}"
        ));
    }
    let args = support::bind_sysroot(args, &sysroot)?;
    let mut compiler_args = vec![compiler.to_string_lossy().into_owned()];
    compiler_args.extend(args);
    let wrapper = std::env::current_exe().map_err(|error| error.to_string())?;
    let paths = vec![
        compiler.clone(),
        driver,
        wrapper,
        clean_root.join("Cargo.toml"),
        clean_root.join("Cargo.lock"),
        clean_root.join(".cargo/config.toml"),
        clean_root.join("rust-toolchain.toml"),
        clean_root.join("crates/clean-kernel/Cargo.toml"),
        clean_root.join("crates/clean-kernel/src/lib.rs"),
        clean_root.join("crates/clean-kernel/src/tc/infer.rs"),
        trust_root.join("crates/trust-mir-extract/src/lib.rs"),
        trust_root.join("crates/trust-mir-extract/src/ty_convert.rs"),
        trust_root.join("crates/trust-mir-extract/src/convert.rs"),
        trust_root.join("crates/trust-mir-extract/src/convert/faithful_atomic_xadd.rs"),
        trust_root.join("crates/trust-mir-extract/src/constant_image.rs"),
        trust_root.join("crates/trust-mir-extract/src/instance_body.rs"),
        trust_root.join("crates/trust-mir-extract/examples/faithful_mir_capture.rs"),
        trust_root.join("crates/trust-mir-extract/examples/faithful_mir_capture/callees.rs"),
        trust_root.join("crates/trust-mir-extract/examples/faithful_mir_capture/support.rs"),
    ];
    let before = support::snapshot_paths(&paths)?;
    let clean_git = support::git_snapshot(&clean_root)?;
    let trust_git = support::git_snapshot(&trust_root)?;
    let mut capture = Capture::default();
    let compiled = rustc_driver::catch_fatal_errors(|| {
        // Typed embedding explicitly uses NoTrustEvidence. No
        // canonical-main entry, verified flag, proof transport, or dump gate is
        // impersonated by this diagnostic callback.
        rustc_driver::run_compiler_with_expanded_args_and_no_trust_evidence(
            &compiler_args,
            &mut capture,
            rustc_driver::NoTrustEvidence,
        );
    });
    if compiled.is_err() {
        return Err("compiler failed; no successful capture published".into());
    }
    if let Some(error) = capture.error {
        return Err(error);
    }
    let function = capture.function.ok_or("compiler did not analyze the selected helper")?;
    if before != support::snapshot_paths(&paths)?
        || clean_git != support::git_snapshot(&clean_root)?
        || trust_git != support::git_snapshot(&trust_root)?
    {
        return Err("source/tool/repository inputs changed during compilation".into());
    }
    let reads = capture.reads.lock().map_err(|_| "poisoned read ledger")?;
    support::check_observed_reads(&reads)?;
    let dependency_paths: Vec<_> = capture.file_dependencies.iter().map(PathBuf::from).collect();
    let observed_file_dependencies = support::snapshot_paths(&dependency_paths)?;
    let function_json = serde_json::to_value(&function).map_err(|error| error.to_string())?;
    let function_digest = support::json_digest(&function_json)?;
    let report = json!({
        "schema_version": "trust.faithful-mir-capture.diagnostic/v1",
        "evidence_grade": "diagnostic-no-official-evidence",
        "compiler_completed": true,
        "extractor_entry": "trust_mir_extract::instance_body::extract_faithful_body_with_function_allocations",
        "function": function_json,
        "function_json_sha256": function_digest,
        "function_json_encoding": "serde_json::to_vec(report[function]), JSON object keys sorted",
        "compiler_identity": capture.identity,
        "optimized_mir_debug": capture.optimized_mir_debug,
        "optimized_mir_text": capture.optimized_mir_text,
        "callee_inventory": capture.callee_inventory,
        "compiler_argv": compiler_args,
        "compiler_verbose_version": compiler_version,
        "embedded_driver_version": embedded_version,
        "sysroot": sysroot,
        "cwd": std::env::current_dir().map_err(|error| error.to_string())?,
        "clean_repository": clean_git,
        "trust_repository": trust_git,
        "stable_observed_inputs": before,
        "compiler_file_loader_reads": reads.iter().map(|(path, sha256)| json!({"path": path, "sha256": sha256})).collect::<Vec<_>>(),
        "compiler_file_dependencies_after_analysis": observed_file_dependencies,
        "compiler_environment_dependencies_after_analysis": capture.environment_dependencies,
        "limits": [
            "Diagnostic extraction is not a source refinement certificate or compiler product qualification.",
            "Caller-selected driver file is byte-bound but runtime loader selection is not attested here.",
            "Current extractor source files are byte-bound; the caller must independently bind the build to these sources.",
            "FileLoader reads and compiler-reported dependencies are observed inputs, not an exhaustive transitive artifact, proc-macro, native library or environment closure.",
            "Environment and file dependency queries are sampled after analysis; later codegen-only dependencies are not included.",
            "Serde may erase or demote authority fields; this is not authority-preserving proof transport.",
            "No claim is made that the extracted operations or complete callee closure are executable or verified."
        ],
    });
    support::publish_new(&output, &report)?;
    eprintln!("faithful-mir-capture: diagnostic helper capture published to {}", output.display());
    Ok(ExitCode::SUCCESS)
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("faithful-mir-capture: {error}");
            ExitCode::FAILURE
        }
    }
}
