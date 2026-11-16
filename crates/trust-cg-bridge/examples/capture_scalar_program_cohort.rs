//! Untrusted candidate artifact constructor for the fixed actual byte-to-program model only. No Trust/IR typed dependency, proof generation,
//! compiler invocation or source/ABI/grade authority. The future consumer must
//! FULL-recheck the captured dependency cone through its fixed compiled cohort.
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::{Environment, Name};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{
    CapturedModuleBytes, ImportError, OleanHeader, load_modules_with_deps_checked,
    reference_base_closed,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[path = "../src/compiler_input_capture/semr_scalar/program_contract.rs"]
mod program_contract;
const ROOT: &str = program_contract::ROOT_MODULE;
#[path = "../src/compiler_input_capture/semr_scalar/source_contract.rs"]
mod source_contract;
#[path = "../src/compiler_input_capture/semr_scalar/source_binding.rs"]
mod foundation_source_binding;
#[path = "../src/compiler_input_capture/semr_scalar/program/source_binding.rs"]
mod program_source_binding;
// Include the same private source checks without adding a runtime selector
// or exposing a proof/grade constructor from the library.
mod object_replay {
    pub(super) fn artifact_digest(bytes: &[u8]) -> String {
        super::hash(bytes)
    }
}

// Exact recursive source-import closure of the fixed production ROOT.
const PROJECT: &[&str] = &[
    "MiniRust",
    "MiniRustAllocate",
    "MiniRustAllocate8Room",
    "MiniRustAllocate8Safety",
    "MiniRustMachineNew",
    "MiniRustProgramCall",
    "MiniRustProgramExit",
    "MiniRustProgramStep",
    "MiniRustU64AllocatedCall",
    "MiniRustU64Availability",
    "MiniRustU64Call",
    "MiniRustU64Correspondence",
    "MiniRustU64Entry",
    "MiniRustU64Execution",
    "MiniRustU64ExitCall",
    "MiniRustU64ExitExecution",
    "MiniRustU64ExitProgram",
    "MiniRustU64ExitRun",
    "MiniRustU64ExitStart",
    "MiniRustU64ExitStop",
    "MiniRustU64Function",
    "MiniRustU64Program",
    "MiniRustU64ProgramCall",
    "MiniRustU64ProgramExecution",
    "MiniRustU64ProgramFromBytes",
    "MiniRustU64ProgramReturn",
    "MiniRustU64ProgramRun",
    "MiniRustU64ProgramStart",
    "MiniRustU64ProgramTyping",
    "MiniRustU64Return",
    "MiniRustU64Run",
    "MiniRustU64ScalarCorrespondence",
    "MiniRustU64Step",
    "SemR",
    "SemRMemory",
    "SemRMiniRust",
    "U64Addition",
    "U64ScalarProfile",
];
const GIT: &str = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc";
fn hash(b: &[u8]) -> String {
    Sha256::digest(b).iter().map(|byte| format!("{byte:02x}")).collect()
}
fn error(name: &Name, reason: impl Into<String>) -> ImportError {
    ImportError::UnsupportedModule { module: name.to_string(), reason: reason.into() }
}
#[derive(Serialize)]
struct Parts {
    base: String,
    server: Option<String>,
    private: Option<String>,
    ir: Option<String>,
}
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceMetadata {
    ir_commit: String,
    clean_commit: String,
    source_sha256: BTreeMap<String, String>,
}
#[derive(Serialize)]
struct Manifest {
    schema: &'static str,
    ir_commit: String,
    lean_version: &'static str,
    lean_githash: &'static str,
    source_sha256: BTreeMap<String, String>,
    modules: BTreeMap<String, Parts>,
}
fn main() {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    assert_eq!(
        args.len(),
        4,
        "NEW output-directory source-metadata producer-family exact-Lean-lib"
    );
    let output = PathBuf::from(&args[0]);
    assert!(!output.exists());
    let metadata: SourceMetadata =
        serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
    assert_eq!(metadata.ir_commit, program_contract::MODEL_IR);
    assert_eq!(metadata.clean_commit, source_contract::PRODUCER_CLEAN);
    // The historical extension and selected foundation both retain their
    // independent exact-source checks; neither can select a runtime model.
    program_source_binding::check(&serde_json::to_string(&metadata).unwrap()).unwrap();
    assert!(!metadata.source_sha256.is_empty());
    let search = [
        PathBuf::from(&args[2]).canonicalize().unwrap(),
        PathBuf::from(&args[3]).canonicalize().unwrap(),
    ];
    std::fs::create_dir(&output).unwrap();
    let mut env = Environment::for_lean_replay();
    let mut modules = BTreeMap::new();
    let mut seen_paths = BTreeSet::new();
    let mut before = |name: &Name, path: &Path, index: usize| {
        let text = name.to_string();
        let wanted = if PROJECT.contains(&text.as_str()) { 0 } else { 1 };
        if index != wanted
            || index > 1
            || (!PROJECT.contains(&text.as_str()) && !(text == "Init" || text.starts_with("Init.")))
            || text.split('.').any(|part| {
                part.is_empty() || !part.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
            })
        {
            return Err(error(
                name,
                "module is outside exact canonical scalar/Init source families",
            ));
        }
        let exact = search[index].join(text.replace('.', "/") + ".olean");
        if path != exact
            || path.canonicalize().ok().as_ref() != Some(&exact)
            || !std::fs::symlink_metadata(path)
                .map_err(|e| error(name, e.to_string()))?
                .file_type()
                .is_file()
        {
            return Err(error(name, "producer base path/kind differs"));
        }
        if !seen_paths.insert(path.to_owned()) {
            return Err(error(name, "duplicate producer path"));
        }
        Ok(())
    };
    let mut captured = |name: &Name, path: &Path, bytes: CapturedModuleBytes<'_>| {
        let text = name.to_string();
        let header = OleanHeader::parse(bytes.base).map_err(|e| error(name, e.to_string()))?;
        if header.lean_version.as_deref() != Some("4.30.0-rc2") || !header.matches_git_hash(GIT) {
            return Err(error(name, "actual captured module toolchain header differs"));
        }
        let base = output.join(text.replace('.', "/") + ".olean");
        std::fs::create_dir_all(base.parent().unwrap()).map_err(|e| error(name, e.to_string()))?;
        for (suffix, content) in [
            ("", Some(bytes.base)),
            (".server", bytes.server),
            (".private", bytes.private),
            (".ir", bytes.ir),
        ] {
            if let Some(content) = content {
                let original = if suffix == ".ir" {
                    path.with_extension("ir")
                } else {
                    PathBuf::from(format!("{}{suffix}", path.display()))
                };
                if !std::fs::symlink_metadata(&original)
                    .map_err(|e| error(name, e.to_string()))?
                    .file_type()
                    .is_file()
                    || original.canonicalize().ok().as_ref() != Some(&original)
                {
                    return Err(error(name, "actual producer companion path/kind differs"));
                }
                let dst = if suffix == ".ir" {
                    base.with_extension("ir")
                } else {
                    PathBuf::from(format!("{}{suffix}", base.display()))
                };
                std::fs::write(dst, content).map_err(|e| error(name, e.to_string()))?;
            }
        }
        if modules
            .insert(
                text,
                Parts {
                    base: hash(bytes.base),
                    server: bytes.server.map(hash),
                    private: bytes.private.map(hash),
                    ir: bytes.ir.map(hash),
                },
            )
            .is_some()
        {
            return Err(error(name, "duplicate captured module"));
        }
        Ok(())
    };
    load_modules_with_deps_checked(&mut env, &[ROOT.into()], &search, &mut before, &mut captured)
        .unwrap();
    assert!(PROJECT.iter().all(|name| modules.contains_key(*name)));
    let roots = program_contract::ROOTS
        .into_iter()
        .map(Name::from_string)
        .collect::<BTreeSet<_>>();
    let mut options = ClosedRecheckOptions::default();
    options.max_closure = Some(100_000);
    let checked = reference_base_closed(&env, &roots, &options).unwrap();
    println!("COHORT_CLOSED_REPLAY {}", serde_json::to_string(&checked.report).unwrap());
    assert!(checked.entry_refusals.is_empty(), "{:?}", checked.entry_refusals);
    assert!(checked.report.passed() && checked.report.extension_bindings_pinned);
    assert!(roots.is_subset(&checked.admitted));
    let _kernel = checked.into_kernel().expect("complete fixed program replay");
    let manifest = Manifest {
        schema: program_contract::SCHEMA,
        ir_commit: metadata.ir_commit,
        lean_version: "4.30.0-rc2",
        lean_githash: GIT,
        source_sha256: metadata.source_sha256,
        modules,
    };
    let bytes = serde_json::to_vec_pretty(&manifest).unwrap();
    std::fs::write(output.join("MANIFEST.json"), &bytes).unwrap();
    println!(
        "SCALAR_PROGRAM_COHORT_CAPTURE modules={} manifest={}",
        manifest.modules.len(),
        hash(&bytes)
    );
}
