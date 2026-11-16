// Copyright 2026 Andrew Yates | Apache-2.0
//! Engineering producer: copies the loader's exact owned bytes into a new
//! bundle and emits comparison metadata. This creates no checked token.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use clean_kernel::{Environment, Name};
use clean_olean::{CapturedModuleBytes, ImportError, load_modules_with_deps_checked};
use serde::Serialize;
use sha2::{Digest, Sha256};
#[derive(Serialize)]
struct Parts {
    base: String,
    server: Option<String>,
    private: Option<String>,
    ir: Option<String>,
}
#[derive(Serialize)]
struct Manifest {
    schema: String,
    ir_commit: String,
    lean_version: String,
    lean_githash: String,
    source_sha256: BTreeMap<String, String>,
    modules: BTreeMap<String, Parts>,
}
fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn fail(n: &Name, why: String) -> ImportError {
    ImportError::UnsupportedModule { module: n.to_string(), reason: why }
}
fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    assert!(args.len() >= 3, "output-dir source-metadata-json search...");
    let output = PathBuf::from(&args[0]);
    std::fs::create_dir(&output).unwrap();
    let metadata: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&args[1]).unwrap()).unwrap();
    let search = args[2..].iter().map(PathBuf::from).collect::<Vec<_>>();
    let mut env = Environment::for_lean_replay();
    let mut modules = BTreeMap::new();
    let mut before = |_: &Name, _: &Path, _: usize| Ok(());
    let mut captured = |name: &Name, _: &Path, bytes: CapturedModuleBytes<'_>| {
        let text = name.to_string();
        if text
            .split('.')
            .any(|p| p.is_empty() || !p.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'))
        {
            return Err(fail(name, "nonportable module name".into()));
        }
        let base = output.join(text.replace('.', "/") + ".olean");
        std::fs::create_dir_all(base.parent().unwrap()).map_err(|e| fail(name, e.to_string()))?;
        for (suffix, content) in [
            ("", Some(bytes.base)),
            (".server", bytes.server),
            (".private", bytes.private),
            (".ir", bytes.ir),
        ] {
            if let Some(content) = content {
                let path = if suffix == ".ir" {
                    base.with_extension("ir")
                } else {
                    PathBuf::from(format!("{}{suffix}", base.display()))
                };
                std::fs::write(path, content).map_err(|e| fail(name, e.to_string()))?;
            }
        }
        modules.insert(
            text,
            Parts {
                base: hash(bytes.base),
                server: bytes.server.map(hash),
                private: bytes.private.map(hash),
                ir: bytes.ir.map(hash),
            },
        );
        Ok(())
    };
    load_modules_with_deps_checked(
        &mut env,
        &["SemRFrameCaller".into()],
        &search,
        &mut before,
        &mut captured,
    )
    .unwrap();
    let manifest = Manifest {
        schema: "trust.frame-step-cohort.v1".into(),
        ir_commit: metadata["ir_commit"].as_str().unwrap().into(),
        lean_version: "4.30.0-rc2".into(),
        lean_githash: metadata["lean_githash"].as_str().unwrap().into(),
        source_sha256: serde_json::from_value(metadata["source_sha256"].clone()).unwrap(),
        modules,
    };
    let bytes = serde_json::to_vec_pretty(&manifest).unwrap();
    std::fs::write(output.join("MANIFEST.json"), &bytes).unwrap();
    println!("{}", hash(&bytes));
}
