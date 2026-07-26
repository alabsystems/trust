// trust_wp build-time trust_wp API probe
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rustc-check-cfg=cfg(trust_wp_proof_transport_api)");
    println!("cargo:rustc-check-cfg=cfg(trust_wp_structured_context_api)");
    println!("cargo:rustc-check-cfg=cfg(trust_wp_metadata_constants_api)");
    println!("cargo:rustc-check-cfg=cfg(trust_wp_typed_metadata_helper_api)");
    println!("cargo:rustc-check-cfg=cfg(trust_wp_verify_bundle_replay_helper_api)");

    let manifest_dir = PathBuf::from(
        env::var_os("CARGO_MANIFEST_DIR")
            .expect("CARGO_MANIFEST_DIR is set by Cargo for build scripts"),
    );
    let verify_bundle_dir =
        manifest_dir.join("../../first-party/trust-wp/crates/trust-wp-core/src/verify_bundle");
    let result_rs = verify_bundle_dir.join("result.rs");
    let types_rs = verify_bundle_dir.join("types.rs");
    let proof_rs = verify_bundle_dir.join("proof.rs");
    let mod_rs = verify_bundle_dir.join("mod.rs");
    println!("cargo:rerun-if-changed={}", result_rs.display());
    println!("cargo:rerun-if-changed={}", types_rs.display());
    println!("cargo:rerun-if-changed={}", proof_rs.display());
    println!("cargo:rerun-if-changed={}", mod_rs.display());

    let verify_bundle_source = read_verify_bundle_sources(&verify_bundle_dir);
    let mod_source = fs::read_to_string(&mod_rs).unwrap_or_default();

    let Ok(result_source) = fs::read_to_string(&result_rs) else {
        return;
    };

    let has_transport_api = [
        "pub inline_bytes: Option<EvidenceArtifactBytes>",
        "pub fn with_utf8_bytes",
        "pub fn with_hex_bytes",
        "pub fn has_transport",
        "pub fn inline_bytes_digest_matches",
        "pub struct EvidenceArtifactBytes",
        "pub enum EvidenceArtifactBytesEncoding",
    ]
    .iter()
    .all(|needle| result_source.contains(needle));

    if has_transport_api {
        println!("cargo:rustc-cfg=trust_wp_proof_transport_api");
    }

    let Ok(types_source) = fs::read_to_string(&types_rs) else {
        return;
    };

    let has_structured_context_api = [
        "pub struct BundleNativeOrigin",
        "pub struct BundleTmirSourceSpan",
        "pub struct BundleNativeToolIdentity",
        "pub struct BundleNativeReplayIdentity",
        "pub struct BundleTmirObligationSource",
        "pub struct BundleTmirCompilerFactRef",
        "pub struct BundleProofContext",
        "pub struct BundleProofAtom",
        "pub fn with_tmir_source_span",
        "pub fn with_native_verifier",
        "pub fn with_native_replay",
        "pub fn with_native_solver",
        "pub fn with_tmir_obligation_source",
        "pub fn with_proof_context",
        "PointerProvenanceEqBinding",
        "PointerProvenanceDisjointBinding",
        "FatPointerMetadataEqBinding",
        "FatPointerMetadataDisjointBinding",
    ]
    .iter()
    .all(|needle| types_source.contains(needle));

    if has_structured_context_api {
        println!("cargo:rustc-cfg=trust_wp_structured_context_api");
    }

    let has_metadata_constants_api = [
        "TRUST_WP_NATIVE_ORIGIN_METADATA_KEY",
        "TRUST_WP_CLAIM_DIGEST_METADATA_KEY",
        "TRUST_WP_TMIR_SOURCE_SPAN_METADATA_KEY",
        "TRUST_WP_NATIVE_VERIFIER_METADATA_KEY",
        "TRUST_WP_NATIVE_REPLAY_METADATA_KEY",
        "TRUST_WP_NATIVE_SOLVER_METADATA_KEY",
        "TRUST_WP_TMIR_OBLIGATION_SOURCE_METADATA_KEY",
        "TRUST_WP_PROOF_CONTEXT_METADATA_KEY",
        "TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY",
    ]
    .iter()
    .all(|name| exported_from_verify_bundle(&mod_source, &verify_bundle_source, name));

    if has_metadata_constants_api {
        println!("cargo:rustc-cfg=trust_wp_metadata_constants_api");
    }

    let has_typed_metadata_helper_api = [
        "pub struct TrustWpNativeReplayEvidenceInput",
        "pub struct TrustWpMetadataEntry",
        "pub enum TrustWpNativeReplayMetadataError",
        "pub fn to_metadata_entries",
        "pub fn from_metadata_pairs",
        "pub fn apply_to_obligation",
    ]
    .iter()
    .all(|needle| verify_bundle_source.contains(needle))
        && exported_from_verify_bundle(
            &mod_source,
            &verify_bundle_source,
            "TrustWpNativeReplayEvidenceInput",
        );

    if has_typed_metadata_helper_api {
        println!("cargo:rustc-cfg=trust_wp_typed_metadata_helper_api");
    }

    let has_replay_helper_api = verify_bundle_source
        .contains("pub fn replay_verify_bundle_result_evidence")
        || verify_bundle_source.contains("replay_verify_bundle_result_evidence,");

    if has_replay_helper_api {
        println!("cargo:rustc-cfg=trust_wp_verify_bundle_replay_helper_api");
    }
}

fn read_verify_bundle_sources(dir: &PathBuf) -> String {
    let mut source = String::new();
    let Ok(entries) = fs::read_dir(dir) else {
        return source;
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().is_some_and(|extension| extension == "rs") {
            println!("cargo:rerun-if-changed={}", path.display());
            if let Ok(contents) = fs::read_to_string(&path) {
                source.push_str(&contents);
                source.push('\n');
            }
        }
    }

    source
}

fn exported_from_verify_bundle(mod_source: &str, all_source: &str, name: &str) -> bool {
    let direct_const = format!("pub const {name}");
    if mod_source.contains(&direct_const) {
        return true;
    }

    let mut in_pub_use = false;
    let mut block = String::new();
    for line in mod_source.lines() {
        if !in_pub_use && line.contains("pub use") {
            block.clear();
            in_pub_use = true;
        }
        if in_pub_use {
            block.push_str(line);
            block.push('\n');
            if line.contains(';') {
                if block.contains(name) {
                    return true;
                }
                in_pub_use = false;
            }
        }
    }

    mod_source.contains(&format!("pub use {name}"))
        || (mod_source.contains("pub use")
            && mod_source.contains("::*")
            && all_source.contains(&direct_const)
            && all_source.contains(name))
}
