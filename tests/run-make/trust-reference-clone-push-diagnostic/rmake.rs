// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Observe the real producer's reference-read/Clone/Vec::push typing frontier.
//! A passing diagnostic test means its compilations and publication/refusal
//! consistency checks ran. It does not mean every case lowered or validated,
//! nor identify the production Clean capture's unpublished struct IDs.
//! Scalar and enum-field registration paths remain separately observed cases.
//@ ignore-cross-compile
//@ only-apple

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

fn main() {
    let mut observations = Vec::new();
    for case in [
        "reference_first",
        "no_preread",
        "by_value",
        "pure_payload",
        "enum_reference_first",
    ] {
        rfs::create_dir(case);
        let binary = format!("{case}/clone_push.trust-ir.bin");
        let text = format!("{case}/clone_push.trust-ir.txt");
        let coverage = format!("{case}/clone_push.trust-ir.coverage.json");
        let compiler = rustc()
            .input("subject.rs")
            .edition("2024")
            .crate_type("lib")
            .crate_name("clone_push")
            .cfg(case)
            .arg("-Copt-level=3")
            .arg("-Cpanic=abort")
            .arg("-Cdebug-assertions=off")
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-ir-lower=on")
            .arg(format!("--emit=metadata,trust-ir={binary}"))
            .arg("-o")
            .arg(format!("{case}/clone_push.rmeta"))
            .run_unchecked();
        rfs::write(format!("{case}/compiler.stdout"), compiler.stdout());
        rfs::write(format!("{case}/compiler.stderr"), compiler.stderr());
        let status = compiler.status().code();
        rfs::write(format!("{case}/compiler.exit"), format!("{status:?}\n"));
        // These are ordinary valid Rust programs in an explicitly unverified
        // diagnostic lane. A compiler failure is still preserved before refusal.
        assert_eq!(status, Some(0), "native compiler failed for {case}");
        assert!(!rfs::read(format!("{case}/clone_push.rmeta")).is_empty());
        let stderr = compiler.stderr_utf8();
        let semantic_refusal = stderr.contains("trust-ir-lower semantic finalization failed:");
        let mut sizes = Vec::new();
        for artifact in [&binary, &text, &coverage] {
            if semantic_refusal {
                assert!(!Path::new(artifact).exists(), "invalid module published {artifact}");
            } else {
                let bytes = rfs::read(artifact);
                assert!(!bytes.is_empty(), "missing/empty published artifact: {artifact}");
                sizes.push(bytes.len());
            }
        }
        if !semantic_refusal {
            let value: serde_json::Value = serde_json::from_slice(&rfs::read(&coverage))
                .expect("published coverage is JSON");
            assert_eq!(value["schema"], "trust.thir-lower.crate-module.coverage.v2");
            assert_eq!(value["crate"], "clone_push");
            assert_eq!(value["proof_authority"], false);
            assert_eq!(value["native_verification_requests"], false);
            assert_eq!(value["publication"]["commit_marker"], true);
        }
        observations.push(serde_json::json!({
            "case": case,
            "compiler_exit": status,
            "semantic_finalization_refused": semantic_refusal,
            "call_argument_type_mismatches": stderr.matches("[CallArgTypeMismatch]").count(),
            "published": !semantic_refusal,
            "artifact_sizes": sizes,
            "proof_authority": false,
            "production_clean_source_capture": false,
        }));
    }
    rfs::write(
        "observations.json",
        serde_json::to_vec_pretty(&observations).expect("diagnostic observations serialize"),
    );
}

/// Execute the same maintained recipe under libtest with externally fixed env/cwd.
#[test]
fn actual_reference_clone_push_diagnostic_runs() {
    assert!(cfg!(all(target_vendor = "apple", target_arch = "aarch64")));
    assert_eq!(std::env::var("HOST").as_deref(), Ok("aarch64-apple-darwin"));
    assert_eq!(std::env::var("TARGET").as_deref(), Ok("aarch64-apple-darwin"));
    let compiled_subject = include_bytes!("subject.rs");
    assert_eq!(rfs::read("subject.rs").as_slice(), compiled_subject.as_slice());
    main();
    assert_eq!(rfs::read("subject.rs").as_slice(), compiled_subject.as_slice());
}
