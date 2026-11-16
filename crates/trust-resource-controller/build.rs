// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Identify Trust's std before selecting its explicit descriptor-inheritance API.

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-env-changed=RUSTC");
    println!("cargo::rustc-check-cfg=cfg(trust_std)");
    // Pure data builds claim no native channel, compiled-image or client
    // authority. Preserve the existing native channel/server compiler probe.
    if std::env::var_os("CARGO_FEATURE_CLIENT").is_none()
        && std::env::var_os("CARGO_FEATURE_CHANNEL").is_none()
    {
        return;
    }
    let compiler = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    #[allow(
        unfulfilled_lint_expectations,
        reason = "this probe also builds outside consumers that ban std::process::Command"
    )]
    #[expect(
        clippy::disallowed_types,
        reason = "build-time compiler identity probe; never linked into the client"
    )]
    let mut probe = std::process::Command::new(compiler);
    let output = probe.arg("-vV").output().expect("read compiler identity");
    assert!(output.status.success(), "compiler identity probe failed");
    if output.stdout.split(|byte| *byte == b'\n').any(|line| line.starts_with(b"trust:")) {
        println!("cargo::rustc-cfg=trust_std");
    }
}
