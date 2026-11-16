// Trust: BUILD-time mathematical DATA staging. This module creates no proof authority.
use std::path::Path;

use serde_derive::Deserialize;

use crate::core::builder::Builder;
use crate::core::compiler::Compiler;
use crate::core::config::Vf5BaseInput;

const RESOURCE: &str = "lib/trust/vf5-base-v1";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PackagePin {
    manifest_sha256: String,
    environment_sha256: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ResourcePolicy {
    schema: u32,
    kind: String,
    production_pin_required: bool,
    allowed_packages: Vec<PackagePin>,
    production_admission: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct StageReport {
    manifest_sha256: String,
    modules: usize,
    files: usize,
    bytes: u64,
    reused: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct StageOutput {
    schema: u32,
    kind: String,
    report: StageReport,
    production_admission: bool,
}

fn valid_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

fn policy_allows(policy: &ResourcePolicy, configured: Option<&Vf5BaseInput>) -> Result<(), String> {
    if policy.schema != 1 || policy.kind != "vf5-resource-policy-v1" || policy.production_admission {
        return Err("invalid VF5 build-resource policy response".into());
    }
    if policy.production_pin_required == policy.allowed_packages.is_empty() {
        return Err("incoherent VF5 build-resource policy".into());
    }
    let mut manifests = std::collections::BTreeSet::new();
    for pin in &policy.allowed_packages {
        if !valid_digest(&pin.manifest_sha256) || !valid_digest(&pin.environment_sha256)
            || pin.manifest_sha256.bytes().all(|b| b == b'0')
            || pin.environment_sha256.bytes().all(|b| b == b'0')
            || !manifests.insert(&pin.manifest_sha256)
        {
            return Err("invalid or duplicate compiled VF5 resource association".into());
        }
    }
    if policy.production_pin_required {
        let input = configured.ok_or("compiled VF5 pins require build.vf5-base and build.vf5-base-sha256")?;
        if !policy.allowed_packages.iter().any(|pin| pin.manifest_sha256 == input.manifest_sha256) {
            return Err("configured VF5 manifest is absent from the compiler's compiled package/environment associations".into());
        }
    }
    Ok(())
}

// All parent creation/overlap checks belong to the descriptor-held host DATA
// seam. Bootstrap performs no filesystem writes before that admission.
fn stage(builder: &Builder<'_>, input: &Path, digest: &str, root: &Path) {
    let output = builder.vf5_resource_tool_cmd()
        .arg("stage-sysroot-resource").arg(input).arg(digest).arg(root)
        .run_capture_stdout(builder);
    let output: StageOutput = serde_json::from_str(output.stdout().trim())
        .unwrap_or_else(|error| panic!("invalid VF5 DATA copier response: {error}"));
    assert!(output.schema == 1 && output.kind == "vf5-resource-staging-v1"
        && !output.production_admission && output.report.manifest_sha256 == digest,
        "VF5 DATA copier response does not bind the requested manifest");
    builder.info(&format!("VF5 mathematical DATA: {} modules, {} files, {} bytes{} at {} (no proof authority)",
        output.report.modules, output.report.files, output.report.bytes,
        if output.report.reused { ", unchanged" } else { "" }, root.join(RESOURCE).display()));
}

fn configured_local_resource<'a>(builder: &'a Builder<'_>, target: Compiler) -> Option<&'a Vf5BaseInput> {
    if target.stage == 0 || target.is_forced_compiler() || builder.download_rustc() {
        assert!(builder.config.vf5_base.is_none(),
            "build.vf5-base cannot stage into an external, downloaded, forced, or stage0 compiler");
        return None;
    }
    builder.config.vf5_base.as_ref()
}

fn admit_configuration(builder: &Builder<'_>, input: Option<&Vf5BaseInput>) {
    // ToolBuild targets the BUILD host and uses the snapshot std. It never
    // ensures Assemble or executes the target compiler (including cross-host).
    let mut command = builder.vf5_resource_tool_cmd();
    command.arg("resource-policy");
    // The normal command API must consume the armed command in dry runs too.
    // It preserves tool discovery and suppresses execution through ExecutionContext.
    let output = command.run_capture_stdout(builder);
    if builder.config.dry_run() {
        return;
    }
    let policy: ResourcePolicy = serde_json::from_str(output.stdout().trim())
        .unwrap_or_else(|error| panic!("invalid compiled VF5 resource policy: {error}"));
    policy_allows(&policy, input).unwrap_or_else(|error| panic!("cannot stage VF5 resource: {error}"));
}

pub(crate) fn install_into_sysroot(
    builder: &Builder<'_>,
    build_compiler: Compiler,
    target_compiler: Compiler,
    sysroot: &Path,
) {
    let input = configured_local_resource(builder, target_compiler);
    if target_compiler.stage == 0 || target_compiler.is_forced_compiler() || builder.download_rustc() {
        return;
    }
    assert_eq!(build_compiler.host, builder.host_target,
        "VF5 resources must be prepared by the BUILD host");
    admit_configuration(builder, input);
    if builder.config.dry_run() { return; }
    if let Some(input) = input {
        stage(builder, &input.package, &input.manifest_sha256, sysroot);
    }
}

pub(crate) fn copy_into_dist(
    builder: &Builder<'_>,
    target_compiler: Compiler,
    source_sysroot: &Path,
    image: &Path,
) {
    let input = configured_local_resource(builder, target_compiler);
    if target_compiler.stage == 0 || target_compiler.is_forced_compiler() || builder.download_rustc() {
        return;
    }
    admit_configuration(builder, input);
    if builder.config.dry_run() { return; }
    if let Some(input) = input {
        // Re-read/hash the actual installed resource through the same private
        // descriptor copier; do not substitute the original input directory.
        stage(builder, &source_sysroot.join(RESOURCE), &input.manifest_sha256, image);
    }
}

#[cfg(test)]
mod tests;
