// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Build-host VF5 DATA policy and staging. The runtime base's immutable pin
//! associations are the sole policy source. No entry here imports a theorem,
//! constructs a reference kernel, or issues proof or execution authority.

use std::collections::BTreeSet;
use std::path::Path;

use serde::Serialize;

use super::{BasePin, PINNED_BASES};

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod held;

#[derive(Debug, Serialize)]
pub struct PackagePin {
    pub manifest_sha256: String,
    pub environment_sha256: String,
}

#[derive(Debug, Serialize)]
pub struct ResourcePolicy {
    pub schema: u32,
    pub kind: &'static str,
    pub production_pin_required: bool,
    pub allowed_packages: Vec<PackagePin>,
    pub production_admission: bool,
}

fn policy_for(pins: &[BasePin], environments: &[[u8; 32]]) -> Result<ResourcePolicy, String> {
    if pins.is_empty() != environments.is_empty() {
        return Err("incoherent compiled VF5 package/environment pin tables".into());
    }
    let unique_environments = environments.iter().copied().collect::<BTreeSet<_>>();
    if environments.contains(&[0; 32]) || unique_environments.len() != environments.len() {
        return Err("invalid compiled VF5 environment pin table".into());
    }
    let mut manifests = BTreeSet::new();
    let mut allowed_packages = Vec::new();
    for pin in pins {
        if pin.manifest_sha256 == [0; 32]
            || pin.environment_sha256 == [0; 32]
            || !manifests.insert(pin.manifest_sha256)
            || !environments.contains(&pin.environment_sha256)
        {
            return Err("invalid compiled VF5 package/environment association".into());
        }
        allowed_packages.push(PackagePin {
            manifest_sha256: hex(&pin.manifest_sha256),
            environment_sha256: hex(&pin.environment_sha256),
        });
    }
    Ok(ResourcePolicy {
        schema: 1,
        kind: "vf5-resource-policy-v1",
        production_pin_required: !pins.is_empty(),
        allowed_packages,
        production_admission: false,
    })
}

/// Describe the actual compiled runtime policy. There is no caller-supplied
/// table, environment variable, command option or persistent pin override.
pub fn resource_policy() -> Result<ResourcePolicy, String> {
    policy_for(PINNED_BASES, super::super::PINNED_VF5_ENV_DIGESTS)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[derive(Debug, Serialize)]
pub struct StageReport {
    pub manifest_sha256: String,
    pub modules: usize,
    pub files: usize,
    pub bytes: u64,
    pub reused: bool,
}

#[derive(Debug, Serialize)]
pub struct StageOutput {
    pub schema: u32,
    pub kind: &'static str,
    pub report: StageReport,
    pub production_admission: bool,
}

fn check_request(policy: &ResourcePolicy, manifest_sha256: &str) -> Result<(), String> {
    if !super::valid_digest(manifest_sha256)
        || manifest_sha256.bytes().all(|byte| byte == b'0')
    {
        return Err("invalid requested VF5 manifest digest".into());
    }
    if policy.production_pin_required
        && !policy.allowed_packages.iter().any(|pin| pin.manifest_sha256 == manifest_sha256)
    {
        return Err("requested VF5 manifest is absent from compiled production associations".into());
    }
    Ok(())
}

/// Validate a complete raw-manifest-bound DATA package and publish it at the
/// fixed sysroot resource location. Successful copying grants no math admission.
pub fn stage_sysroot_resource(
    package: &Path,
    manifest_sha256: &str,
    sysroot: &Path,
) -> Result<StageOutput, String> {
    let policy = resource_policy()?;
    check_request(&policy, manifest_sha256)?;
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (package, sysroot);
        Err("descriptor-held VF5 staging is unavailable on this platform".into())
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let report = held::stage(package, manifest_sha256, sysroot)?;
        Ok(StageOutput {
            schema: 1,
            kind: "vf5-resource-staging-v1",
            report,
            production_admission: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn policy_uses_both_runtime_tables_and_never_turns_bad_pins_off() {
        assert!(!policy_for(&[], &[]).unwrap().production_pin_required);
        let pins = [BasePin { manifest_sha256: [1; 32], environment_sha256: [2; 32] }];
        let on = policy_for(&pins, &[[2; 32]]).unwrap();
        assert!(on.production_pin_required);
        assert_eq!(on.allowed_packages[0].manifest_sha256, "01".repeat(32));
        assert!(!on.production_admission);
        assert!(check_request(&on, &"01".repeat(32)).is_ok());
        assert!(check_request(&on, &"03".repeat(32)).is_err());
        assert!(check_request(&on, &"00".repeat(32)).is_err());
        assert!(check_request(&on, "short").is_err());
        assert!(policy_for(&pins, &[]).is_err());
        assert!(policy_for(&[], &[[2; 32]]).is_err());
        assert!(policy_for(&pins, &[[3; 32]]).is_err());
        let duplicate = [
            BasePin { manifest_sha256: [1; 32], environment_sha256: [2; 32] },
            BasePin { manifest_sha256: [1; 32], environment_sha256: [2; 32] },
        ];
        assert!(policy_for(&duplicate, &[[2; 32]]).is_err());
        assert!(policy_for(&[BasePin {
            manifest_sha256: [0; 32], environment_sha256: [2; 32],
        }], &[[2; 32]]).is_err());
        assert!(policy_for(&[BasePin {
            manifest_sha256: [1; 32], environment_sha256: [0; 32],
        }], &[[0; 32]]).is_err());
    }

    #[test]
    fn real_policy_is_the_runtime_bases_exact_immutable_table() {
        let policy = resource_policy().unwrap();
        assert_eq!(policy.allowed_packages.len(), PINNED_BASES.len());
        assert_eq!(policy.production_pin_required, super::super::has_production_pin());
    }
}
