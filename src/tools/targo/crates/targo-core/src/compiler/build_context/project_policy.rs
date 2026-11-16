//! Trust: read-only project requirements, resolved with Cargo's own config rules.
//! This query creates no Units and cannot supply activation or a proof session.

use super::target_info::{
    Flags, TargetInfo, host_artifact_uses_only_host_config, rustflags_from_build,
    rustflags_from_host, rustflags_from_target,
};
use crate::compiler::{CompileKind, CompileTarget, prefixed_compiler_options};
use crate::util::data_structures::HashSet;
use crate::util::process_authority::configure_verified_tool_loader_environment;
use crate::util::{CargoResult, GlobalContext, Rustc};
use anyhow::{Context as _, bail};
use cargo_platform::Cfg;
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum Policy {
    Strict,
    Certify,
    Advisory,
    MemorySafe,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum IrLower {
    Off,
    On,
    Strict,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct ProjectTrustPolicy {
    schema: &'static str,
    policy: Option<Policy>,
    level: Option<u8>,
    profile: Option<String>,
    include_dependencies: Option<bool>,
    ir_lower: Option<IrLower>,
    verification_required: bool,
}

impl Default for ProjectTrustPolicy {
    fn default() -> Self {
        Self {
            schema: "trust.project-policy.v1",
            policy: None,
            level: None,
            profile: None,
            include_dependencies: None,
            ir_lower: None,
            verification_required: false,
        }
    }
}

fn set<T: PartialEq>(slot: &mut Option<T>, value: T, name: &str) -> CargoResult<()> {
    if slot.as_ref().is_some_and(|previous| previous != &value) {
        bail!(
            "conflicting project Trust requirement -Z{name} between compiler/documentation scopes"
        );
    }
    *slot = Some(value);
    Ok(())
}

fn explicit_bool(value: &str) -> CargoResult<bool> {
    match value {
        "on" | "yes" | "true" | "y" => Ok(true),
        "off" | "no" | "false" | "n" => Ok(false),
        _ => bail!("project Trust requirement needs an explicit boolean, got `{value}`"),
    }
}

impl ProjectTrustPolicy {
    fn require_scope(&mut self, flags: &[String], scope: &str) -> CargoResult<()> {
        let options = prefixed_compiler_options(flags, "-Z").map_err(anyhow::Error::msg)?;
        let mut seen = HashSet::default();
        for (name, value) in options {
            if name == "contract_checks" {
                bail!("{scope} cannot use the retired -Zcontract-checks projection");
            }
            if !name.starts_with("trust_") && !name.starts_with("no_trust_") {
                continue;
            }
            if !seen.insert(name.clone()) {
                bail!("{scope} repeats project Trust requirement -Z{name}");
            }
            let value = value.as_deref().ok_or_else(|| {
                anyhow::anyhow!("{scope} requires an explicit value for -Z{name}")
            })?;
            match name.as_str() {
                "trust_policy" => {
                    let policy = match value {
                        "strict" => Policy::Strict,
                        "certify" => Policy::Certify,
                        "advisory" => Policy::Advisory,
                        "memory-safe" => Policy::MemorySafe,
                        _ => bail!("{scope} has invalid Trust policy `{value}`"),
                    };
                    set(&mut self.policy, policy, &name)?;
                }
                "trust_verify_level" => {
                    let level = value
                        .parse::<u8>()
                        .context("invalid project verification level")?;
                    if level > 2 {
                        bail!("{scope} verification level must be 0, 1, or 2");
                    }
                    set(&mut self.level, level, &name)?;
                }
                "trust_verify_profile" => {
                    if value.is_empty() || value.len() > 128 {
                        bail!("{scope} has an empty or oversized Trust profile");
                    }
                    set(&mut self.profile, value.to_string(), &name)?;
                }
                "trust_verify_include_dependencies" => {
                    set(&mut self.include_dependencies, explicit_bool(value)?, &name)?;
                }
                "trust_ir_lower" => {
                    let lower = if value == "strict" {
                        IrLower::Strict
                    } else if explicit_bool(value)? {
                        IrLower::On
                    } else {
                        IrLower::Off
                    };
                    set(&mut self.ir_lower, lower, &name)?;
                }
                "trust_verify" if explicit_bool(value)? => self.verification_required = true,
                _ => bail!(
                    "{scope} cannot supply -Z{name}: project configuration supplies requirements, \
                     not activation, session, unit-role, or proof-output authority"
                ),
            }
        }
        Ok(())
    }
}

// Trust (T14a): the query selects `[target.'cfg(..)']` tables with the cfg set
// the build selects them with: `TargetInfo`'s own fixed point over the
// project's resolved flags and the lane targo trust hands the query (with
// every `-Ztrust-*` token stripped from the probe, and the lane's backend,
// plugin and LLVM-argument ownership applied), not the environment's flags
// alone. The configured flags inspected below are data and are never executed
// here.
fn target_cfg(
    gctx: &GlobalContext,
    rustc: &Rustc,
    requested: &[CompileKind],
    kind: CompileKind,
) -> CargoResult<Vec<Cfg>> {
    if matches!(kind, CompileKind::Target(CompileTarget::Json { .. })) {
        bail!("project Trust policy resolution requires a compiler built-in target");
    }
    if let CompileKind::Target(target) = kind {
        let mut command = rustc.process_no_wrapper();
        configure_verified_tool_loader_environment(&mut command, &rustc.path)?;
        let output = command
            .arg("--print=target-list")
            .env_remove("RUST_TARGET_PATH")
            .exec_with_output()?;
        let builtins = String::from_utf8(output.stdout)?;
        if !builtins.lines().any(|line| line == target.short_name()) {
            bail!(
                "project Trust policy target is not in the selected compiler's built-in inventory"
            );
        }
    }
    Ok(TargetInfo::new(gctx, requested, rustc, kind)
        .context("project policy target cfg query failed")?
        .cfg()
        .to_vec())
}

fn configured_scope(
    gctx: &GlobalContext,
    requested: &[CompileKind],
    host_triple: &str,
    cfg: &[Cfg],
    kind: CompileKind,
    flags: Flags,
) -> CargoResult<Vec<String>> {
    if host_artifact_uses_only_host_config(gctx, requested, kind)? {
        return Ok(rustflags_from_host(gctx, flags, host_triple)?.unwrap_or_default());
    }
    if let Some(flags) = rustflags_from_target(gctx, host_triple, Some(cfg), kind, flags)? {
        return Ok(flags);
    }
    Ok(rustflags_from_build(gctx, flags)?.unwrap_or_default())
}

// The query has no verified session to import. Require the same OS-branded
// sibling pair explicitly, with empty wrapper overrides, before the version
// probe. Source [env] and startup loader admission use the existing Targo
// authority checks; neither sets the verified activation marker.
fn admit_policy_query_compiler(gctx: &GlobalContext) -> CargoResult<()> {
    let frontend = crate::authenticated_targo_path()
        .map_err(anyhow::Error::msg)?
        .ok_or_else(|| {
            anyhow::anyhow!("project policy query has no authenticated sibling Targo")
        })?;
    crate::validate_verified_targo_startup_loader_environment().map_err(anyhow::Error::msg)?;
    gctx.env_config()?;
    let compiler_name = if cfg!(windows) {
        "trustc.exe"
    } else {
        "trustc"
    };
    let sibling = frontend
        .parent()
        .ok_or_else(|| anyhow::anyhow!("Targo has no tool directory"))?
        .join(compiler_name);
    let expected = std::fs::canonicalize(&sibling)?;
    for name in ["RUSTC", "CARGO_BUILD_RUSTC"] {
        let selected = gctx
            .get_env_os(name)
            .ok_or_else(|| anyhow::anyhow!("project policy query requires pinned {name}"))?;
        if std::fs::canonicalize(std::path::Path::new(&selected))? != expected {
            bail!("project policy query {name} is not the authenticated sibling trustc");
        }
    }
    for name in [
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        if !gctx.get_env_os(name).is_some_and(|value| value.is_empty()) {
            bail!("project policy query requires an explicit empty {name}");
        }
    }
    Ok(())
}

pub(crate) fn resolve_project_trust_policy(
    gctx: &GlobalContext,
    targets: &[String],
) -> CargoResult<ProjectTrustPolicy> {
    admit_policy_query_compiler(gctx)?;
    let requested = CompileKind::from_requested_targets(gctx, targets)?;
    if requested.len() != 1 {
        bail!("project Trust policy needs exactly one effective compile target");
    }
    let rustc = gctx.load_global_rustc(None)?;
    let mut policy = ProjectTrustPolicy::default();
    for kind in [CompileKind::Host, requested[0]] {
        let cfg = target_cfg(gctx, &rustc, &requested, kind)?;
        for flags in [Flags::Rust, Flags::Rustdoc] {
            let scope = configured_scope(gctx, &requested, &rustc.host, &cfg, kind, flags)?;
            policy.require_scope(&scope, &format!("{kind:?} {flags:?}"))?;
        }
    }
    Ok(policy)
}

#[cfg(test)]
#[path = "project_policy_tests.rs"]
mod tests;
