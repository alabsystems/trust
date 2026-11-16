//! Checked project requirements precede lane selection, banners, and sessions.
//! The authenticated sibling Targo owns Cargo config precedence and cfg matching.
//! Requirements are not compiler activation, a proof session, or unit authority.

use std::path::Path;
use std::time::{Duration, Instant};

use serde::{Deserialize, Deserializer};

use super::backend::{canonical_rustc_option_name, cfg_probe_lane_rustflags};
use super::cargo_selection::{
    CargoSelectionArgs, effective_cargo_target_with_targo_until, export_cfg_probe_lane,
    selection_probe_command,
};
use super::discovery::native_trust_cargo_path;
use crate::bounded_process;
use crate::cli::SubcommandArgs;
use crate::config::TrustConfig;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ProjectPolicy {
    Strict,
    Certify,
    Advisory,
    MemorySafe,
}

impl ProjectPolicy {
    fn name(self) -> &'static str {
        match self {
            Self::Strict => "strict",
            Self::Certify => "certify",
            Self::Advisory => "advisory",
            Self::MemorySafe => "memory-safe",
        }
    }

    /// The command-line spelling that selects this policy's lane, for a
    /// policy weaker than the strict default. `None` for strict and certify,
    /// which a project may require without the invocation restating them:
    /// adopting either can only make the gate stricter.
    fn loosening_cli_flag(self) -> Option<&'static str> {
        match self {
            Self::Strict | Self::Certify => None,
            Self::Advisory => Some("--allow-l0-gaps (or --survey)"),
            Self::MemorySafe => Some("--memory-safe"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ProjectIrLower {
    Off,
    On,
    Strict,
}

impl ProjectIrLower {
    fn rank(self) -> u8 {
        match self {
            Self::Off => 0,
            Self::On => 1,
            Self::Strict => 2,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::On => "on",
            Self::Strict => "strict",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ProjectTrustPolicy {
    schema: String,
    #[serde(deserialize_with = "required_optional")]
    policy: Option<ProjectPolicy>,
    #[serde(deserialize_with = "required_optional")]
    level: Option<u8>,
    #[serde(deserialize_with = "required_optional")]
    profile: Option<String>,
    #[serde(deserialize_with = "required_optional")]
    include_dependencies: Option<bool>,
    #[serde(deserialize_with = "required_optional")]
    ir_lower: Option<ProjectIrLower>,
    // A positive assertion constrains a verified invocation. It is deliberately
    // never emitted as an activation flag; the existing session/Unit owner does that.
    verification_required: bool,
}

fn required_optional<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

impl ProjectTrustPolicy {
    pub(crate) fn parse(bytes: &[u8]) -> Result<Self, String> {
        let policy: Self = serde_json::from_slice(bytes)
            .map_err(|error| format!("invalid sibling Targo project-policy response: {error}"))?;
        if policy.schema != "trust.project-policy.v1" || policy.level.is_some_and(|level| level > 2)
        {
            return Err("unsupported project-policy schema or verification level".to_string());
        }
        if let Some(profile) = &policy.profile {
            if profile != "default"
                && trust_vcgen::canonical_profile(profile) != Some(profile.as_str())
            {
                return Err(format!(
                    "project requires unregistered or noncanonical Trust profile `{profile}`"
                ));
            }
        }
        Ok(policy)
    }

    pub(crate) fn adopt(
        &self,
        args: &mut SubcommandArgs,
        config: &mut TrustConfig,
    ) -> Result<(), String> {
        if self.verification_required && (args.standalone || args.is_single_file) {
            return Err("Cargo project verification requirement cannot be discharged by a standalone/direct audit".to_string());
        }
        if let Some(policy) = self.policy {
            let explicit = if args.certify {
                Some(ProjectPolicy::Certify)
            } else if args.memory_safe {
                Some(ProjectPolicy::MemorySafe)
            } else if args.survey || args.allow_l0_gaps {
                Some(ProjectPolicy::Advisory)
            } else {
                None
            };
            if explicit.is_some_and(|selected| selected != policy) {
                return Err(format!(
                    "explicit CLI lane conflicts with project Trust policy `{}`",
                    policy.name()
                ));
            }
            // A project file may tighten the lane (certify) but never loosen
            // it behind the invocation: a plain `targo trust check` asks for
            // the strict gate. A Cargo config `-Ztrust-policy=advisory` used
            // to replace it with nothing naming the config: refutations became
            // warnings and the crate compiled, the gate read `[advisory lane]`
            // exactly as if `--allow-l0-gaps` had been typed, and under the
            // advisory exit contract an unproved obligation exits 0 where
            // strict exits 1 (DECISION_QUEUE "Project policy cannot loosen the
            // lane — 2026-10-07"). The lane that grades a run is chosen on
            // the command line, so a weaker project policy needs that lane's
            // own flag.
            if let (None, Some(flag)) = (explicit, policy.loosening_cli_flag()) {
                return Err(format!(
                    "Cargo project configuration requires Trust policy `{}`, which is weaker \
                     than this invocation's strict lane; project configuration may tighten the \
                     lane but cannot loosen it. Pass {flag} to run the `{}` lane the project \
                     asks for, or remove -Ztrust-policy={} from the project's Cargo \
                     configuration",
                    policy.name(),
                    policy.name(),
                    policy.name()
                ));
            }
        }
        if let Some(level) = self.level {
            if config.level_declared && config.level != format!("L{level}") {
                return Err(
                    "manifest verification level conflicts with Cargo project requirements"
                        .to_string(),
                );
            }
        }
        if let Some(profile) = &self.profile {
            let hardened = profile != "default";
            if args.hardened_override.is_some_and(|selected| selected != hardened)
                || config.hardened.is_some_and(|selected| selected != hardened)
                || args.trust_profile.as_ref().is_some_and(|selected| selected != profile)
                || config.trust_profile.as_ref().is_some_and(|selected| selected != profile)
            {
                return Err(format!(
                    "CLI/manifest hardened profile conflicts with project requirement `{profile}`"
                ));
            }
        }
        // The policy rule above, for every other requirement key: a project
        // value weaker than what this invocation would otherwise run refuses,
        // unless this run selects it itself (DECISION_QUEUE "Project policy
        // cannot loosen the lane — 2026-10-07").
        self.refuse_loosening_requirements(args, config)?;
        if let Some(policy) = self.policy {
            args.certify = policy == ProjectPolicy::Certify;
            args.memory_safe = policy == ProjectPolicy::MemorySafe;
            if !args.survey {
                args.allow_l0_gaps = policy == ProjectPolicy::Advisory;
            }
        }
        if let Some(level) = self.level {
            config.level = format!("L{level}");
        }
        if let Some(profile) = &self.profile {
            let hardened = profile != "default";
            config.hardened = Some(hardened);
            config.trust_profile = hardened.then(|| profile.clone());
            args.hardened = hardened;
            args.trust_profile = config.trust_profile.clone();
        }
        config.project_policy = Some(self.clone());
        Ok(())
    }

    /// Refuse a level, profile or lowering requirement that is weaker than the
    /// value this invocation resolves without the project file, unless the run
    /// selects that value itself: the CLI (`--no-hardened`, `--trust-profile`)
    /// or the `[trust]` table, which the invocation value already reflects.
    /// Stronger and equal requirements pass; they can only tighten the run.
    ///
    /// Since T7a (DECISION_QUEUE, 2026-10-11) no environment channel selects a
    /// value for one run: TRUSTFLAGS is ignored with a notice. So the
    /// invocation's dependency scope is always the compiler default (`no`),
    /// which no project value narrows, and its lowering is always `on`, so a
    /// project `-Ztrust-ir-lower=off` refuses with no per-run selection.
    fn refuse_loosening_requirements(
        &self,
        args: &SubcommandArgs,
        config: &TrustConfig,
    ) -> Result<(), String> {
        let refuse = |requirement: String, invocation: String, select: &str| {
            Err(format!(
                "Cargo project configuration requires {requirement}, which is weaker than this \
                 invocation's {invocation}; project configuration may tighten the run but cannot \
                 loosen it. To run it anyway, select it for this run with {select}, or remove \
                 it from the project's Cargo configuration"
            ))
        };
        if let Some(level) = self.level {
            let invocation = config
                .level
                .strip_prefix('L')
                .and_then(|level| level.parse::<u8>().ok())
                .ok_or_else(|| {
                    format!("unrecognized resolved verification level `{}`", config.level)
                })?;
            if level < invocation {
                return refuse(
                    format!("-Ztrust-verify-level={level}"),
                    format!("level L{invocation}"),
                    &format!("`level = \"L{level}\"` in the [trust] table"),
                );
            }
        }
        if let Some(profile) = &self.profile {
            let invocation = invocation_profile(args, config);
            let required = (profile != "default").then_some(profile.as_str());
            if invocation.as_deref() != required && invocation.is_some() {
                let invocation = invocation.unwrap_or_default();
                let select = if required.is_none() {
                    "--no-hardened (or `hardened = false` in the [trust] table)".to_string()
                } else {
                    format!(
                        "--trust-profile {profile} (or `trust_profile = \"{profile}\"` in the \
                         [trust] table)"
                    )
                };
                // A different hardened profile is not known to be stronger:
                // fail closed and treat it as a loosening.
                return refuse(
                    format!("-Ztrust-verify-profile={profile}"),
                    format!("hardened profile `{invocation}`"),
                    &select,
                );
            }
        }
        if let Some(lower) = self.ir_lower {
            // Unset lowering under verification is `on` (the compiler's
            // `trust_ir_lower_enabled_by_flags`), and no run selects another.
            if lower.rank() < ProjectIrLower::On.rank() {
                return Err(format!(
                    "Cargo project configuration requires -Ztrust-ir-lower={}, which is weaker \
                     than this invocation's Trust-IR lowering `on`; project configuration may \
                     tighten the run but cannot loosen it, and no per-run selection lowers it: \
                     remove it from the project's Cargo configuration",
                    lower.name()
                ));
            }
        }
        Ok(())
    }

    /// The adopted requirements, for the setup line and the published report.
    /// `None` when the project set none.
    pub(crate) fn report(&self) -> Option<trust_types::ProjectRequirementsReport> {
        let report = trust_types::ProjectRequirementsReport {
            policy: self.policy.map(|policy| policy.name().to_string()),
            level: self.level.map(|level| format!("L{level}")),
            profile: self.profile.clone(),
            include_dependencies: self.include_dependencies,
            ir_lower: self.ir_lower.map(|lower| lower.name().to_string()),
            verification_required: self.verification_required,
        };
        (!report.items().is_empty()).then_some(report)
    }

    /// The setup line naming every requirement Cargo configuration supplied
    /// and this run adopted, printed before any banner or compile. `None`
    /// when the project set none.
    pub(crate) fn disclosure(&self) -> Option<String> {
        self.report().map(|report| {
            format!(
                "Cargo project configuration requirements adopted for this run: {}",
                report.items().join(", ")
            )
        })
    }

    pub(crate) fn options(&self) -> Vec<(&'static str, String)> {
        let mut options = Vec::new();
        if let Some(policy) = self.policy {
            options.push(("trust-policy", policy.name().to_string()));
        }
        if let Some(level) = self.level {
            options.push(("trust-verify-level", level.to_string()));
        }
        if let Some(profile) = &self.profile {
            options.push(("trust-verify-profile", profile.clone()));
        }
        if let Some(include) = self.include_dependencies {
            options.push((
                "trust-verify-include-dependencies",
                if include { "yes" } else { "no" }.to_string(),
            ));
        }
        if let Some(lower) = self.ir_lower {
            options.push(("trust-ir-lower", lower.name().to_string()));
        }
        options
    }
}

/// The hardened profile this invocation resolves without project
/// requirements (`None` = not hardened), mirroring
/// `apply_configured_trust_profile`.
fn invocation_profile(args: &SubcommandArgs, config: &TrustConfig) -> Option<String> {
    let canonical = |profile: &str| {
        trust_vcgen::canonical_profile(profile).map_or_else(|| profile.to_string(), str::to_string)
    };
    match args.hardened_override {
        Some(false) => None,
        Some(true) => Some(canonical(
            args.trust_profile.as_deref().unwrap_or(crate::config::DEFAULT_TRUST_PROFILE),
        )),
        None if config.hardened == Some(false) => None,
        None => Some(canonical(
            config
                .trust_profile
                .as_deref()
                .filter(|profile| !profile.trim().is_empty())
                .unwrap_or(crate::config::DEFAULT_TRUST_PROFILE),
        )),
    }
}

/// The options the adopted project requirements put on a verified compile.
///
/// Cargo configuration states requirements as rustflags (the project-policy
/// query reads the committed `.cargo/config.toml` and a run's `--config`).
/// Since T14a those configured rustflags reach the compile too, where a
/// `-Ztrust-*` token is only an assertion the sibling Targo checks against the
/// lane, so targo carries the adopted requirements to the compiler itself:
/// merged LAST into the lane (crate mode) or a direct compiler's argv,
/// replacing any earlier spelling of the same option. The lane is part of every
/// unit's flags, which Cargo fingerprints, so a changed requirement
/// re-verifies. This is the only route a tightening such as
/// `-Ztrust-verify-include-dependencies=yes` or `-Ztrust-ir-lower=strict`
/// takes to the compiler (determinism plan §3.6; DECISION_QUEUE T7a).
#[derive(Debug, Clone, Default)]
pub(crate) struct ProjectRequirementFlags {
    options: Vec<String>,
}

impl ProjectRequirementFlags {
    /// This run's requirement options, refused when one disagrees with the
    /// lane, hardened profile or level the run resolved. Adoption makes them
    /// agree ([`ProjectTrustPolicy::adopt`] sets the lane, level and profile
    /// it requires), so a disagreement means a run reached the compiler
    /// without adopting them: compiling it would publish a gate verdict for a
    /// compile that ran under another policy than the one the report names.
    ///
    /// `lane_policy` is the compiler policy the CLI lane selects (`strict`,
    /// `certify`, `advisory` or `memory-safe`), `resolved_profile` the hardened
    /// profile the run names (`None`: not hardened) and `resolved_level` the
    /// numeric level it passes the compiler.
    pub(crate) fn for_run(
        policy: Option<&ProjectTrustPolicy>,
        lane_policy: &str,
        resolved_profile: Option<&str>,
        resolved_level: u8,
    ) -> Result<Self, String> {
        let Some(policy) = policy else {
            return Ok(Self::default());
        };
        let mut options = Vec::new();
        for (name, required) in policy.options() {
            let agrees = match name {
                "trust-policy" => required == lane_policy,
                "trust-verify-profile" => {
                    Some(required.as_str()) == resolved_profile
                        || (required == "default" && resolved_profile.is_none())
                }
                "trust-verify-level" => required == resolved_level.to_string(),
                _ => true,
            };
            if !agrees {
                let resolved = match name {
                    "trust-policy" => format!("the `{lane_policy}` lane"),
                    "trust-verify-profile" => resolved_profile.map_or_else(
                        || "no hardened profile".to_string(),
                        |profile| format!("the `{profile}` hardened profile"),
                    ),
                    _ => format!("level L{resolved_level}"),
                };
                return Err(format!(
                    "Cargo project configuration requires -Z{name}={required}, but this run \
                     resolved {resolved}: the requirement was not adopted for this run, and \
                     compiling under it would publish a verdict for a run the report does not \
                     name"
                ));
            }
            options.push(format!("{name}={required}"));
        }
        Ok(Self { options })
    }

    /// The requirement option payloads (e.g. `trust-ir-lower=strict`).
    #[cfg(test)]
    pub(crate) fn options(&self) -> &[String] {
        &self.options
    }

    /// Merge into an assembled rustc argument vector: remove every existing
    /// spelling of a required option, then append the requirement.
    pub(crate) fn apply_to_args(&self, args: &mut Vec<String>) {
        if self.options.is_empty() {
            return;
        }
        let required = self
            .options
            .iter()
            .map(|option| canonical_rustc_option_name(option).into_owned())
            .collect::<std::collections::HashSet<_>>();
        let is_required =
            |option: &str| required.contains(canonical_rustc_option_name(option).as_ref());
        let mut merged = Vec::with_capacity(args.len() + 2 * self.options.len());
        let mut index = 0;
        while index < args.len() {
            if args[index] == "-Z" && args.get(index + 1).is_some_and(|option| is_required(option))
            {
                index += 2;
                continue;
            }
            if args[index]
                .strip_prefix("-Z")
                .filter(|option| !option.is_empty())
                .is_some_and(is_required)
            {
                index += 1;
                continue;
            }
            merged.push(args[index].clone());
            index += 1;
        }
        for option in &self.options {
            merged.push("-Z".to_string());
            merged.push(option.clone());
        }
        *args = merged;
    }
}

/// One setup allowance for paired discovery, config lookup, cfg query, and
/// policy recheck. It stays subordinate to the invocation's external owner;
/// it does not create or renew a verification/compilation allowance.
pub(crate) fn setup_deadline() -> Result<Instant, String> {
    Instant::now()
        .checked_add(bounded_process::resolve_probe_deadline(Duration::from_secs(30)))
        .ok_or_else(|| "project-policy setup deadline overflow".to_string())
}

pub(super) fn remaining(deadline: Instant) -> Result<Duration, String> {
    deadline
        .checked_duration_since(Instant::now())
        .filter(|left| !left.is_zero())
        .ok_or_else(|| "original project-policy setup deadline expired".to_string())
}

pub(crate) fn resolve_project_policy(
    args: &SubcommandArgs,
    config: &TrustConfig,
    rustc: &Path,
    deadline: Instant,
) -> Result<ProjectTrustPolicy, String> {
    remaining(deadline)?;
    let mut command = project_policy_query_command(args, config, rustc, deadline)?;
    let output = bounded_process::output_with_exact_deadline(
        &mut command,
        "authenticated sibling Targo project-policy query",
        1024 * 1024,
        remaining(deadline)?,
    )?;
    if !output.status.success() {
        return Err(format!(
            "sibling Targo project-policy resolution refused: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let policy = ProjectTrustPolicy::parse(&output.stdout)?;
    remaining(deadline)?;
    Ok(policy)
}

/// The sibling Targo's `config trust-policy` query, ready to spawn.
///
/// Targo admits that query only from a process whose dynamic-loader search path
/// is exactly the one it reconstructs from its authenticated sibling toolchain,
/// with no other loader variable set (`admit_policy_query_compiler` ->
/// `validate_verified_targo_startup_loader_environment`). Every other start of a
/// sibling tool gets that value from `apply_native_runtime_env`, and so does
/// this one. Without it a toolchain whose `lib/` holds the compiler's runtime
/// libraries — every sealed one — refused every `targo trust` run before it
/// compiled anything: "verified Targo startup is missing targo-trust's
/// reconstructed `DYLD_LIBRARY_PATH` runtime path" (measured 2026-10-04 on
/// macOS, on the seal of 62f89f111a and a one-function crate; the same seal
/// verified that crate once the path was given).
fn project_policy_query_command(
    args: &SubcommandArgs,
    config: &TrustConfig,
    rustc: &Path,
    deadline: Instant,
) -> Result<std::process::Command, String> {
    let cargo_args = args.crate_mode_cargo_args();
    let selection = CargoSelectionArgs::parse(&cargo_args)?;
    let targo = native_trust_cargo_path(rustc)?;
    let mut command = selection_probe_command(&targo, rustc, &cargo_args)?;
    let mut query_args = selection.project_policy_query_args();
    let backend = args
        .backend
        .as_deref()
        .or(config.codegen_backend.as_deref())
        .unwrap_or(crate::config::DEFAULT_CODEGEN_BACKEND);
    // Match compile_command's existing Trust-CG native-target insertion: the
    // implicit explicit target changes Cargo's isolated host configuration.
    if backend == "trust-cg"
        && effective_cargo_target_with_targo_until(&cargo_args, &targo, rustc, deadline)?.is_none()
    {
        query_args.extend([
            "--target".to_string(),
            super::run::exact_rustc_host_triple_until(rustc, deadline)?,
        ]);
    }
    command.args(query_args);
    // Config inspection never joins or grants a verified compilation session.
    command.env_remove("TRUST_TARGO_VERIFY").env_remove("TRUST_TARGO_FRONTEND");
    export_cfg_probe_lane(
        &mut command,
        &cfg_probe_lane_rustflags(Some(backend), args.strict_artifact_policy()),
    )?;
    // The one loader search path the sibling toolchain authenticates, and no
    // ambient loader authority (see the doc comment above).
    super::apply_native_runtime_env(&mut command, rustc);
    Ok(command)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::parse_subcommand_args;

    fn policy() -> ProjectTrustPolicy {
        ProjectTrustPolicy::parse(br#"{"schema":"trust.project-policy.v1","policy":"certify","level":2,"profile":"unix_hardened","include_dependencies":true,"ir_lower":"strict","verification_required":true}"#).unwrap()
    }

    #[test]
    fn plain_required_lane_adopts_complete_project_before_session() {
        let mut args = parse_subcommand_args(&[]).unwrap();
        let mut config = TrustConfig::default();
        policy().adopt(&mut args, &mut config).unwrap();
        assert!(args.certify_lane());
        assert!(args.strict_artifact_policy());
        assert_eq!(config.level, "L2");
        assert_eq!(args.trust_profile.as_deref(), Some("unix_hardened"));
        let flags = ProjectRequirementFlags::for_run(
            config.project_policy.as_ref(),
            "certify",
            args.trust_profile.as_deref(),
            2,
        )
        .unwrap();
        assert!(flags.options().contains(&"trust-verify-include-dependencies=yes".to_string()));
        assert!(flags.options().contains(&"trust-ir-lower=strict".to_string()));
        assert!(
            !flags
                .options()
                .iter()
                .any(|option| canonical_rustc_option_name(option) == "trust-verify")
        );
    }

    #[test]
    fn cli_lane_profile_and_manifest_level_conflicts_refuse() {
        for values in [
            vec!["--allow-l0-gaps".to_string()],
            vec!["--memory-safe".to_string()],
            vec!["--survey".to_string()],
            vec!["--no-hardened".to_string()],
        ] {
            let mut args = parse_subcommand_args(&values).unwrap();
            assert!(policy().adopt(&mut args, &mut TrustConfig::default()).is_err(), "{values:?}");
        }
        let mut args = parse_subcommand_args(&[]).unwrap();
        let mut config =
            TrustConfig { level: "L1".to_string(), level_declared: true, ..TrustConfig::default() };
        assert!(policy().adopt(&mut args, &mut config).is_err());
        assert!(!args.certify);
    }

    fn lane_policy(name: &str) -> ProjectTrustPolicy {
        ProjectTrustPolicy::parse(
            format!(
                r#"{{"schema":"trust.project-policy.v1","policy":"{name}","level":null,"profile":null,"include_dependencies":null,"ir_lower":null,"verification_required":false}}"#
            )
            .as_bytes(),
        )
        .unwrap()
    }

    fn adopt(policy: &ProjectTrustPolicy, cli: &[&str]) -> Result<SubcommandArgs, String> {
        let cli = cli.iter().map(|arg| arg.to_string()).collect::<Vec<_>>();
        let mut args = parse_subcommand_args(&cli).unwrap();
        let mut config = TrustConfig::default();
        policy.adopt(&mut args, &mut config)?;
        assert_eq!(config.project_policy.as_ref(), Some(policy));
        Ok(args)
    }

    /// DECISION_QUEUE "Project policy cannot loosen the lane — 2026-10-07".
    /// Measured before the fix on the stage-1 targo of 2a12d26fe: a target
    /// `-Ztrust-policy=advisory` turned a plain `targo trust check` into the
    /// advisory lane with nothing naming the config. A weaker project policy
    /// now refuses a plain (strict-default) invocation and names the flag that
    /// selects its lane, and the refusal leaves the lane untouched.
    #[test]
    fn weaker_project_policy_refuses_a_plain_invocation() {
        for (name, flag) in [("advisory", "--allow-l0-gaps"), ("memory-safe", "--memory-safe")] {
            for cli in [&[][..], &["--strict"][..]] {
                let policy = lane_policy(name);
                let mut args = parse_subcommand_args(
                    &cli.iter().map(|arg| arg.to_string()).collect::<Vec<_>>(),
                )
                .unwrap();
                let mut config = TrustConfig::default();
                let error = policy
                    .adopt(&mut args, &mut config)
                    .expect_err("a project file cannot loosen the strict lane");
                assert!(error.contains(&format!("requires Trust policy `{name}`")), "{error}");
                assert!(error.contains("cannot loosen"), "{error}");
                assert!(error.contains(flag), "{error}");
                assert!(!args.allow_l0_gaps && !args.memory_safe && !args.certify, "{name}");
                assert!(args.strict_artifact_policy(), "{name}");
                assert!(config.project_policy.is_none(), "{name}");
            }
        }
    }

    #[test]
    fn weaker_project_policy_runs_when_the_cli_selects_its_lane() {
        for cli in [&["--allow-l0-gaps"][..], &["--survey"][..]] {
            let args = adopt(&lane_policy("advisory"), cli).expect("explicit advisory lane");
            assert!(!args.strict_artifact_policy(), "{cli:?}");
            assert!(!args.certify && !args.memory_safe, "{cli:?}");
        }
        let args = adopt(&lane_policy("memory-safe"), &["--memory-safe"]).unwrap();
        assert!(args.memory_safe && !args.allow_l0_gaps && !args.certify);
        // A different loosening lane is still a conflict, not an opt-in.
        assert!(adopt(&lane_policy("memory-safe"), &["--allow-l0-gaps"]).is_err());
        assert!(adopt(&lane_policy("advisory"), &["--memory-safe"]).is_err());
    }

    /// Strict and certify tighten or restate the default lane, so a project may
    /// require them without the invocation repeating them.
    #[test]
    fn equal_or_stronger_project_policy_adopts_on_a_plain_invocation() {
        let args = adopt(&lane_policy("strict"), &[]).unwrap();
        assert!(args.strict_artifact_policy() && !args.certify);
        let args = adopt(&lane_policy("certify"), &[]).unwrap();
        assert!(args.certify_lane());
    }

    /// A project policy with exactly one requirement key set to `value`
    /// (a JSON literal), every other key null.
    fn one_key(key: &str, value: &str) -> ProjectTrustPolicy {
        let mut fields = serde_json::json!({
            "schema": "trust.project-policy.v1", "policy": null, "level": null,
            "profile": null, "include_dependencies": null, "ir_lower": null,
            "verification_required": false,
        });
        fields[key] = serde_json::from_str(value).unwrap();
        ProjectTrustPolicy::parse(fields.to_string().as_bytes()).unwrap()
    }

    fn adopt_in(
        policy: &ProjectTrustPolicy,
        cli: &[&str],
        config: TrustConfig,
    ) -> Result<(SubcommandArgs, TrustConfig), String> {
        let cli = cli.iter().map(|arg| arg.to_string()).collect::<Vec<_>>();
        let mut args = parse_subcommand_args(&cli).unwrap();
        let mut config = config;
        let before = (config.level.clone(), config.hardened, config.trust_profile.clone());
        let result = policy.adopt(&mut args, &mut config);
        match result {
            Ok(()) => Ok((args, config)),
            Err(error) => {
                // A refusal leaves the resolved run untouched.
                assert_eq!(
                    (config.level.clone(), config.hardened, config.trust_profile.clone()),
                    before
                );
                assert!(config.project_policy.is_none());
                Err(error)
            }
        }
    }

    fn assert_loosening_refused(error: &str, requirement: &str, select: &str) {
        assert!(error.contains(&format!("requires {requirement}")), "{error}");
        assert!(error.contains("cannot loosen"), "{error}");
        assert!(error.contains(select), "{error}");
    }

    #[test]
    fn weaker_project_level_refuses_unless_this_run_selects_it() {
        for level in ["0", "1"] {
            let policy = one_key("level", level);
            let error = adopt_in(&policy, &[], TrustConfig::default())
                .expect_err("a project level below the default L2 is a loosening");
            assert_loosening_refused(
                &error,
                &format!("-Ztrust-verify-level={level}"),
                &format!("`level = \"L{level}\"` in the [trust] table"),
            );
            assert!(error.contains("level L2"), "{error}");
            assert!(!error.contains("TRUSTFLAGS"), "T7a: no environment selection: {error}");
            // Declared in the [trust] table: the invocation already runs it.
            let declared = TrustConfig {
                level: format!("L{level}"),
                level_declared: true,
                ..TrustConfig::default()
            };
            let (_, config) = adopt_in(&policy, &[], declared).unwrap();
            assert_eq!(config.level, format!("L{level}"));
        }
        // Equal or stronger: adopted on a plain run.
        let (_, config) = adopt_in(&one_key("level", "2"), &[], TrustConfig::default()).unwrap();
        assert_eq!(config.level, "L2");
        let l1 = TrustConfig { level: "L1".into(), ..TrustConfig::default() };
        let (_, config) = adopt_in(&one_key("level", "2"), &[], l1).unwrap();
        assert_eq!(config.level, "L2");
    }

    #[test]
    fn unhardened_or_different_project_profile_refuses_unless_this_run_selects_it() {
        let default = one_key("profile", r#""default""#);
        let error = adopt_in(&default, &[], TrustConfig::default())
            .expect_err("dropping the default unix_hardened profile is a loosening");
        assert_loosening_refused(&error, "-Ztrust-verify-profile=default", "--no-hardened");
        assert!(error.contains("hardened profile `unix_hardened`"), "{error}");
        assert!(!error.contains("TRUSTFLAGS"), "T7a: no environment selection: {error}");
        let (args, config) = adopt_in(&default, &["--no-hardened"], TrustConfig::default())
            .expect("--no-hardened selects the unhardened run");
        assert!(!args.hardened);
        assert_eq!(config.hardened, Some(false));
        let unhardened = TrustConfig { hardened: Some(false), ..TrustConfig::default() };
        assert!(adopt_in(&default, &[], unhardened).is_ok());

        // A different hardened profile is not known to be stronger.
        let coreutils = one_key("profile", r#""coreutils_hardened""#);
        let error = adopt_in(&coreutils, &[], TrustConfig::default())
            .expect_err("an incomparable hardened profile fails closed");
        assert_loosening_refused(
            &error,
            "-Ztrust-verify-profile=coreutils_hardened",
            "--trust-profile coreutils_hardened",
        );
        let (args, _) = adopt_in(
            &coreutils,
            &["--trust-profile", "coreutils_hardened"],
            TrustConfig::default(),
        )
        .unwrap();
        assert_eq!(args.trust_profile.as_deref(), Some("coreutils_hardened"));
        let manifest = TrustConfig {
            trust_profile: Some("coreutils_hardened".into()),
            ..TrustConfig::default()
        };
        assert!(adopt_in(&coreutils, &[], manifest).is_ok());

        // The invocation's own profile: adopted on a plain run.
        let (args, _) =
            adopt_in(&one_key("profile", r#""unix_hardened""#), &[], TrustConfig::default())
                .unwrap();
        assert!(args.hardened);
        assert_eq!(args.trust_profile.as_deref(), Some("unix_hardened"));
    }

    /// No run selects dependency verification for itself any more (T7a), so
    /// the invocation's scope is the compiler default, `no`: a project value
    /// either restates it or widens it, and both are adopted.
    #[test]
    fn dependency_scope_requirement_never_narrows_the_invocation() {
        for value in ["true", "false"] {
            let (_, config) =
                adopt_in(&one_key("include_dependencies", value), &[], TrustConfig::default())
                    .unwrap();
            assert!(config.project_policy.is_some(), "{value}");
        }
    }

    /// The invocation's lowering is always `on` (T7a: no run selects another),
    /// so a project `off` refuses and names no per-run selection; `on` and
    /// `strict` are adopted.
    #[test]
    fn weaker_project_ir_lowering_refuses_with_no_per_run_selection() {
        let error = adopt_in(&one_key("ir_lower", r#""off""#), &[], TrustConfig::default())
            .expect_err("lowering off is below the verified default `on`");
        assert!(error.contains("requires -Ztrust-ir-lower=off"), "{error}");
        assert!(error.contains("cannot loosen"), "{error}");
        assert!(error.contains("no per-run selection lowers it"), "{error}");
        assert!(error.contains("remove it from the project's Cargo configuration"), "{error}");
        assert!(!error.contains("TRUSTFLAGS"), "{error}");
        for value in [r#""on""#, r#""strict""#] {
            assert!(adopt_in(&one_key("ir_lower", value), &[], TrustConfig::default()).is_ok());
        }
    }

    #[test]
    fn verification_requirement_only_tightens() {
        let required = one_key("verification_required", "true");
        assert!(adopt_in(&required, &[], TrustConfig::default()).is_ok());
        assert!(adopt_in(&required, &["--standalone"], TrustConfig::default()).is_err());
    }

    #[test]
    fn every_adopted_requirement_is_disclosed() {
        let cases = [
            ("policy", r#""certify""#, "policy=certify"),
            ("policy", r#""advisory""#, "policy=advisory"),
            ("level", "1", "level=L1"),
            ("profile", r#""default""#, "profile=default"),
            ("include_dependencies", "true", "include-dependencies=yes"),
            ("include_dependencies", "false", "include-dependencies=no"),
            ("ir_lower", r#""off""#, "ir-lower=off"),
            ("ir_lower", r#""strict""#, "ir-lower=strict"),
            ("verification_required", "true", "verification=required"),
        ];
        for (key, value, item) in cases {
            let policy = one_key(key, value);
            assert_eq!(
                policy.disclosure().as_deref(),
                Some(
                    format!(
                        "Cargo project configuration requirements adopted for this run: {item}"
                    )
                    .as_str()
                ),
                "{key}={value}"
            );
            assert_eq!(policy.report().unwrap().items(), [item], "{key}={value}");
        }
        assert_eq!(
            policy().disclosure().as_deref(),
            Some(
                "Cargo project configuration requirements adopted for this run: policy=certify, \
                 level=L2, profile=unix_hardened, include-dependencies=yes, ir-lower=strict, \
                 verification=required"
            )
        );
        let none = one_key("policy", "null");
        assert_eq!(none.disclosure(), None);
        assert_eq!(none.report(), None);
    }

    /// The adopted requirements reach the compile as options, and a run whose
    /// lane, profile or level disagrees with one is refused rather than
    /// compiled under a policy the report would not name.
    #[test]
    fn requirement_flags_carry_the_requirements_and_refuse_a_run_that_did_not_adopt_them() {
        let flags =
            ProjectRequirementFlags::for_run(Some(&policy()), "certify", Some("unix_hardened"), 2)
                .unwrap();
        assert_eq!(
            flags.options(),
            [
                "trust-policy=certify",
                "trust-verify-level=2",
                "trust-verify-profile=unix_hardened",
                "trust-verify-include-dependencies=yes",
                "trust-ir-lower=strict",
            ]
        );
        assert!(
            ProjectRequirementFlags::for_run(None, "advisory", None, 0)
                .unwrap()
                .options()
                .is_empty()
        );
        for (lane, profile, level, named) in [
            ("strict", Some("unix_hardened"), 2, "the `strict` lane"),
            ("certify", None, 2, "no hardened profile"),
            ("certify", Some("coreutils_hardened"), 2, "the `coreutils_hardened` hardened profile"),
            ("certify", Some("unix_hardened"), 1, "level L1"),
        ] {
            let error = ProjectRequirementFlags::for_run(Some(&policy()), lane, profile, level)
                .expect_err("a run that did not adopt the requirements is refused");
            assert!(error.contains(named), "{error}");
            assert!(error.contains("was not adopted for this run"), "{error}");
        }
        // `default` restates an unhardened run, and only that.
        let default = one_key("profile", r#""default""#);
        let flags = ProjectRequirementFlags::for_run(Some(&default), "strict", None, 2).unwrap();
        assert_eq!(flags.options(), ["trust-verify-profile=default"]);
        assert!(
            ProjectRequirementFlags::for_run(Some(&default), "strict", Some("unix_hardened"), 2)
                .is_err()
        );
    }

    #[test]
    fn requirement_flags_replace_every_earlier_spelling_and_keep_the_representation() {
        let flags = ProjectRequirementFlags::for_run(
            Some(&one_key("ir_lower", r#""strict""#)),
            "strict",
            None,
            2,
        )
        .unwrap();
        let mut args =
            ["-Ztrust-ir-lower=on", "-Z", "trust_ir_lower=off", "-Ztrust-policy=certify"]
                .map(str::to_string)
                .to_vec();
        flags.apply_to_args(&mut args);
        assert_eq!(args, ["-Ztrust-policy=certify", "-Z", "trust-ir-lower=strict"]);

        // No requirement: nothing moves.
        let none = ProjectRequirementFlags::default();
        let mut args = vec!["-Z".to_string(), "trust-verify-level=2".to_string()];
        none.apply_to_args(&mut args);
        assert_eq!(args, ["-Z", "trust-verify-level=2"]);
    }

    #[test]
    fn unknown_schema_profile_and_authority_fields_cannot_select_defaults() {
        for bytes in [br#"{"schema":"other","policy":null,"level":null,"profile":null,"include_dependencies":null,"ir_lower":null,"verification_required":false}"#.as_slice(), br#"{"schema":"trust.project-policy.v1","policy":"certify","level":2,"profile":"typo","include_dependencies":true,"ir_lower":"strict","verification_required":true}"#.as_slice(), br#"{"schema":"trust.project-policy.v1","policy":null,"level":null,"profile":null,"include_dependencies":null,"ir_lower":null,"verification_required":false,"session":"forged"}"#.as_slice()] {
            assert!(ProjectTrustPolicy::parse(bytes).is_err());
        }
    }

    #[test]
    fn missing_optional_policy_keys_do_not_silently_remove_requirements() {
        assert!(
            ProjectTrustPolicy::parse(
                br#"{"schema":"trust.project-policy.v1","verification_required":false}"#
            )
            .is_err()
        );
    }

    #[test]
    fn policy_query_preserves_cargo_context_and_explicit_target_only() {
        let args = [
            "--config",
            "target-applies-to-host=false",
            "--offline",
            "--locked",
            "--target",
            "aarch64-unknown-linux-gnu",
            "--manifest-path",
            "/owned/Cargo.toml",
            "-p",
            "selected",
        ]
        .map(str::to_string);
        let query = CargoSelectionArgs::parse(&args).unwrap().project_policy_query_args();
        assert_eq!(
            query,
            [
                "--config",
                "target-applies-to-host=false",
                "--offline",
                "--locked",
                "-Z",
                "unstable-options",
                "config",
                "trust-policy",
                "--target",
                "aarch64-unknown-linux-gnu"
            ]
            .map(str::to_string)
        );
        // Cargo resolves config from launch cwd, not the manifest's directory.
        assert!(!query.iter().any(|arg| arg == "--manifest-path" || arg == "-p"));
    }

    /// The policy query carries the sibling toolchain's one loader search path
    /// and force-clears every other loader variable, as Targo's admission of the
    /// query requires (`project_policy_query_command`). Without it every
    /// `targo trust` run of a sealed toolchain was refused before compiling.
    #[cfg(unix)]
    #[test]
    fn policy_query_carries_the_sibling_toolchain_loader_path_and_no_other_loader_authority() {
        use std::ffi::{OsStr, OsString};
        use std::os::unix::fs::PermissionsExt;

        // A sealed toolchain's shape: bin/{trustc,targo} beside the compiler's
        // runtime libraries in lib/ and lib/rustlib/<host>/lib.
        let root = std::env::temp_dir().join(format!(
            "targo-trust-policy-query-loader-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |since| since.as_nanos())
        ));
        let bin = root.join("bin");
        let host_lib = root.join("lib/rustlib/test-host/lib");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(&host_lib).unwrap();
        for tool in ["trustc", "targo"] {
            let path = bin.join(tool);
            std::fs::write(&path, "").unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let rustc = bin.join("trustc");

        let args = parse_subcommand_args(&[]).unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        let command =
            project_policy_query_command(&args, &TrustConfig::default(), &rustc, deadline).unwrap();
        let env = |name: &str| -> Option<Option<OsString>> {
            command.get_envs().find_map(|(key, value)| {
                (key == OsStr::new(name)).then(|| value.map(OsStr::to_owned))
            })
        };

        let (variable, expected) = super::super::probe::native_runtime_environment(&rustc)
            .expect("a sealed toolchain has a runtime search path");
        let expected_paths = std::env::split_paths(&expected).collect::<Vec<_>>();
        for dir in [root.join("lib"), host_lib] {
            let dir = std::fs::canonicalize(&dir).unwrap_or(dir);
            assert!(
                expected_paths.contains(&dir),
                "{} missing from {expected_paths:?}",
                dir.display()
            );
        }
        assert_eq!(env(variable), Some(Some(expected)), "the query must carry `{variable}`");
        for injected in ["DYLD_INSERT_LIBRARIES", "DYLD_FRAMEWORK_PATH", "LD_PRELOAD", "LD_AUDIT"] {
            assert_eq!(env(injected), Some(None), "the query must force-clear `{injected}`");
        }

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn expired_original_setup_deadline_refuses_first_query_and_recheck_before_discovery() {
        let expired = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
        let args = parse_subcommand_args(&[]).unwrap();
        for _ in 0..2 {
            let error = resolve_project_policy(
                &args,
                &TrustConfig::default(),
                Path::new("/no-compiler-or-spawn"),
                expired,
            )
            .unwrap_err();
            assert!(error.contains("original project-policy setup deadline expired"), "{error}");
        }
    }
}
