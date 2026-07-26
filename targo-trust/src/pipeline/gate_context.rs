// Cargo semantic context replay for post-build verification gates.
//
// A post-build proof is evidence for the build only when it sees the same
// feature/cfg/target selection. Re-running a default host/debug crate after a
// feature, release, configured, or cross-target build can silently remove the
// very model or harness the gate is meant to inspect.

use std::process::Command;
use std::time::Duration;

use crate::bounded_process;
use crate::cli::parse_subcommand_args;

const CONTEXT_PROBE_MAX_STREAM_BYTES: usize = 16 * 1024 * 1024;
const CONTEXT_PROBE_TIMEOUT: Duration = Duration::from_secs(2 * 60);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PostBuildCargoContext {
    /// Cargo flags that can be replayed byte-for-byte by the temporal `targo
    /// run --example` invocation.
    temporal_args: Vec<String>,
    /// Feature/config/lock/platform flags accepted by `targo metadata` for
    /// resolving the actually-active temporal dependency graph.
    metadata_args: Vec<String>,
    /// Cargo/common target flags accepted by cargo-trust-mc.
    trust_mc_args: Vec<String>,
    /// Semantically relevant Cargo flags cargo-trust-mc cannot currently
    /// reproduce. A Kani gate must fail closed when this is nonempty.
    trust_mc_unsupported: Vec<String>,
}

impl PostBuildCargoContext {
    pub(crate) fn temporal_args(&self) -> &[String] {
        &self.temporal_args
    }

    pub(crate) fn metadata_args(&self) -> &[String] {
        &self.metadata_args
    }

    // Retained only to regression-test context drift while the post-build Kani
    // certification route is fail-closed pending authenticated build binding.
    #[cfg(test)]
    pub(crate) fn trust_mc_args(&self) -> Result<&[String], String> {
        if self.trust_mc_unsupported.is_empty() {
            Ok(&self.trust_mc_args)
        } else {
            Err(format!(
                "cargo-trust-mc cannot reproduce build context {}; refusing to treat a \
                 default host/debug proof run as evidence for this build",
                self.trust_mc_unsupported.join(", ")
            ))
        }
    }
}

/// Recover the child-facing Cargo context from wrapper arguments. `None` is
/// the intentional direct-rustc single-file lane, which has no post-build Cargo
/// gate.
pub(crate) fn post_build_cargo_context(
    wrapper_args: &[String],
) -> Result<Option<PostBuildCargoContext>, String> {
    let parsed = parse_subcommand_args(wrapper_args)
        .map_err(|error| format!("could not parse build arguments for gate replay: {error}"))?;
    if parsed.is_single_file {
        return Ok(None);
    }
    parse_child_cargo_context(&parsed.crate_mode_cargo_args()).map(Some)
}

/// Resolve Cargo's non-CLI `build.target` selection. cargo-trust-mc does not
/// currently accept a target triple, so its host proof cannot certify a build
/// whose cfg/layout came from `CARGO_BUILD_TARGET` or `.cargo/config.toml`.
pub(crate) fn configured_cargo_build_target() -> Result<Option<String>, String> {
    if let Some(value) = std::env::var_os("CARGO_BUILD_TARGET") {
        if !value.is_empty() {
            return Ok(Some(value.to_string_lossy().into_owned()));
        }
    }

    let targo = super::discovery::discover_native_trust_cargo_checked()?;
    let mut command = Command::new(&targo);
    command.args([
        "-Z",
        "unstable-options",
        "config",
        "get",
        "build.target",
        "--format",
        "json-value",
    ]);
    let output = bounded_process::output(
        &mut command,
        "canonical Targo build.target probe",
        CONTEXT_PROBE_MAX_STREAM_BYTES,
        CONTEXT_PROBE_TIMEOUT,
    )
    .map_err(|error| {
        format!("could not inspect canonical Targo build.target at {}: {error}", targo.display())
    })?;
    if output.status.success() {
        let value: serde_json::Value = serde_json::from_slice(&output.stdout).map_err(|error| {
            format!("canonical `targo config get build.target` returned invalid JSON: {error}")
        })?;
        return Ok(match value {
            serde_json::Value::String(target) if !target.is_empty() => Some(target),
            serde_json::Value::Array(targets) if !targets.is_empty() => Some(
                targets
                    .into_iter()
                    .map(|target| target.as_str().unwrap_or("<non-string>").to_string())
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            serde_json::Value::Null => None,
            other => {
                return Err(format!(
                    "canonical `targo config get build.target` returned unexpected value {other}"
                ));
            }
        });
    }
    let stderr = std::str::from_utf8(&output.stderr).map_err(|error| {
        format!("canonical `targo config get build.target` returned non-UTF-8 stderr: {error}")
    })?;
    if stderr.contains("config value `build.target` is not set") {
        Ok(None)
    } else {
        Err(format!(
            "canonical `targo config get build.target` failed with {}: {}",
            output.status,
            stderr.trim()
        ))
    }
}

pub(crate) fn selected_trustc_host_triple() -> Result<String, String> {
    let rustc = super::discovery::discover_native_rustc_checked()
        .ok_or_else(|| "canonical Trust compiler is unavailable for host discovery".to_string())?
        .rustc;
    super::run::exact_rustc_host_triple(&rustc)
}

fn parse_child_cargo_context(args: &[String]) -> Result<PostBuildCargoContext, String> {
    let mut context = PostBuildCargoContext::default();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--" {
            break;
        }

        match arg {
            // Feature selection is supported by both Cargo and cargo-trust-mc.
            "--features" | "-F" => {
                push_required_pair(args, &mut index, &mut context.temporal_args, arg)?;
                let value = context.temporal_args[context.temporal_args.len() - 1].clone();
                context.metadata_args.extend([arg.to_string(), value.clone()]);
                context.trust_mc_args.push(arg.to_string());
                context.trust_mc_args.push(value);
            }
            "--all-features" | "--no-default-features" => {
                context.temporal_args.push(arg.to_string());
                context.metadata_args.push(arg.to_string());
                context.trust_mc_args.push(arg.to_string());
            }

            // cargo-trust-mc mirrors these target selectors.
            "--all-targets" | "--lib" | "--bins" | "--examples" | "--tests" | "--benches" => {
                context.trust_mc_args.push(arg.to_string())
            }
            "--bin" | "--example" | "--test" | "--bench" => {
                context.trust_mc_args.push(arg.to_string());
                if let Some(value) = optional_value(args, &mut index) {
                    context.trust_mc_args.push(value);
                }
            }

            // Artifact location is not semantic, but replaying it avoids a
            // second build tree and cargo-trust-mc accepts the option.
            "--target-dir" => {
                let value = required_value(args, &mut index, arg)?;
                context.temporal_args.extend([arg.to_string(), value.clone()]);
                context.trust_mc_args.extend([arg.to_string(), absolutize(value)]);
            }

            // Temporal's canonical Targo can reproduce these contexts;
            // cargo-trust-mc currently cannot, so Kani fails closed.
            "--target" => {
                context.temporal_args.push(arg.to_string());
                let value = optional_value(args, &mut index);
                if let Some(value) = value {
                    context.temporal_args.push(value.clone());
                    context.metadata_args.extend(["--filter-platform".to_string(), value.clone()]);
                    context.trust_mc_unsupported.push(format!("--target {value}"));
                } else {
                    context.trust_mc_unsupported.push("--target".to_string());
                }
            }
            "--profile" | "--config" | "--lockfile-path" | "-Z" => {
                let value = required_value(args, &mut index, arg)?;
                context.temporal_args.extend([arg.to_string(), value.clone()]);
                if arg != "--profile" {
                    context.metadata_args.extend([arg.to_string(), value.clone()]);
                }
                context.trust_mc_unsupported.push(format!("{arg} {value}"));
            }
            "--release" | "-r" | "--locked" | "--offline" | "--frozen" => {
                context.temporal_args.push(arg.to_string());
                if matches!(arg, "--locked" | "--offline" | "--frozen") {
                    context.metadata_args.push(arg.to_string());
                }
                context.trust_mc_unsupported.push(arg.to_string());
            }
            _ => {
                if is_joined(arg, &["--features=", "-F"]) {
                    context.temporal_args.push(arg.to_string());
                    context.metadata_args.push(arg.to_string());
                    context.trust_mc_args.push(arg.to_string());
                } else if is_joined(arg, &["--target-dir="]) {
                    let value = arg.split_once('=').map(|(_, value)| value).unwrap_or_default();
                    if value.is_empty() {
                        return Err("--target-dir requires a nonempty value".to_string());
                    }
                    context.temporal_args.push(arg.to_string());
                    context.trust_mc_args.push(format!("--target-dir={}", absolutize(value)));
                } else if is_joined(
                    arg,
                    &["--target=", "--profile=", "--config=", "--lockfile-path=", "-Z"],
                ) {
                    let value = joined_value(arg).ok_or_else(|| {
                        format!("Cargo context option `{arg}` requires a nonempty value")
                    })?;
                    context.temporal_args.push(arg.to_string());
                    if arg.starts_with("--target=") {
                        context
                            .metadata_args
                            .extend(["--filter-platform".to_string(), value.to_string()]);
                    } else if !arg.starts_with("--profile=") {
                        context.metadata_args.push(arg.to_string());
                    }
                    context.trust_mc_unsupported.push(arg.to_string());
                } else if is_joined(arg, &["--bin=", "--example=", "--test=", "--bench="]) {
                    if joined_value(arg).is_none() {
                        return Err(format!("Cargo target selector `{arg}` requires a value"));
                    }
                    context.trust_mc_args.push(arg.to_string());
                }
            }
        }
        index += 1;
    }
    Ok(context)
}

fn push_required_pair(
    args: &[String],
    index: &mut usize,
    output: &mut Vec<String>,
    option: &str,
) -> Result<(), String> {
    let value = required_value(args, index, option)?;
    output.extend([option.to_string(), value]);
    Ok(())
}

fn required_value(args: &[String], index: &mut usize, option: &str) -> Result<String, String> {
    *index += 1;
    args.get(*index)
        .filter(|value| !value.is_empty() && value.as_str() != "--")
        .cloned()
        .ok_or_else(|| format!("{option} requires a nonempty value"))
}

fn optional_value(args: &[String], index: &mut usize) -> Option<String> {
    let next = args.get(*index + 1)?;
    if next == "--" || next.starts_with('-') {
        return None;
    }
    *index += 1;
    Some(next.clone())
}

fn is_joined(arg: &str, prefixes: &[&str]) -> bool {
    prefixes.iter().any(|prefix| arg.starts_with(prefix) && arg.len() > prefix.len())
}

fn joined_value(arg: &str) -> Option<&str> {
    if let Some((_, value)) = arg.split_once('=') {
        return (!value.is_empty()).then_some(value);
    }
    arg.strip_prefix("-Z").filter(|value| !value.is_empty())
}

fn absolutize(path: impl AsRef<std::path::Path>) -> String {
    let path = path.as_ref();
    if path.is_absolute() {
        return path.to_string_lossy().into_owned();
    }
    std::env::current_dir()
        .map(|cwd| cwd.join(path).to_string_lossy().into_owned())
        .unwrap_or_else(|_| path.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn replays_features_and_target_selectors_to_both_gates() {
        let context = parse_child_cargo_context(&strings(&[
            "--features",
            "bad,extra",
            "--no-default-features",
            "--example",
            "violating",
            "--target-dir=target/custom",
        ]))
        .expect("parse supported context");
        assert_eq!(
            context.temporal_args,
            ["--features", "bad,extra", "--no-default-features", "--target-dir=target/custom"]
        );
        let trust_mc = context.trust_mc_args().expect("supported trust-mc context");
        assert!(trust_mc.windows(2).any(|pair| pair == ["--features", "bad,extra"]));
        assert!(trust_mc.windows(2).any(|pair| pair == ["--example", "violating"]));
        assert!(trust_mc.iter().any(|arg| arg.starts_with("--target-dir=")));
    }

    #[test]
    fn unsupported_kani_semantic_context_fails_closed_but_temporal_replays_it() {
        let context = parse_child_cargo_context(&strings(&[
            "--release",
            "--target",
            "wasm32-unknown-unknown",
            "--config=build.rustflags=['--cfg','special']",
            "-Z",
            "bindeps",
        ]))
        .expect("parse unsupported context");
        assert!(context.temporal_args.contains(&"--release".to_string()));
        assert!(context.temporal_args.contains(&"wasm32-unknown-unknown".to_string()));
        let error = context.trust_mc_args().expect_err("Kani must refuse context drift");
        assert!(error.contains("--release"));
        assert!(error.contains("--target wasm32-unknown-unknown"));
        assert!(error.contains("--config="));
        assert!(error.contains("-Z bindeps"));
    }

    #[test]
    fn joined_semantic_options_reach_metadata_without_target_dir_confusion() {
        let context = parse_child_cargo_context(&strings(&[
            "--target-dir=target/custom",
            "--target=wasm32-unknown-unknown",
            "--profile=benchlike",
            "--config=build.rustflags=['--cfg','special']",
            "--lockfile-path=locks/Cargo.lock",
            "-Zbindeps",
        ]))
        .expect("parse joined context");

        assert!(context.temporal_args.contains(&"--target-dir=target/custom".to_string()));
        assert!(context.temporal_args.contains(&"--target=wasm32-unknown-unknown".to_string()));
        assert!(context.temporal_args.contains(&"--profile=benchlike".to_string()));
        assert!(
            context
                .metadata_args
                .windows(2)
                .any(|pair| { pair == ["--filter-platform", "wasm32-unknown-unknown"] })
        );
        assert!(
            context
                .metadata_args
                .contains(&"--config=build.rustflags=['--cfg','special']".to_string())
        );
        assert!(context.metadata_args.contains(&"--lockfile-path=locks/Cargo.lock".to_string()));
        assert!(context.metadata_args.contains(&"-Zbindeps".to_string()));
        assert!(!context.metadata_args.iter().any(|arg| arg.starts_with("--target-dir")));
        assert!(!context.metadata_args.iter().any(|arg| arg.starts_with("--profile")));
        assert!(context.trust_mc_args().is_err());
    }

    #[test]
    fn wrapper_trust_options_are_not_replayed_as_cargo_context() {
        let context = post_build_cargo_context(&strings(&[
            "--no-hardened",
            "--features",
            "model",
            "--survey",
        ]))
        .expect("parse wrapper")
        .expect("crate mode");
        assert_eq!(context.temporal_args, ["--features", "model"]);
        assert_eq!(context.trust_mc_args().unwrap(), ["--features", "model"]);
    }
}
