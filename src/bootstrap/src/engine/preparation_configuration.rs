//! Exact original Bootstrap parser input, never process argv or input custody.
//! The actual CLI captures it before Config reads. The native resident must
//! separately retain source/config roots and validate every physical producer.
use trust_resource_controller::bootstrap_graph::offline_preparation::ConfigurationSelection;

use super::*;

const MAX_ARGUMENTS: usize = 1024;
const MAX_BYTES: usize = 64 * 1024;

/// Closed FullEnvelope parser DATA. No source, Config-root, execution, SDK,
/// completed preparation or Step authority is represented or constructed.
/// There is no Command/Step builder or executable selector on this type.
#[derive(Clone)]
pub struct ClosedFullPreparationConfiguration {
    input: Vec<String>,
    invocation: PathBuf,
}
impl ClosedFullPreparationConfiguration {
    /// Validate DATA with the SAME fallible parser and full-scope contract.
    /// `invocation` is an original cwd observation, not a directory capability.
    pub fn from_parser_input(input: &[String], invocation: &Path) -> Result<Self, String> {
        let mut lexical = PathBuf::new();
        for component in invocation.components() {
            lexical.push(component.as_os_str());
        }
        let invocation_bytes = invocation.as_os_str().as_encoded_bytes();
        if input.is_empty()
            || input.len() > MAX_ARGUMENTS
            || !invocation.is_absolute()
            || invocation_bytes.len() > 4096
            || invocation_bytes.contains(&0)
            || lexical.as_os_str() != invocation.as_os_str()
            || invocation.components().any(|part| {
                matches!(part, std::path::Component::CurDir | std::path::Component::ParentDir)
            })
        {
            return Err(
                "original full configuration parser input is unbounded or unanchored".into()
            );
        }
        input
            .iter()
            .try_fold(0usize, |total, argument| {
                if argument.as_bytes().contains(&0) {
                    return None;
                }
                total.checked_add(argument.len()).and_then(|bytes| bytes.checked_add(1))
            })
            .filter(|total| *total <= MAX_BYTES)
            .ok_or("original full configuration parser input exceeds its byte bound")?;
        let arguments: Vec<_> = input.iter().map(OsString::from).collect();
        let flags = xpy_flags(&arguments)?
            .ok_or("help/version has no original full configuration selection")?;
        validate_flags(&flags)?;
        if flags.dry_run || PreparationScope::for_flags(&flags) != PreparationScope::FullEnvelope {
            return Err("original configuration selection is not the full preparation scope".into());
        }
        Ok(Self { input: input.to_vec(), invocation: invocation.to_path_buf() })
    }
    /// Exact bytes/order accepted by Bootstrap; these are parser DATA only.
    pub fn parser_input(&self) -> &[String] {
        &self.input
    }
    /// Observed original cwd; it grants no rights to read/canonicalize a path.
    pub fn invocation_directory(&self) -> &Path {
        &self.invocation
    }
    /// Carrier DATA only. No encoder may turn it into executable argv or
    /// claim that the explicitly selected configuration root is already held.
    pub fn attachment(&self) -> std::io::Result<ConfigurationSelection> {
        let value = ConfigurationSelection {
            parser_input: self.input.clone(),
            invocation_directory: self.invocation.as_os_str().as_encoded_bytes().to_vec(),
        };
        value.validate()?;
        Ok(value)
    }
    /// Receiving DATA must pass the SAME fallible parser/scope contract again.
    /// This validates observations, without opening its cwd/config paths or
    /// creating Source Managers, configuration producers or dispatch rights.
    #[cfg(unix)]
    pub fn from_attachment(value: &ConfigurationSelection) -> Result<Self, String> {
        use std::os::unix::ffi::OsStringExt;
        value.validate().map_err(|error| error.to_string())?;
        let invocation = PathBuf::from(OsString::from_vec(value.invocation_directory.clone()));
        Self::from_parser_input(&value.parser_input, &invocation)
    }
}

/// The maintained actual caller supplies its parsed Flags and original input
/// together, before Config consumes them. Ordinary non-full invocations keep
/// their existing behavior; errors explicitly refuse later native promotion.
pub(crate) fn capture_original_configuration(
    input: &[String],
    flags: &crate::core::config::flags::Flags,
) -> Result<Option<ClosedFullPreparationConfiguration>, String> {
    if flags.dry_run || PreparationScope::for_flags(flags) != PreparationScope::FullEnvelope {
        return Ok(None);
    }
    let invocation = std::env::current_dir()
        .map_err(|error| format!("cannot retain original configuration cwd: {error}"))?;
    ClosedFullPreparationConfiguration::from_parser_input(input, &invocation).map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn args(input: &[&str]) -> Vec<String> {
        input.iter().map(|arg| (*arg).into()).collect()
    }
    #[test]
    fn exact_external_config_profile_override_order_and_duplicates_are_retained() {
        let original = args(&[
            "build",
            "--config",
            "/evidence/full.toml",
            "--set",
            "profile=\"compiler\"",
            "--set",
            "build.jobs=2",
            "--set",
            "build.jobs=1",
            "--build-dir",
            "/original-output",
        ]);
        let selected = ClosedFullPreparationConfiguration::from_parser_input(
            &original,
            Path::new("/original-cwd"),
        )
        .unwrap();
        assert_eq!(selected.parser_input(), original);
        assert_eq!(selected.invocation_directory(), Path::new("/original-cwd"));
    }
    #[test]
    fn existing_parser_scope_and_stage0_contract_refuse_unsupported_selection() {
        for input in [
            args(&["--help"]),
            args(&["--version"]),
            args(&["build", "--unknown-option"]),
            args(&["build", "--dry-run"]),
            args(&["build", "--stage", "1", "compiler/rustc"]),
            args(&["build", "--skip-stage0-validation"]),
            args(&["setup"]),
        ] {
            assert!(
                ClosedFullPreparationConfiguration::from_parser_input(&input, Path::new("/cwd"))
                    .is_err()
            );
        }
        let defaults =
            args(&["build", "--stage", "1", "--include-default-paths", "compiler/rustc"]);
        ClosedFullPreparationConfiguration::from_parser_input(&defaults, Path::new("/cwd"))
            .unwrap();
    }
    #[test]
    fn malformed_or_unbounded_parser_data_never_implies_original_selection() {
        for input in [
            vec![],
            args(&["build", "--config", "bad\0path"]),
            vec!["build".into(); MAX_ARGUMENTS + 1],
            args(&["build", "--set", &"x".repeat(MAX_BYTES)]),
        ] {
            assert!(
                ClosedFullPreparationConfiguration::from_parser_input(&input, Path::new("/cwd"))
                    .is_err()
            );
        }
        assert!(
            ClosedFullPreparationConfiguration::from_parser_input(
                &args(&["build"]),
                Path::new("relative")
            )
            .is_err()
        );
    }
    #[test]
    fn actual_caller_keeps_non_full_scope_separate_and_retains_full_parser_error() {
        let selected = args(&["build", "--stage", "1", "compiler/rustc"]);
        let flags = crate::core::config::flags::Flags::try_parse(&selected).unwrap();
        assert!(capture_original_configuration(&selected, &flags).unwrap().is_none());
        let unsupported = args(&["build", "--skip-stage0-validation"]);
        let flags = crate::core::config::flags::Flags::try_parse(&unsupported).unwrap();
        assert!(capture_original_configuration(&unsupported, &flags).is_err());
    }
    #[cfg(unix)]
    #[test]
    fn decoded_configuration_data_requires_the_same_fallible_parser_and_full_scope() {
        let original = args(&["build", "--config", "/external/full.toml", "--set", "build.jobs=2"]);
        let captured =
            ClosedFullPreparationConfiguration::from_parser_input(&original, Path::new("/cwd"))
                .unwrap();
        let mut attachment = captured.attachment().unwrap();
        let same = ClosedFullPreparationConfiguration::from_attachment(&attachment).unwrap();
        assert_eq!(same.parser_input(), original);
        assert_eq!(same.invocation_directory(), captured.invocation_directory());
        for unsupported in [
            args(&["--help"]),
            args(&["--unknown-option"]),
            args(&["build", "--stage", "1", "compiler/rustc"]),
            args(&["build", "--skip-stage0-validation"]),
        ] {
            attachment.parser_input = unsupported;
            attachment.validate().unwrap(); // syntax DATA has no scope authority
            assert!(ClosedFullPreparationConfiguration::from_attachment(&attachment).is_err());
        }
    }
}
