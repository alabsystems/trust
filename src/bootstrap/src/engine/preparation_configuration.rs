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
mod tests;
