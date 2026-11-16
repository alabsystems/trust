//! Trust: one captured inherited environment for action identity and execution.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::sync::Arc;

use anyhow::{Result, bail};

/// Environment values stay in memory; only the digest belongs in fingerprints.
/// Explicit command overrides and jobserver capabilities are separate inputs.
#[derive(Clone)]
pub struct EnvironmentInputs {
    variables: Arc<BTreeMap<OsString, OsString>>,
    digest: String,
}

impl std::fmt::Debug for EnvironmentInputs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EnvironmentInputs")
            .field("variable_count", &self.variables.len())
            .finish_non_exhaustive()
    }
}

impl EnvironmentInputs {
    pub fn capture() -> Result<Self> {
        Self::from_variables(std::env::vars_os())
    }

    /// Capture all final command values, including the selected resource
    /// transport. This is an observation of a prepared command, not a request
    /// to inherit additional ambient variables.
    pub fn capture_effective(command: &crate::ProcessBuilder) -> Result<Self> {
        #[cfg(unix)]
        return Self::from_variables(command.get_effective_envs()?);
        #[cfg(not(unix))]
        {
            let _ = command;
            bail!("effective action environments are not implemented on this platform")
        }
    }

    /// Capture declared inheritance after configuration and protocol scrubbing.
    /// Explicit command settings are declarations too; unrelated ambient
    /// variables never enter either the digest or the child's environment.
    pub fn capture_for(command: &crate::ProcessBuilder, inherited: &[&str]) -> Result<Self> {
        #[cfg(unix)]
        {
            let mut values = command.get_effective_envs()?;
            values.retain(|name, _| {
                inherited.iter().any(|allowed| name == OsStr::new(allowed))
                    || name
                        .to_str()
                        .is_some_and(|name| command.get_envs().contains_key(name))
            });
            Self::from_variables(values)
        }
        #[cfg(not(unix))]
        {
            let _ = (command, inherited);
            bail!("captured action environments are not implemented on this platform")
        }
    }

    /// Reconstruct a validated, bounded environment without inheriting ambient values.
    pub fn from_variables(values: impl IntoIterator<Item = (OsString, OsString)>) -> Result<Self> {
        let mut variables = BTreeMap::new();
        let mut bytes = 0_usize;
        for (name, value) in values {
            bytes = bytes
                .checked_add(name.len())
                .and_then(|bytes| bytes.checked_add(value.len()))
                .ok_or_else(|| anyhow::anyhow!("action environment exceeds its size bound"))?;
            if variables.len() >= 16_384 || bytes > 16 * 1024 * 1024 {
                bail!("action environment exceeds its size bound");
            }
            if name.is_empty()
                || name.as_encoded_bytes().contains(&b'=')
                || name.as_encoded_bytes().contains(&0)
                || value.as_encoded_bytes().contains(&0)
            {
                bail!("action environment contains an invalid variable");
            }
            if variables.insert(name, value).is_some() {
                bail!("action environment contains a duplicate variable");
            }
        }
        let mut hash = crate::Sha256::new();
        hash.update(b"targo-inherited-environment-v1");
        for (name, value) in &variables {
            for field in [name, value] {
                let field = field.as_encoded_bytes();
                hash.update(&(field.len() as u64).to_le_bytes());
                hash.update(field);
            }
        }
        Ok(Self {
            variables: Arc::new(variables),
            digest: hash.finish_hex(),
        })
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    pub(crate) fn variables(&self) -> &BTreeMap<OsString, OsString> {
        &self.variables
    }

    pub fn get(&self, name: &OsStr) -> Option<OsString> {
        self.variables.get(name).cloned()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&OsStr, &OsStr)> {
        self.variables
            .iter()
            .map(|(name, value)| (name.as_os_str(), value.as_os_str()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inputs(values: &[(&str, &str)]) -> EnvironmentInputs {
        EnvironmentInputs::from_variables(values.iter().map(|(k, v)| ((*k).into(), (*v).into())))
            .unwrap()
    }

    #[test]
    fn identity_binds_values_and_absence_but_not_iteration_order() {
        let original = inputs(&[("FIRST", "one"), ("SECOND", "two")]);
        assert_eq!(
            original.digest(),
            inputs(&[("SECOND", "two"), ("FIRST", "one")]).digest()
        );
        assert_ne!(
            original.digest(),
            inputs(&[("FIRST", "one"), ("SECOND", "changed")]).digest()
        );
        assert_ne!(inputs(&[]).digest(), inputs(&[("FIRST", "")]).digest());
        assert_ne!(
            inputs(&[("AB", "C")]).digest(),
            inputs(&[("A", "BC")]).digest()
        );
        assert!(!format!("{original:?}").contains("FIRST"));
    }

    #[test]
    fn duplicate_and_invalid_variables_cannot_be_captured() {
        for values in [
            vec![("A", "1"), ("A", "2")],
            vec![("A=B", "1")],
            vec![("", "1")],
        ] {
            assert!(
                EnvironmentInputs::from_variables(
                    values.into_iter().map(|(k, v)| (k.into(), v.into()))
                )
                .is_err()
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn declared_capture_preserves_configuration_without_ambient_inheritance() {
        let mut command = crate::ProcessBuilder::new("unused");
        command.env("DECLARED", "configured");
        let inputs = EnvironmentInputs::capture_for(&command, &[]).unwrap();
        assert_eq!(inputs.variables().len(), 1);
        assert_eq!(inputs.get(OsStr::new("DECLARED")).unwrap(), "configured");
    }

    #[cfg(unix)]
    #[test]
    fn exact_captured_environment_reaches_child_after_overrides() {
        let snapshot = inputs(&[
            ("KEPT", "captured"),
            ("REMOVED", "old"),
            ("REPLACED", "old"),
        ]);
        let mut command = crate::ProcessBuilder::new("/bin/sh");
        command.environment_snapshot(snapshot);
        command.env_remove("REMOVED").env("REPLACED", "new");
        command.args(&["-c", "test -z \"${HOME+x}\" && test -z \"${REMOVED+x}\" && printf '%s/%s' \"$KEPT\" \"$REPLACED\""]);
        assert_eq!(command.get_env("KEPT").unwrap(), "captured");
        assert_eq!(command.get_env("HOME"), None);
        assert_eq!(command.get_env("REMOVED"), None);
        assert_eq!(command.exec_with_output().unwrap().stdout, b"captured/new");
        assert_eq!(
            command
                .get_effective_envs()
                .unwrap()
                .get(OsStr::new("KEPT"))
                .unwrap(),
            "captured"
        );
    }
}
