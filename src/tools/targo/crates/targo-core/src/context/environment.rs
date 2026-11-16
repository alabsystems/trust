//! Encapsulates snapshotting of environment variables.

use crate::util::data_structures::HashMap;
use std::ffi::{OsStr, OsString};

use crate::util::errors::CargoResult;
use anyhow::{anyhow, bail};

/// Trust: add Cargo-compatibility views for native Targo configuration
/// variables.
///
/// The inherited configuration machinery intentionally continues to parse the
/// `CARGO_*` namespace. Keeping the translation inside the immutable
/// `GlobalContext` snapshot avoids process-global environment mutation while
/// letting `TARGO_HOME`, `TARGO_TARGET_DIR`, `TARGO_NET_*`, and future native
/// configuration keys use the same parser. An explicitly supplied Cargo
/// spelling wins, preserving compatibility callers' established precedence.
fn add_targo_config_compatibility_twins(env: &mut HashMap<OsString, OsString>, native: bool) {
    if !native {
        return;
    }
    let twins = env
        .iter()
        .filter_map(|(key, value)| {
            let suffix = key.to_str()?.strip_prefix("TARGO_")?;
            // These are outputs for compiled units, not configuration inputs.
            // Re-importing a parent's metadata can conceal this package's changes.
            if [
                "PKG_",
                "MANIFEST_",
                "COMMIT_",
                "CFG_",
                "FEATURE_",
                "BIN_EXE_",
            ]
            .iter()
            .any(|prefix| suffix.starts_with(prefix))
                || matches!(suffix, "CRATE_NAME" | "BIN_NAME" | "PRIMARY_PACKAGE")
            {
                return None;
            }
            Some((OsString::from(format!("CARGO_{suffix}")), value.clone()))
        })
        .collect::<Vec<_>>();

    for (key, value) in twins {
        env.entry(key).or_insert(value);
    }
}

/// Generate `case_insensitive_env` and `normalized_env` from the `env`.
fn make_case_insensitive_and_normalized_env(
    env: &HashMap<OsString, OsString>,
) -> (HashMap<String, String>, HashMap<String, String>) {
    let case_insensitive_env: HashMap<_, _> = env
        .keys()
        .filter_map(|k| k.to_str())
        .map(|k| (k.to_uppercase(), k.to_owned()))
        .collect();

    let normalized_env = env
        .iter()
        // Only keep entries where both the key and value are valid UTF-8,
        // since the config env vars only support UTF-8 keys and values.
        // Otherwise, the normalized map warning could incorrectly warn about entries that can't be
        // read by the config system.
        // Please see the docs for `Env` for more context.
        .filter_map(|(k, v)| Some((k.to_str()?, v.to_str()?)))
        .map(|(k, _)| (k.to_uppercase().replace("-", "_"), k.to_owned()))
        .collect();
    (case_insensitive_env, normalized_env)
}

/// A snapshot of the environment variables available to [`GlobalContext`].
///
/// Currently, the [`GlobalContext`] supports lookup of environment variables
/// through two different means:
///
/// - [`GlobalContext::get_env`](super::GlobalContext::get_env)
///   and [`GlobalContext::get_env_os`](super::GlobalContext::get_env_os)
///   for process environment variables (similar to [`std::env::var`] and [`std::env::var_os`]),
/// - Typed Config Value API via [`GlobalContext::get`](super::GlobalContext::get).
///   This is only available for `CARGO_` prefixed environment keys.
///
/// This type contains the env var snapshot and helper methods for both APIs.
///
/// [`GlobalContext`]: super::GlobalContext
#[derive(Debug)]
pub struct Env {
    /// A snapshot of the process's environment variables.
    env: HashMap<OsString, OsString>,
    /// Used in the typed Config value API for warning messages when config keys are
    /// given in the wrong format.
    ///
    /// Maps from "normalized" (upper case and with "-" replaced by "_") env keys
    /// to the actual keys in the environment.
    /// The normalized format is the one expected by Cargo.
    ///
    /// This only holds env keys that are valid UTF-8, since [`super::ConfigKey`] only supports UTF-8 keys.
    /// In addition, this only holds env keys whose value in the environment is also valid UTF-8,
    /// since the typed Config value API only supports UTF-8 values.
    normalized_env: HashMap<String, String>,
    /// Used to implement `get_env` and `get_env_os` on Windows, where env keys are case-insensitive.
    ///
    /// Maps from uppercased env keys to the actual key in the environment.
    /// For example, this might hold a pair `("PATH", "Path")`.
    /// Currently only supports UTF-8 keys and values.
    case_insensitive_env: HashMap<String, String>,
}

impl Env {
    /// A bounded, already validated native command environment. This selects
    /// configuration bytes only; it imports no descriptor or SDK authority.
    pub(super) fn from_selected(variables: &cargo_util::EnvironmentInputs) -> Self {
        let mut env = variables
            .iter()
            .map(|(key, value)| (key.to_owned(), value.to_owned()))
            .collect();
        add_targo_config_compatibility_twins(&mut env, crate::is_targo_invocation());
        let (case_insensitive_env, normalized_env) = make_case_insensitive_and_normalized_env(&env);
        Self {
            env,
            case_insensitive_env,
            normalized_env,
        }
    }
    #[cfg(unix)]
    pub(super) fn matches_selected(&self, variables: &cargo_util::EnvironmentInputs) -> bool {
        self.env == Self::from_selected(variables).env
    }
    /// Closed measurement override in this ONE owned Cargo configuration
    /// snapshot. Preserve every native key/value; never mutate process-global
    /// environment or silently discard a competing caller's policy override.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn paired_ay_measurement(&mut self) -> CargoResult<()> {
        for name in [
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "CARGO_BUILD_RUSTFLAGS",
            "TARGO_BUILD_RUSTFLAGS",
            super::super::compiler::TRUST_TARGO_LANE_RUSTFLAGS_ENV,
        ] {
            if self.env.contains_key(OsStr::new(name)) {
                bail!("paired AY measurement refuses pre-existing policy channel {name}");
            }
        }
        self.env.insert(
            OsString::from("RUSTFLAGS"),
            OsString::from("-Ztrust-verify=off"),
        );
        let (case_insensitive_env, normalized_env) =
            make_case_insensitive_and_normalized_env(&self.env);
        self.case_insensitive_env = case_insensitive_env;
        self.normalized_env = normalized_env;
        Ok(())
    }
    /// Create a new `Env` from process's environment variables.
    pub fn new() -> Self {
        #[expect(clippy::disallowed_methods, reason = "seeds `GlobalContext::get_env`")]
        let mut env: HashMap<_, _> = std::env::vars_os().collect();
        add_targo_config_compatibility_twins(&mut env, crate::is_targo_invocation());
        let (case_insensitive_env, normalized_env) = make_case_insensitive_and_normalized_env(&env);
        Self {
            env,
            case_insensitive_env,
            normalized_env,
        }
    }

    /// Set the env directly from a `HashMap`.
    /// This should be used for debugging purposes only.
    pub(super) fn from_map(env: HashMap<String, String>) -> Self {
        Self::from_map_for_frontend(env, crate::is_targo_invocation())
    }

    fn from_map_for_frontend(env: HashMap<String, String>, native: bool) -> Self {
        let mut env = env.into_iter().map(|(k, v)| (k.into(), v.into())).collect();
        add_targo_config_compatibility_twins(&mut env, native);
        let (case_insensitive_env, normalized_env) = make_case_insensitive_and_normalized_env(&env);
        Self {
            env,
            case_insensitive_env,
            normalized_env,
        }
    }

    /// Returns all environment variables as an iterator,
    /// keeping only entries where both the key and value are valid UTF-8.
    pub fn iter_str(&self) -> impl Iterator<Item = (&str, &str)> {
        self.env
            .iter()
            .filter_map(|(k, v)| Some((k.to_str()?, v.to_str()?)))
    }

    /// Complete native environment snapshot. Equality checks must not discard
    /// non-Unicode names or values that an ordinary compiler can observe.
    pub(super) fn iter_os(&self) -> impl Iterator<Item = (&OsStr, &OsStr)> {
        self.env
            .iter()
            .map(|(key, value)| (key.as_os_str(), value.as_os_str()))
    }

    /// Returns all environment variable keys, filtering out keys that are not valid UTF-8.
    pub fn keys_str(&self) -> impl Iterator<Item = &str> {
        self.env.keys().filter_map(|k| k.to_str())
    }

    /// Get the value of environment variable `key` through the snapshot in
    /// [`GlobalContext`](super::GlobalContext).
    ///
    /// This can be used similarly to [`std::env::var_os`].
    /// On Windows, we check for case mismatch since environment keys are case-insensitive.
    pub fn get_env_os(&self, key: impl AsRef<OsStr>) -> Option<&OsStr> {
        match self.env.get(key.as_ref()) {
            Some(s) => Some(s),
            None => {
                if cfg!(windows) {
                    self.get_env_case_insensitive(key)
                } else {
                    None
                }
            }
        }
    }

    /// Get the value of environment variable `key` through the `self.env` snapshot.
    ///
    /// This can be used similarly to `std::env::var`.
    /// On Windows, we check for case mismatch since environment keys are case-insensitive.
    pub fn get_env(&self, key: impl AsRef<OsStr>) -> CargoResult<&str> {
        let key = key.as_ref();
        let s = self
            .get_env_os(key)
            .ok_or_else(|| anyhow!("{key:?} could not be found in the environment snapshot"))?;

        match s.to_str() {
            Some(s) => Ok(s),
            None => bail!("environment variable value is not valid unicode: {s:?}"),
        }
    }

    /// Performs a case-insensitive lookup of `key` in the environment.
    ///
    /// This is relevant on Windows, where environment variables are case-insensitive.
    /// Note that this only works on keys that are valid UTF-8 and it uses Unicode uppercase,
    /// which may differ from the OS's notion of uppercase.
    fn get_env_case_insensitive(&self, key: impl AsRef<OsStr>) -> Option<&OsStr> {
        let upper_case_key = key.as_ref().to_str()?.to_uppercase();
        let env_key: &OsStr = self.case_insensitive_env.get(&upper_case_key)?.as_ref();
        self.env.get(env_key).map(|v| v.as_ref())
    }

    /// Get the value of environment variable `key` as a `&str`.
    /// Returns `None` if `key` is not in `self.env` or if the value is not valid UTF-8.
    ///
    /// This is intended for use in private methods of [`GlobalContext`](super::GlobalContext),
    /// and does not check for env key case mismatch.
    ///
    /// This is case-sensitive on Windows (even though environment keys on Windows are usually
    /// case-insensitive) due to an unintended regression in 1.28 (via #5552).
    /// This should only affect keys used for cargo's config-system env variables (`CARGO_`
    /// prefixed ones), which are currently all uppercase.
    /// We may want to consider rectifying it if users report issues.
    /// One thing that adds a wrinkle here is the unstable advanced-env option that *requires*
    /// case-sensitive keys.
    ///
    /// Do not use this for any other purposes.
    /// Use [`Env::get_env_os`] or [`Env::get_env`] instead, which properly handle case
    /// insensitivity on Windows.
    pub(super) fn get_str(&self, key: impl AsRef<OsStr>) -> Option<&str> {
        self.env.get(key.as_ref()).and_then(|s| s.to_str())
    }

    /// Check if the environment contains `key`.
    ///
    /// This is intended for use in private methods of [`GlobalContext`](super::GlobalContext),
    /// and does not check for env key case mismatch.
    /// See the docstring of [`Env::get_str`] for more context.
    pub(super) fn contains_key(&self, key: impl AsRef<OsStr>) -> bool {
        self.env.contains_key(key.as_ref())
    }

    /// Looks up a normalized `key` in the `normalized_env`.
    /// Returns the corresponding (non-normalized) env key if it exists, else `None`.
    ///
    /// This is used by [`super::GlobalContext::check_environment_key_case_mismatch`].
    pub(super) fn get_normalized(&self, key: &str) -> Option<&str> {
        self.normalized_env.get(key).map(|s| s.as_ref())
    }
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod paired_measurement_tests {
    use super::*;
    use std::os::unix::ffi::OsStringExt as _;
    fn original() -> Env {
        let env = [
            (
                OsString::from("CARGO_HOME"),
                OsString::from("/original/cache"),
            ),
            (
                OsString::from_vec(b"NATIVE_KEY_\xff".to_vec()),
                OsString::from_vec(b"native value \xfe".to_vec()),
            ),
        ]
        .into_iter()
        .collect();
        let (case_insensitive_env, normalized_env) = make_case_insensitive_and_normalized_env(&env);
        Env {
            env,
            case_insensitive_env,
            normalized_env,
        }
    }
    #[test]
    fn native_equality_snapshot_retains_non_unicode_names_and_values() {
        let owned = original();
        let entries = owned.iter_os().collect::<Vec<_>>();
        assert_eq!(entries.len(), 2);
        let key = OsString::from_vec(b"NATIVE_KEY_\xff".to_vec());
        let value = OsString::from_vec(b"native value \xfe".to_vec());
        assert!(entries.contains(&(key.as_os_str(), value.as_os_str())));
        assert_eq!(owned.iter_str().count(), 1);
    }
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "observe before/after process environment without mutating it while testing an owned snapshot"
    )]
    fn closed_ay_flags_preserve_all_native_bytes_without_changing_process_environment() {
        let mut owned = original();
        let before = owned.env.clone();
        let process_before = std::env::var_os("RUSTFLAGS");
        owned.paired_ay_measurement().unwrap();
        for (name, value) in before {
            assert_eq!(owned.env.get(&name), Some(&value));
        }
        assert_eq!(
            owned.get_env_os("RUSTFLAGS"),
            Some(OsStr::new("-Ztrust-verify=off"))
        );
        assert_eq!(std::env::var_os("RUSTFLAGS"), process_before);
        assert!(
            owned.paired_ay_measurement().is_err(),
            "the owned selection is one-use"
        );
    }
    #[test]
    fn competing_policy_channels_refuse_without_mutating_the_original_snapshot() {
        for channel in [
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "CARGO_BUILD_RUSTFLAGS",
            "TARGO_BUILD_RUSTFLAGS",
            super::super::super::compiler::TRUST_TARGO_LANE_RUSTFLAGS_ENV,
        ] {
            let mut owned = original();
            owned.env.insert(channel.into(), "caller policy".into());
            let before = owned.env.clone();
            assert!(owned.paired_ay_measurement().is_err());
            assert_eq!(owned.env, before);
        }
    }
}

// Trust: pins that a native `TARGO_*` key reaches the inherited parser and
// that an explicit `CARGO_*` spelling still wins, so adding the native
// namespace cannot change what an existing project resolves to.
#[cfg(test)]
mod tests {
    use super::Env;
    use std::ffi::OsStr;

    #[test]
    fn native_targo_config_keys_feed_the_compatibility_parser_snapshot() {
        let env = Env::from_map_for_frontend(
            [
                ("TARGO_HOME".to_string(), "/native/home".to_string()),
                ("TARGO_NET_OFFLINE".to_string(), "true".to_string()),
                ("UNRELATED".to_string(), "preserved".to_string()),
            ]
            .into_iter()
            .collect(),
            true,
        );

        assert_eq!(
            env.get_env_os("TARGO_HOME"),
            Some(OsStr::new("/native/home"))
        );
        assert_eq!(
            env.get_env_os("CARGO_HOME"),
            Some(OsStr::new("/native/home"))
        );
        assert_eq!(
            env.get_env_os("CARGO_NET_OFFLINE"),
            Some(OsStr::new("true"))
        );
        assert_eq!(env.get_env_os("UNRELATED"), Some(OsStr::new("preserved")));
    }

    #[test]
    fn explicit_cargo_config_key_wins_over_its_native_twin() {
        let env = Env::from_map_for_frontend(
            [
                ("TARGO_HOME".to_string(), "/native/home".to_string()),
                ("CARGO_HOME".to_string(), "/compat/home".to_string()),
            ]
            .into_iter()
            .collect(),
            true,
        );

        assert_eq!(
            env.get_env_os("TARGO_HOME"),
            Some(OsStr::new("/native/home"))
        );
        assert_eq!(
            env.get_env_os("CARGO_HOME"),
            Some(OsStr::new("/compat/home"))
        );
    }
}

// Trust: output metadata remains available by its raw name, but never creates
// configuration inputs; the Cargo alias ignores the native namespace entirely.
#[cfg(test)]
mod frontend_namespace_tests {
    use super::Env;
    use std::ffi::OsStr;

    #[test]
    fn cargo_alias_keeps_native_keys_out_of_configuration() {
        let env = Env::from_map_for_frontend(
            [("TARGO_NET_OFFLINE".into(), "true".into())]
                .into_iter()
                .collect(),
            false,
        );
        assert_eq!(
            env.get_env_os("TARGO_NET_OFFLINE"),
            Some(OsStr::new("true"))
        );
        assert_eq!(env.get_env_os("CARGO_NET_OFFLINE"), None);
    }

    #[test]
    fn native_unit_metadata_does_not_become_configuration() {
        let keys = [
            "PKG_LICENSE_FILE",
            "MANIFEST_DIR",
            "COMMIT_HASH",
            "CFG_TARGET_OS",
            "FEATURE_TEST",
            "BIN_EXE_example",
            "CRATE_NAME",
            "BIN_NAME",
            "PRIMARY_PACKAGE",
        ];
        let env = Env::from_map_for_frontend(
            keys.iter()
                .map(|key| (format!("TARGO_{key}"), "parent".into()))
                .collect(),
            true,
        );
        for key in keys {
            assert_eq!(
                env.get_env_os(format!("TARGO_{key}")),
                Some(OsStr::new("parent"))
            );
            assert_eq!(env.get_env_os(format!("CARGO_{key}")), None);
        }
    }
}

#[cfg(test)]
mod original_home_tests {
    use super::Env;
    use std::path::{Path, PathBuf};
    #[test]
    fn original_home_keeps_explicit_empty_compatibility_selection_and_lazy_fallback() {
        let env = Env::from_map_for_frontend([
            ("TARGO_HOME".to_string(), "/native-home".to_string()),
            ("CARGO_HOME".to_string(), "".to_string()),
        ].into_iter().collect(), true);
        assert_eq!(super::super::homedir_with_environment(Path::new("/source"), &env,
            || Some(PathBuf::from("/original-os-home"))),
            Some(PathBuf::from("/original-os-home/.cargo")));
        let env = Env::from_map_for_frontend([
            ("TARGO_HOME".to_string(), "relative-native-home".to_string()),
        ].into_iter().collect(), true);
        assert_eq!(super::super::homedir_with_environment(Path::new("/source"), &env,
            || panic!("explicit native home must not consult the OS fallback")),
            Some(PathBuf::from("/source/relative-native-home")));
    }
    #[test]
    fn original_home_keeps_explicit_compatibility_precedence_without_mutating_environment() {
        let env = Env::from_map_for_frontend([
            ("TARGO_HOME".to_string(), "/native-home".to_string()),
            ("CARGO_HOME".to_string(), "/compatibility-home".to_string()),
        ].into_iter().collect(), true);
        assert_eq!(super::super::homedir_with_environment(Path::new("/source"), &env,
            || panic!("explicit compatibility home must not consult fallback")),
            Some(PathBuf::from("/compatibility-home")));
        assert_eq!(env.get_env_os("TARGO_HOME"), Some(std::ffi::OsStr::new("/native-home")));
    }
}
