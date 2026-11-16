//! This module defines the structures that directly mirror the `bootstrap.toml`
//! file's format. These types are used for `serde` deserialization.
//!
//! Crucially, this module also houses the core logic for loading, parsing, and merging
//! these raw TOML configurations from various sources (the main `bootstrap.toml`,
//! included files, profile defaults, and command-line overrides). This processed
//! TOML data then serves as an intermediate representation, which is further
//! transformed and applied to the final `Config` struct.

use serde::Deserialize;
// Trust: preserve standalone derives without colliding with serde/derive in
// the embedding's unified feature set.
use serde_derive::Deserialize as DeriveDeserialize;
pub mod build;
pub mod change_id;
pub mod dist;
pub mod install;
pub mod llvm;
pub mod pgo;
pub mod rust;
pub mod target;

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use build::Build;
use change_id::{ChangeId, ChangeIdWrapper};
use dist::Dist;
use install::Install;
use llvm::Llvm;
use rust::Rust;
use target::TomlTarget;

use crate::core::config::toml::pgo::Pgo;
use crate::core::config::{Config, Merge, ReplaceOpt};
use crate::utils::change_tracker::{find_recent_config_change_ids, human_readable_changes};
use crate::utils::helpers::{self, t};

/// Structure of the `bootstrap.toml` file that configuration is read from.
///
/// This structure uses `Decodable` to automatically decode a TOML configuration
/// file into this format, and then this is traversed and written into the above
/// `Config` structure.
#[derive(DeriveDeserialize, Default)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub(crate) struct TomlConfig {
    #[serde(flatten)]
    pub(crate) change_id: ChangeIdWrapper,
    pub(super) build: Option<Build>,
    pub(super) install: Option<Install>,
    pub(super) llvm: Option<Llvm>,
    pub(super) rust: Option<Rust>,
    pub(super) target: Option<HashMap<String, TomlTarget>>,
    pub(super) dist: Option<Dist>,
    pub(super) pgo: Option<Pgo>,
    pub(super) profile: Option<String>,
    pub(super) include: Option<Vec<PathBuf>>,
}

impl Merge for TomlConfig {
    fn merge(
        &mut self,
        parent_config_path: Option<PathBuf>,
        included_extensions: &mut HashSet<PathBuf>,
        TomlConfig {
            build,
            install,
            llvm,
            rust,
            dist,
            target,
            pgo,
            profile,
            change_id,
            include,
        }: Self,
        replace: ReplaceOpt,
    ) {
        fn do_merge<T: Merge>(x: &mut Option<T>, y: Option<T>, replace: ReplaceOpt) {
            if let Some(new) = y {
                if let Some(original) = x {
                    original.merge(None, &mut Default::default(), new, replace);
                } else {
                    *x = Some(new);
                }
            }
        }

        self.change_id.inner.merge(None, &mut Default::default(), change_id.inner, replace);
        self.profile.merge(None, &mut Default::default(), profile, replace);

        do_merge(&mut self.build, build, replace);
        do_merge(&mut self.install, install, replace);
        do_merge(&mut self.llvm, llvm, replace);
        do_merge(&mut self.rust, rust, replace);
        do_merge(&mut self.dist, dist, replace);
        do_merge(&mut self.pgo, pgo, replace);

        match (self.target.as_mut(), target) {
            (_, None) => {}
            (None, Some(target)) => self.target = Some(target),
            (Some(original_target), Some(new_target)) => {
                for (triple, new) in new_target {
                    if let Some(original) = original_target.get_mut(&triple) {
                        original.merge(None, &mut Default::default(), new, replace);
                    } else {
                        original_target.insert(triple, new);
                    }
                }
            }
        }

        let parent_dir = parent_config_path
            .as_ref()
            .and_then(|p| p.parent().map(ToOwned::to_owned))
            .unwrap_or_default();

        // `include` handled later since we ignore duplicates using `ReplaceOpt::IgnoreDuplicate` to
        // keep the upper-level configuration to take precedence.
        for include_path in include.clone().unwrap_or_default().iter().rev() {
            let include_path = parent_dir.join(include_path);
            let include_path = Config::canonicalize_toml_path(&include_path).unwrap_or_else(|e| {
                eprintln!("ERROR: Failed to canonicalize '{}' path: {e}", include_path.display());
                helpers::exit_process(2);
            });

            let included_toml = Config::get_toml_inner(&include_path).unwrap_or_else(|e| {
                eprintln!("ERROR: Failed to parse '{}': {e}", include_path.display());
                helpers::exit_process(2);
            });

            assert!(
                included_extensions.insert(include_path.clone()),
                "Cyclic inclusion detected: '{}' is being included again before its previous inclusion was fully processed.",
                include_path.display()
            );

            self.merge(
                Some(include_path.clone()),
                included_extensions,
                included_toml,
                // Ensures that parent configuration always takes precedence
                // over child configurations.
                ReplaceOpt::IgnoreDuplicate,
            );

            included_extensions.remove(&include_path);
        }
    }
}

/// This file is embedded in the overlay directory of the tarball sources. It is
/// useful in scenarios where developers want to see how the tarball sources were
/// generated.
///
/// We also use this file to compare the host's bootstrap.toml against the CI rustc builder
/// configuration to detect any incompatible options.
pub const BUILDER_CONFIG_FILENAME: &str = "builder-config";

impl Config {
    /// Project cache-location DATA through the normal strict Bootstrap parser.
    /// Includes/profile precedence is resolved by the caller while retaining
    /// every actual file read; this never parses or constructs build ownership.
    pub(crate) fn cache_output_fields(
        contents: &str,
    ) -> Result<(Option<String>, Vec<PathBuf>, Option<String>), toml::de::Error> {
        let config = Self::parse_toml_contents(contents)?;
        Ok((
            config.build.and_then(|build| build.build_dir),
            config.include.unwrap_or_default(),
            config.profile,
        ))
    }

    pub(crate) fn get_builder_toml(&self, build_name: &str) -> Result<TomlConfig, toml::de::Error> {
        if self.dry_run() {
            return Ok(TomlConfig::default());
        }

        let builder_config_path =
            self.out.join(self.host_target.triple).join(build_name).join(BUILDER_CONFIG_FILENAME);
        Self::get_toml(&builder_config_path)
    }

    pub(crate) fn get_toml(file: &Path) -> Result<TomlConfig, toml::de::Error> {
        Self::get_toml_inner(file)
    }

    pub(crate) fn get_toml_inner(file: &Path) -> Result<TomlConfig, toml::de::Error> {
        Self::get_toml_source(file, |_| {})
    }
    pub(crate) fn canonicalize_toml_path(file: &Path) -> std::io::Result<PathBuf> {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        crate::utils::metadata_scheduler::host_graph::check_original_configuration_path(file)?;
        file.canonicalize()
    }

    // The same ordinary parser selects every include/profile. A genuine
    // original preparation graph, when present, supplies those exact bytes
    // from its retained source/file issuer before they are interpreted.
    pub(crate) fn get_toml_source(
        file: &Path,
        mut observe: impl FnMut(&str),
    ) -> Result<TomlConfig, toml::de::Error> {
        let mut parse = |contents: &str| {
            observe(contents);
            Self::parse_toml_contents(contents)
        };
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Some(result) =
            t!(crate::utils::metadata_scheduler::host_graph::with_original_configuration(
                file, &mut parse
            ))
        {
            return result;
        }
        let contents =
            t!(Self::read_source_text(file), format!("config file {} not found", file.display()));
        parse(&contents)
    }

    // Trust: native input binding parses the exact string whose digest it keeps.
    pub(crate) fn parse_toml_contents(contents: &str) -> Result<TomlConfig, toml::de::Error> {
        // Deserialize to Value and then TomlConfig to prevent the Deserialize impl of
        // TomlConfig and sub types to be monomorphized 5x by toml.
        toml::from_str(&contents)
            .and_then(|table: toml::Value| TomlConfig::deserialize(table))
            .inspect_err(|_| {
                if let Ok(ChangeIdWrapper { inner: Some(ChangeId::Id(id)) }) =
                    toml::from_str::<toml::Value>(&contents)
                        .and_then(|table: toml::Value| ChangeIdWrapper::deserialize(table))
                {
                    let changes = find_recent_config_change_ids(id);
                    if !changes.is_empty() {
                        println!(
                            "WARNING: There have been changes to x.py since you last updated:\n{}",
                            human_readable_changes(changes)
                        );
                    }
                }
            })
    }
}
