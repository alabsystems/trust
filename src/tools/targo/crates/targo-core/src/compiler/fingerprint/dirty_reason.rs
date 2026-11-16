use crate::util::data_structures::HashMap;
use std::fmt;
use std::fmt::Debug;

use serde::Serialize;

use super::*;
use crate::compiler::UnitIndex;
use crate::context::FingerprintMethod;
use cargo_util_terminal::Shell;

/// Tells a better story of why a build is considered "dirty" that leads
/// to a recompile. Usually constructed via [`Fingerprint::compare`].
///
/// [`Fingerprint::compare`]: super::Fingerprint::compare
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "dirty_reason", rename_all = "kebab-case")]
pub enum DirtyReason {
    RustcChanged,
    FeaturesChanged {
        old: String,
        new: String,
    },
    DeclaredFeaturesChanged {
        old: String,
        new: String,
    },
    TargetConfigurationChanged,
    PathToSourceChanged,
    ProfileConfigurationChanged,
    RustflagsChanged {
        old: Vec<String>,
        new: Vec<String>,
    },
    ConfigSettingsChanged,
    CompileKindChanged,
    LocalLengthsChanged,
    PrecalculatedComponentsChanged {
        old: String,
        new: String,
    },
    FingerprintMethodChanged {
        old: FingerprintMethod,
        new: FingerprintMethod,
    },
    DepInfoOutputChanged {
        old: PathBuf,
        new: PathBuf,
    },
    RerunIfChangedOutputFileChanged {
        old: PathBuf,
        new: PathBuf,
    },
    RerunIfChangedOutputPathsChanged {
        old: Vec<PathBuf>,
        new: Vec<PathBuf>,
    },
    EnvVarsChanged {
        old: String,
        new: String,
    },
    EnvVarChanged {
        name: String,
        old_value: Option<String>,
        new_value: Option<String>,
    },
    LocalFingerprintTypeChanged {
        old: String,
        new: String,
    },
    NumberOfDependenciesChanged {
        old: usize,
        new: usize,
    },
    UnitDependencyNameChanged {
        old: InternedString,
        new: InternedString,
    },
    UnitDependencyInfoChanged {
        unit: UnitIndex,
    },
    FsStatusOutdated(FsStatus),
    /// Trust: an existing content key or complete record does not match.
    /// This does not identify which input, setting, or record byte changed.
    ContentFingerprintChanged,
    /// Trust: an existing bounded content record could not be inspected.
    ContentFingerprintUnavailable,
    /// Trust: persisted key and decoded record disagree under this Targo.
    FingerprintRecordMismatch,
    NothingObvious,
    Forced,
    /// First time to build something.
    FreshBuild,
}

trait ShellExt {
    fn dirty_because(&mut self, unit: &Unit, s: impl fmt::Display) -> CargoResult<()>;
}

impl ShellExt for Shell {
    fn dirty_because(&mut self, unit: &Unit, s: impl fmt::Display) -> CargoResult<()> {
        self.status("Dirty", format_args!("{}: {s}", &unit.pkg))
    }
}

struct FileTimeDiff {
    old_time: FileTime,
    new_time: FileTime,
}

impl fmt::Display for FileTimeDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s_diff = self.new_time.seconds() - self.old_time.seconds();
        if s_diff >= 1 {
            write!(f, "{:#}", jiff::SignedDuration::from_secs(s_diff))
        } else {
            // format nanoseconds as it is, jiff would display ms, us and ns
            let ns_diff = self.new_time.nanoseconds() - self.old_time.nanoseconds();
            write!(f, "{ns_diff}ns")
        }
    }
}

#[derive(Copy, Clone)]
struct After {
    old_time: FileTime,
    new_time: FileTime,
    what: &'static str,
}

impl fmt::Display for After {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            old_time,
            new_time,
            what,
        } = *self;
        let diff = FileTimeDiff { old_time, new_time };

        write!(f, "{new_time}, {diff} after {what} at {old_time}")
    }
}

impl DirtyReason {
    // Trust: serialize only the actual typed category, never diagnostic payloads.
    pub(crate) fn dispatch_cause(&self) -> crate::util::machine_message::UnitRebuildCause {
        use crate::util::machine_message::UnitRebuildCause as Cause;
        match self {
            Self::RustcChanged => Cause::RustcChanged,
            Self::FeaturesChanged { .. } => Cause::FeaturesChanged,
            Self::DeclaredFeaturesChanged { .. } => Cause::DeclaredFeaturesChanged,
            Self::TargetConfigurationChanged => Cause::TargetConfigurationChanged,
            Self::PathToSourceChanged => Cause::PathToSourceChanged,
            Self::ProfileConfigurationChanged => Cause::ProfileConfigurationChanged,
            Self::RustflagsChanged { .. } => Cause::RustflagsChanged,
            Self::ConfigSettingsChanged => Cause::ConfigSettingsChanged,
            Self::CompileKindChanged => Cause::CompileKindChanged,
            Self::LocalLengthsChanged => Cause::LocalLengthsChanged,
            Self::PrecalculatedComponentsChanged { .. } => Cause::PrecalculatedComponentsChanged,
            Self::FingerprintMethodChanged { .. } => Cause::FingerprintMethodChanged,
            Self::DepInfoOutputChanged { .. } => Cause::DepInfoOutputChanged,
            Self::RerunIfChangedOutputFileChanged { .. } => Cause::RerunIfChangedOutputFileChanged,
            Self::RerunIfChangedOutputPathsChanged { .. } => {
                Cause::RerunIfChangedOutputPathsChanged
            }
            Self::EnvVarsChanged { .. } => Cause::EnvVarsChanged,
            Self::EnvVarChanged { .. } => Cause::EnvVarChanged,
            Self::LocalFingerprintTypeChanged { .. } => Cause::LocalFingerprintTypeChanged,
            Self::NumberOfDependenciesChanged { .. } => Cause::NumberOfDependenciesChanged,
            Self::UnitDependencyNameChanged { .. } => Cause::UnitDependencyNameChanged,
            Self::UnitDependencyInfoChanged { .. } => Cause::UnitDependencyInfoChanged,
            Self::ContentFingerprintChanged => Cause::ContentFingerprintChanged,
            Self::ContentFingerprintUnavailable => Cause::ContentFingerprintUnavailable,
            Self::FingerprintRecordMismatch => Cause::FingerprintRecordMismatch,
            Self::FsStatusOutdated(status) => match status {
                FsStatus::Stale | FsStatus::UpToDate { .. } => Cause::Unknown,
                FsStatus::StaleDependency { .. } => Cause::StaleDependency,
                FsStatus::StaleDepFingerprint { .. } => Cause::StaleDepFingerprint,
                FsStatus::StaleItem(item) => match item {
                    StaleItem::MissingFile { .. } => Cause::MissingFile,
                    StaleItem::UnableToReadFile { .. } => Cause::UnableToReadFile,
                    // Trust: withhold the existing content-fact category, never invent I/O.
                    StaleItem::BuildScriptInputsUnavailable { .. } => {
                        Cause::ContentFingerprintUnavailable
                    }
                    // Trust: retain the actual cache rejection category without its payload.
                    StaleItem::DepInfoUnavailable { reason, .. } => match reason {
                        DepInfoUnavailable::Missing => Cause::MissingFile,
                        DepInfoUnavailable::Unreadable => Cause::UnableToReadFile,
                        DepInfoUnavailable::Malformed => Cause::DepInfoMalformed,
                        DepInfoUnavailable::FilenameInventoryIncomplete => {
                            Cause::ContentFingerprintUnavailable
                        }
                        DepInfoUnavailable::FormatMismatch { .. } => Cause::DepInfoFormatMismatch,
                        DepInfoUnavailable::RelocationRootUnavailable => {
                            Cause::DepInfoRelocationRootUnavailable
                        }
                    },
                    StaleItem::OutputIntegrity { .. } => Cause::OutputIntegrity,
                    StaleItem::FailedToReadMetadata { .. } => Cause::FailedToReadMetadata,
                    StaleItem::FileSizeChanged { .. } => Cause::FileSizeChanged,
                    StaleItem::ChangedFile { .. } => Cause::ChangedFile,
                    StaleItem::ChangedChecksum { .. } => Cause::ChangedChecksum,
                    StaleItem::MissingChecksum { .. } => Cause::MissingChecksum,
                    StaleItem::ModuleCandidateChanged { .. } => Cause::ModuleCandidateChanged,
                    StaleItem::ChangedEnv { .. } => Cause::ChangedEnv,
                },
            },
            Self::NothingObvious => Cause::Unknown,
            Self::Forced => Cause::Forced,
            Self::FreshBuild => Cause::FreshBuild,
        }
    }

    /// Whether a build is dirty because it is a fresh build being kicked off.
    pub fn is_fresh_build(&self) -> bool {
        matches!(self, DirtyReason::FreshBuild)
    }

    fn after(old_time: FileTime, new_time: FileTime, what: &'static str) -> After {
        After {
            old_time,
            new_time,
            what,
        }
    }

    pub fn present_to(
        &self,
        s: &mut Shell,
        unit: &Unit,
        root: &Path,
        index_to_unit: &HashMap<UnitIndex, Unit>,
    ) -> CargoResult<()> {
        match self {
            DirtyReason::RustcChanged => s.dirty_because(unit, "the toolchain changed"),
            DirtyReason::FeaturesChanged { .. } => {
                s.dirty_because(unit, "the list of features changed")
            }
            DirtyReason::DeclaredFeaturesChanged { .. } => {
                s.dirty_because(unit, "the list of declared features changed")
            }
            DirtyReason::TargetConfigurationChanged => {
                s.dirty_because(unit, "the target configuration changed")
            }
            DirtyReason::PathToSourceChanged => {
                s.dirty_because(unit, "the path to the source changed")
            }
            DirtyReason::ProfileConfigurationChanged => {
                s.dirty_because(unit, "the profile configuration changed")
            }
            DirtyReason::RustflagsChanged { .. } => s.dirty_because(unit, "the rustflags changed"),
            DirtyReason::ConfigSettingsChanged => {
                s.dirty_because(unit, "the config settings changed")
            }
            DirtyReason::CompileKindChanged => {
                s.dirty_because(unit, "the rustc compile kind changed")
            }
            DirtyReason::LocalLengthsChanged => {
                s.dirty_because(unit, "the local lengths changed")?;
                s.note(
                    "this could happen because of added/removed `cargo::rerun-if` instructions in the build script",
                )?;

                Ok(())
            }
            DirtyReason::PrecalculatedComponentsChanged { .. } => {
                s.dirty_because(unit, "the precalculated components changed")
            }
            DirtyReason::FingerprintMethodChanged { old, new } => s.dirty_because(
                unit,
                format_args!("the prior compilation fingerprinted build inputs using `{old}` and this one used `{new}`"),
            ),
            DirtyReason::DepInfoOutputChanged { .. } => {
                s.dirty_because(unit, "the dependency info output changed")
            }
            DirtyReason::RerunIfChangedOutputFileChanged { .. } => {
                s.dirty_because(unit, "rerun-if-changed output file path changed")
            }
            DirtyReason::RerunIfChangedOutputPathsChanged { .. } => {
                s.dirty_because(unit, "the rerun-if-changed instructions changed")
            }
            DirtyReason::EnvVarsChanged { .. } => {
                s.dirty_because(unit, "the environment variables changed")
            }
            DirtyReason::EnvVarChanged { name, .. } => {
                s.dirty_because(unit, format_args!("the env variable {name} changed"))
            }
            DirtyReason::LocalFingerprintTypeChanged { .. } => {
                s.dirty_because(unit, "the local fingerprint type changed")
            }
            DirtyReason::NumberOfDependenciesChanged { old, new } => s.dirty_because(
                unit,
                format_args!("number of dependencies changed ({old} => {new})",),
            ),
            DirtyReason::UnitDependencyNameChanged { old, new } => s.dirty_because(
                unit,
                format_args!("name of dependency changed ({old} => {new})"),
            ),
            DirtyReason::UnitDependencyInfoChanged { unit: dep_unit } => {
                let dep_name = index_to_unit.get(dep_unit).map(|u| u.pkg.name()).unwrap();
                s.dirty_because(
                    unit,
                    format_args!("info of dependency `{dep_name}` changed"),
                )
            }
            DirtyReason::FsStatusOutdated(status) => match status {
                FsStatus::Stale => s.dirty_because(unit, "stale, unknown reason"),
                FsStatus::StaleItem(item) => match item {
                    StaleItem::MissingFile { path } => {
                        let file = path.strip_prefix(root).unwrap_or(&path);
                        s.dirty_because(
                            unit,
                            format_args!("the file `{}` is missing", file.display()),
                        )
                    }
                    StaleItem::UnableToReadFile { path } => {
                        let file = path.strip_prefix(root).unwrap_or(&path);
                        s.dirty_because(
                            unit,
                            format_args!("the file `{}` could not be read", file.display()),
                        )
                    }
                    // Trust: the output path is only the script's diagnostic anchor.
                    StaleItem::BuildScriptInputsUnavailable { output_anchor } => {
                        let output = output_anchor.strip_prefix(root).unwrap_or(output_anchor);
                        s.dirty_because(
                            unit,
                            format_args!(
                                "build-script input observation is unavailable or invalid (output anchor `{}`)",
                                output.display()
                            ),
                        )
                    }
                    // Trust: present but unusable dependency caches are not missing files.
                    StaleItem::DepInfoUnavailable { path, reason } => {
                        let file = path.strip_prefix(root).unwrap_or(path);
                        s.dirty_because(
                            unit,
                            format_args!("dependency cache `{}`: {reason}", file.display()),
                        )
                    }
                    StaleItem::OutputIntegrity { path, reason } => s.dirty_because(
                        unit,
                        format_args!("cached output integrity failed at `{}`: {reason}", path.display()),
                    ),
                    StaleItem::FailedToReadMetadata { path } => {
                        let file = path.strip_prefix(root).unwrap_or(&path);
                        s.dirty_because(
                            unit,
                            format_args!("couldn't read metadata for file `{}`", file.display()),
                        )
                    }
                    StaleItem::ChangedFile {
                        stale,
                        stale_mtime,
                        reference_mtime,
                        ..
                    } => {
                        let file = stale.strip_prefix(root).unwrap_or(&stale);
                        let after = Self::after(*reference_mtime, *stale_mtime, "last build");
                        s.dirty_because(
                            unit,
                            format_args!("the file `{}` has changed ({after})", file.display()),
                        )
                    }
                    StaleItem::ChangedChecksum {
                        source,
                        stored_checksum,
                        new_checksum,
                    } => {
                        let file = source.strip_prefix(root).unwrap_or(&source);
                        s.dirty_because(
                            unit,
                            format_args!(
                                "the file `{}` has changed (checksum didn't match, {stored_checksum} != {new_checksum})",
                                file.display(),
                            ),
                        )
                    }
                    StaleItem::FileSizeChanged {
                        path,
                        old_size,
                        new_size,
                    } => {
                        let file = path.strip_prefix(root).unwrap_or(&path);
                        s.dirty_because(
                            unit,
                            format_args!(
                                "file size changed ({old_size} != {new_size}) for `{}`",
                                file.display()
                            ),
                        )
                    }
                    StaleItem::MissingChecksum { path } => {
                        let file = path.strip_prefix(root).unwrap_or(&path);
                        s.dirty_because(
                            unit,
                            format_args!("the checksum for file `{}` is missing", file.display()),
                        )
                    }
                    StaleItem::ModuleCandidateChanged { path, previous, current } => {
                        let file = path.strip_prefix(root).unwrap_or(path);
                        let state = |present| match present {
                            Some(false) => "absent", Some(true) => "present", None => "unavailable",
                        };
                        s.dirty_because(unit, format_args!(
                            "Rust module candidate `{}` changed ({} -> {})",
                            file.display(), state(*previous), state(*current),
                        ))
                    }
                    StaleItem::ChangedEnv { var, .. } => s.dirty_because(
                        unit,
                        format_args!("the environment variable {var} changed"),
                    ),
                },
                FsStatus::StaleDependency {
                    unit: dep_unit,
                    dep_mtime,
                    max_mtime,
                } => {
                    let dep_name = index_to_unit.get(dep_unit).map(|u| u.pkg.name()).unwrap();
                    let after = Self::after(*max_mtime, *dep_mtime, "last build");
                    s.dirty_because(
                        unit,
                        format_args!("the dependency `{dep_name}` was rebuilt ({after})"),
                    )
                }
                FsStatus::StaleDepFingerprint { unit: dep_unit } => {
                    let dep_name = index_to_unit.get(dep_unit).map(|u| u.pkg.name()).unwrap();
                    s.dirty_because(
                        unit,
                        format_args!("the dependency `{dep_name}` was rebuilt"),
                    )
                }
                FsStatus::UpToDate { .. } => {
                    unreachable!()
                }
            },
            DirtyReason::NothingObvious => {
                // See comment in fingerprint compare method.
                s.dirty_because(unit, "the fingerprint comparison turned up nothing obvious")
            }
            DirtyReason::ContentFingerprintChanged => {
                s.dirty_because(unit, "the recorded content fingerprint does not match")
            }
            DirtyReason::ContentFingerprintUnavailable => {
                s.dirty_because(unit, "the recorded content fingerprint could not be read")
            }
            DirtyReason::FingerprintRecordMismatch => {
                s.dirty_because(unit, "the recorded fingerprint key and data disagree")
            }
            DirtyReason::Forced => s.dirty_because(unit, "forced"),
            DirtyReason::FreshBuild => s.dirty_because(unit, "fresh build"),
        }
    }
}

// These test the actual JSON structure that will be logged.
// In the future we might decouple this from the actual log message schema.
#[cfg(test)]
// Trust: typed dispatch telemetry never upgrades an unknown cause or carries secrets.
mod dispatch_tests {
    use super::*;
    use crate::util::machine_message::{
        CompilationUnitDispatched, Message as _, TRUST_UNIT_DISPATCH_SCHEMA_V1, UnitRebuildCause,
    };

    #[test]
    fn unresolved_dispatch_causes_remain_unknown_and_fresh_build_is_not_fresh_reuse() {
        for reason in [
            DirtyReason::NothingObvious,
            DirtyReason::FsStatusOutdated(FsStatus::Stale),
            DirtyReason::FsStatusOutdated(FsStatus::UpToDate {
                mtimes: HashMap::default(),
            }),
        ] {
            assert_eq!(reason.dispatch_cause(), UnitRebuildCause::Unknown);
        }
        assert_eq!(
            DirtyReason::FreshBuild.dispatch_cause(),
            UnitRebuildCause::FreshBuild
        );
        for (reason, expected) in [
            (
                DirtyReason::ContentFingerprintChanged,
                UnitRebuildCause::ContentFingerprintChanged,
            ),
            (
                DirtyReason::ContentFingerprintUnavailable,
                UnitRebuildCause::ContentFingerprintUnavailable,
            ),
            (
                DirtyReason::FingerprintRecordMismatch,
                UnitRebuildCause::FingerprintRecordMismatch,
            ),
        ] {
            assert!(!reason.is_fresh_build());
            assert_eq!(reason.dispatch_cause(), expected);
        }
    }

    #[test]
    fn dispatch_categories_discard_environment_paths_and_flag_values() {
        let secret = "DO_NOT_SERIALIZE_SECRET_VALUE";
        let reasons = [
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                    StaleItem::ModuleCandidateChanged {
                        path: PathBuf::from(secret),
                        previous: Some(false),
                        current: Some(true),
                    },
                )),
                UnitRebuildCause::ModuleCandidateChanged,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::OutputIntegrity {
                    path: PathBuf::from(secret),
                    reason: secret.into(),
                })),
                UnitRebuildCause::OutputIntegrity,
            ),
            (
                DirtyReason::EnvVarChanged {
                    name: secret.into(),
                    old_value: Some(secret.into()),
                    new_value: Some(secret.into()),
                },
                UnitRebuildCause::EnvVarChanged,
            ),
            (
                DirtyReason::RustflagsChanged {
                    old: vec![secret.into()],
                    new: vec![secret.into()],
                },
                UnitRebuildCause::RustflagsChanged,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::ChangedEnv {
                    var: secret.into(),
                    previous: Some(secret.into()),
                    current: Some(secret.into()),
                })),
                UnitRebuildCause::ChangedEnv,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::MissingFile {
                    path: PathBuf::from(secret),
                })),
                UnitRebuildCause::MissingFile,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: PathBuf::from(secret),
                    reason: DepInfoUnavailable::Missing,
                })),
                UnitRebuildCause::MissingFile,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: PathBuf::from(secret),
                    reason: DepInfoUnavailable::Unreadable,
                })),
                UnitRebuildCause::UnableToReadFile,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
                    StaleItem::BuildScriptInputsUnavailable {
                        output_anchor: PathBuf::from(secret),
                    },
                )),
                UnitRebuildCause::ContentFingerprintUnavailable,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: PathBuf::from(secret),
                    reason: DepInfoUnavailable::Malformed,
                })),
                UnitRebuildCause::DepInfoMalformed,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: PathBuf::from(secret),
                    reason: DepInfoUnavailable::FormatMismatch {
                        recorded: 2,
                        current: 3,
                    },
                })),
                UnitRebuildCause::DepInfoFormatMismatch,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: PathBuf::from(secret),
                    reason: DepInfoUnavailable::RelocationRootUnavailable,
                })),
                UnitRebuildCause::DepInfoRelocationRootUnavailable,
            ),
            (
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: PathBuf::from(secret),
                    reason: DepInfoUnavailable::FilenameInventoryIncomplete,
                })),
                UnitRebuildCause::ContentFingerprintUnavailable,
            ),
        ];
        for (reason, expected) in reasons {
            assert_eq!(reason.dispatch_cause(), expected);
            let message = CompilationUnitDispatched {
                schema: TRUST_UNIT_DISPATCH_SCHEMA_V1,
                trust_unit_identity_sha256: &"a".repeat(64),
                trust_compile_mode: "build",
                trust_compile_kind: "host",
                fresh: false,
                dirty_reason: Some(reason.dispatch_cause()),
            }
            .to_json_string();
            assert!(!message.contains(secret));
            assert!(
                message.len() < 512,
                "a diagnostic payload must not enlarge the dispatch record"
            );
            let value: serde_json::Value = serde_json::from_str(&message).unwrap();
            assert_eq!(value["fresh"], false);
            assert!(value["dirty_reason"].is_string());
            assert!(value.get("path").is_none());
            assert!(value.get("recorded").is_none());
            assert!(value.get("current").is_none());
        }
    }
}

#[cfg(test)]
mod json_schema {
    use super::*;
    use snapbox::IntoData;
    use snapbox::assert_data_eq;
    use snapbox::str;

    fn to_json<T: Serialize>(value: &T) -> String {
        serde_json::to_string_pretty(value).unwrap()
    }

    #[test]
    fn rustc_changed() {
        let reason = DirtyReason::RustcChanged;
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "rustc-changed"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fresh_build() {
        let reason = DirtyReason::FreshBuild;
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fresh-build"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn forced() {
        let reason = DirtyReason::Forced;
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "forced"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn nothing_obvious() {
        let reason = DirtyReason::NothingObvious;
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "nothing-obvious"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn features_changed() {
        let reason = DirtyReason::FeaturesChanged {
            old: "f1".to_string(),
            new: "f1,f2".to_string(),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "features-changed",
  "new": "f1,f2",
  "old": "f1"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn rustflags_changed() {
        let reason = DirtyReason::RustflagsChanged {
            old: vec!["-C".into(), "opt-level=2".into()],
            new: vec!["--cfg".into(), "tokio_unstable".into()],
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "rustflags-changed",
  "old": [
    "-C",
    "opt-level=2"
  ],
  "new": [
    "--cfg",
    "tokio_unstable"
  ]
}
"#]]
        );
    }

    #[test]
    fn env_var_changed_both_some() {
        let reason = DirtyReason::EnvVarChanged {
            name: "VAR".into(),
            old_value: Some("old".into()),
            new_value: Some("new".into()),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "env-var-changed",
  "name": "VAR",
  "new_value": "new",
  "old_value": "old"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn env_var_changed_old_none() {
        let reason = DirtyReason::EnvVarChanged {
            name: "VAR".into(),
            old_value: None,
            new_value: Some("new".into()),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "env-var-changed",
  "name": "VAR",
  "new_value": "new",
  "old_value": null
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn dep_info_output_changed() {
        let reason = DirtyReason::DepInfoOutputChanged {
            old: "target/debug/old.d".into(),
            new: "target/debug/new.d".into(),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "dep-info-output-changed",
  "old": "target/debug/old.d",
  "new": "target/debug/new.d"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn number_of_dependencies_changed() {
        let reason = DirtyReason::NumberOfDependenciesChanged { old: 5, new: 7 };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "number-of-dependencies-changed",
  "old": 5,
  "new": 7
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn unit_dependency_name_changed() {
        let reason = DirtyReason::UnitDependencyNameChanged {
            old: "old_dep".into(),
            new: "new_dep".into(),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "unit-dependency-name-changed",
  "new": "new_dep",
  "old": "old_dep"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn unit_dependency_info_changed() {
        let reason = DirtyReason::UnitDependencyInfoChanged {
            unit: UnitIndex(15),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "unit-dependency-info-changed",
  "unit": 15
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fs_status_stale() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::Stale);
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fs_status_missing_file() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::MissingFile {
            path: "src/lib.rs".into(),
        }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "path": "src/lib.rs",
  "stale_item": "missing-file"
}
"#]]
            .is_json()
        );
    }

    // Trust: analysis logs retain the typed cause that dispatch intentionally omits.
    #[test]
    fn fs_status_dep_info_unavailable_preserves_typed_reason() {
        for unavailable in [
            DepInfoUnavailable::Missing,
            DepInfoUnavailable::Unreadable,
            DepInfoUnavailable::Malformed,
            DepInfoUnavailable::FormatMismatch {
                recorded: 2,
                current: 3,
            },
            DepInfoUnavailable::RelocationRootUnavailable,
            DepInfoUnavailable::FilenameInventoryIncomplete,
        ] {
            let reason =
                DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::DepInfoUnavailable {
                    path: "target/debug/fingerprint/dep-bin-foo".into(),
                    reason: unavailable.clone(),
                }));
            let encoded = serde_json::to_value(&reason).unwrap();
            assert_eq!(encoded["stale_item"], "dep-info-unavailable");
            assert_eq!(encoded["path"], "target/debug/fingerprint/dep-bin-foo");
            assert_eq!(
                encoded["reason"],
                serde_json::to_value(unavailable).unwrap()
            );
            let decoded: DirtyReason = serde_json::from_value(encoded.clone()).unwrap();
            assert_eq!(serde_json::to_value(decoded).unwrap(), encoded);
        }
    }

    #[test]
    fn fs_status_changed_file() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::ChangedFile {
            reference: "target/debug/deps/libfoo-abc123.rmeta".into(),
            reference_mtime: FileTime::from_unix_time(1730567890, 123000000),
            stale: "src/lib.rs".into(),
            stale_mtime: FileTime::from_unix_time(1730567891, 456000000),
        }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "reference": "target/debug/deps/libfoo-abc123.rmeta",
  "reference_mtime": 1730567890123.0,
  "stale": "src/lib.rs",
  "stale_item": "changed-file",
  "stale_mtime": 1730567891456.0
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fs_status_changed_checksum() {
        use super::dep_info::ChecksumAlgo;
        let reason =
            DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::ChangedChecksum {
                source: "src/main.rs".into(),
                stored_checksum: Checksum::new(ChecksumAlgo::Sha256, [0xaa; 32]),
                new_checksum: Checksum::new(ChecksumAlgo::Sha256, [0xbb; 32]),
            }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "new_checksum": "sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "source": "src/main.rs",
  "stale_item": "changed-checksum",
  "stored_checksum": "sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fs_status_stale_dependency() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::StaleDependency {
            unit: UnitIndex(42),
            dep_mtime: FileTime::from_unix_time(1730567892, 789000000),
            max_mtime: FileTime::from_unix_time(1730567890, 123000000),
        });
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dep_mtime": 1730567892789.0,
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-dependency",
  "max_mtime": 1730567890123.0,
  "unit": 42
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fs_status_stale_dep_fingerprint() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::StaleDepFingerprint {
            unit: UnitIndex(42),
        });
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-dep-fingerprint",
  "unit": 42
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn fs_status_unable_to_read_file() {
        let reason =
            DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::UnableToReadFile {
                path: "src/lib.rs".into(),
            }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "stale_item": "unable-to-read-file",
  "path": "src/lib.rs"
}
"#]]
        );
    }

    // Trust: preserve the actual unavailable-input category and identify an
    // output anchor without claiming a file was missing or unreadable.
    #[test]
    fn fs_status_build_script_inputs_unavailable() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::StaleItem(
            StaleItem::BuildScriptInputsUnavailable {
                output_anchor: "build/script/run/stdout".into(),
            },
        ));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "stale_item": "build-script-inputs-unavailable",
  "output_anchor": "build/script/run/stdout"
}
"#]]
        );
    }

    #[test]
    fn fs_status_failed_to_read_metadata() {
        let reason =
            DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::FailedToReadMetadata {
                path: "src/lib.rs".into(),
            }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "stale_item": "failed-to-read-metadata",
  "path": "src/lib.rs"
}
"#]]
        );
    }

    #[test]
    fn fs_status_file_size_changed() {
        let reason =
            DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::FileSizeChanged {
                path: "src/lib.rs".into(),
                old_size: 1024,
                new_size: 2048,
            }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "stale_item": "file-size-changed",
  "path": "src/lib.rs",
  "old_size": 1024,
  "new_size": 2048
}
"#]]
        );
    }

    #[test]
    fn fs_status_missing_checksum() {
        let reason =
            DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::MissingChecksum {
                path: "src/lib.rs".into(),
            }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "stale_item": "missing-checksum",
  "path": "src/lib.rs"
}
"#]]
        );
    }

    #[test]
    fn fs_status_changed_env() {
        let reason = DirtyReason::FsStatusOutdated(FsStatus::StaleItem(StaleItem::ChangedEnv {
            var: "VAR".into(),
            previous: Some("old".into()),
            current: Some("new".into()),
        }));
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fs-status-outdated",
  "fs_status": "stale-item",
  "stale_item": "changed-env",
  "var": "VAR",
  "previous": "old",
  "current": "new"
}
"#]]
        );
    }

    #[test]
    fn fingerprint_method_changed() {
        let reason = DirtyReason::FingerprintMethodChanged {
            old: FingerprintMethod::Mtime,
            new: FingerprintMethod::Content,
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "fingerprint-method-changed",
  "new": "content",
  "old": "mtime"
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn rerun_if_changed_output_paths_changed() {
        let reason = DirtyReason::RerunIfChangedOutputPathsChanged {
            old: vec!["file1.txt".into(), "file2.txt".into()],
            new: vec!["file1.txt".into(), "file2.txt".into(), "file3.txt".into()],
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "rerun-if-changed-output-paths-changed",
  "old": [
    "file1.txt",
    "file2.txt"
  ],
  "new": [
    "file1.txt",
    "file2.txt",
    "file3.txt"
  ]
}
"#]]
            .is_json()
        );
    }

    #[test]
    fn local_fingerprint_type_changed() {
        let reason = DirtyReason::LocalFingerprintTypeChanged {
            old: "precalculated".to_owned(),
            new: "rerun-if-changed".to_owned(),
        };
        assert_data_eq!(
            to_json(&reason),
            str![[r#"
{
  "dirty_reason": "local-fingerprint-type-changed",
  "new": "rerun-if-changed",
  "old": "precalculated"
}
"#]]
            .is_json()
        );
    }
}
