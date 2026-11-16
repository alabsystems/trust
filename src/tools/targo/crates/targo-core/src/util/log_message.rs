//! Messages for logging.

use std::borrow::Cow;
use std::io::Write;
use std::path::PathBuf;

use cargo_util_schemas::core::PackageIdSpec;
use jiff::Timestamp;
use serde::Deserialize;
use serde::Serialize;

use crate::compiler::CompileMode;
use crate::compiler::UnitIndex;
use crate::compiler::fingerprint::DirtyReason;

// Trust: diagnostic work observations never enter a compiler fingerprint.
pub const INPUT_WORK_VERSION: u32 = 1;
// Trust: compile-queue outcomes are observations, never proof or test verdicts.
pub const EXECUTION_VERSION: u32 = 1;
// Trust: declares complete primary-process observations, separately from
// dispatch. An old log without this declaration never establishes zero work.
pub const COMPILER_OBSERVATION_VERSION: u32 = 1;
pub const SHARED_DEPENDENCY_POLICY_VERSION: u32 = 1;

/// A diagnostic description of the scheduler's actual sharing policy.
/// This never grants cache, compiler, proof or resource authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "kebab-case", deny_unknown_fields)]
pub enum SharedDependencyDecision {
    // An empty struct (rather than a unit variant) enforces unknown-field
    // rejection in serde's internally tagged representation.
    Eligible {},
    Excluded { reason: SharedDependencyExclusion },
    DependencyBlocked { dependencies: Vec<UnitIndex> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SharedDependencyExclusion {
    SourceNotShareable,
    RequestedPackage,
    NonLibrary,
    ArtifactDependency,
    ProceduralMacro,
    BuildScriptPackage,
    UnsupportedMode,
    UnsupportedCrateType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExecutionUnitOutcome {
    Succeeded,
    Failed,
    ToleratedFailure,
    Cancelled,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExecutionGraphOutcome {
    Succeeded,
    Failed,
    Cancelled,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum InputWorkPhase {
    ExecutionWindow,
    Freshness,
    Publication,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum InputWorkOutcome {
    Captured,
    Uncacheable,
}

pub use trust_fs_observation::InputWork;

/// A log message.
///
/// Each variant represents a different type of event.
#[derive(Serialize, Deserialize, Clone)]
#[serde(tag = "reason", rename_all = "kebab-case")]
pub enum LogMessage {
    /// Trust: an unverified native test action depends on the full artifact
    /// completion of every listed compilation unit. This is a separate node
    /// inventory, never part of the compilation-unit execution denominator.
    TestActionRegistered {
        index: u64,
        harness: UnitIndex,
        prerequisites: Vec<UnitIndex>,
    },
    /// Trust: queue accounting uses the preceding UnitRegistered denominator.
    /// This scope covers compilation jobs, including fresh/no-op and build
    /// script jobs; it does not declare a unified verification/test graph.
    ExecutionEnabled {
        version: u32,
    },
    SharedDependencyPolicy {
        version: u32,
        enabled: bool,
    },
    SharedDependencyDecision {
        index: UnitIndex,
        decision: SharedDependencyDecision,
    },
    CompilerObservationsEnabled {
        version: u32,
        rusage_requested: bool,
    },
    /// Trust: emitted when the queue actually takes ownership of dispatch.
    /// `fresh` is the pre-work classification, not a count of compiler runs:
    /// a dirty job can become fresh after waiting for another producer.
    UnitScheduled {
        index: UnitIndex,
        elapsed: f64,
        fresh: bool,
    },
    /// Trust: full job completion, not an intermediate metadata-ready event.
    UnitOutcome {
        index: UnitIndex,
        elapsed: f64,
        outcome: ExecutionUnitOutcome,
    },
    /// Trust: emitted only after scoped workers join. Counts describe observed
    /// dispatch/terminal events; not_executed includes filtered registered units.
    /// Missing completions remain visible, never synthesized from queue drop.
    ExecutionGraphFinished {
        elapsed: f64,
        outcome: ExecutionGraphOutcome,
        scheduled: u64,
        completed: u64,
        not_executed: u64,
    },
    /// Trust: the file logger supports scoped build-script input accounting.
    InputWorkEnabled {
        version: u32,
    },
    /// Trust: capture IDs are allocated within this build, before scanning.
    InputWorkStarted {
        capture: u64,
        index: UnitIndex,
        phase: InputWorkPhase,
    },
    /// Trust: outcome includes the subsequent execution-window coverage check.
    InputWorkFinished {
        capture: u64,
        index: UnitIndex,
        phase: InputWorkPhase,
        outcome: InputWorkOutcome,
        work: InputWork,
    },
    /// Trust: the coordinator drained the jobs and accounts for every allocated
    /// capture. An aborted queue must not synthesize this acknowledgement.
    InputWorkFinalized {
        captures: u64,
    },
    /// Trust: emitted after all queued events; this is not build-success evidence.
    InputWorkClosed {
        version: u32,
        started: u64,
        finished: u64,
    },
    /// Emitted when a build starts.
    BuildStarted {
        /// The command-line arguments Cargo was invoked with.
        command: Vec<String>,
        /// Current working directory.
        cwd: PathBuf,
        /// Host tuple.
        host: String,
        /// Number of parallel jobs.
        jobs: u32,
        /// Available parallelism of the compilation environment.
        num_cpus: Option<u64>,
        /// Build profile name (e.g., "dev", "release").
        profile: String,
        /// The rustc version (`1.23.4-beta.2`).
        rustc_version: String,
        /// The rustc verbose version information (the output of `rustc -vV`).
        rustc_version_verbose: String,
        /// Target directory for build artifacts.
        target_dir: PathBuf,
        /// Workspace root directory.
        workspace_root: PathBuf,
    },
    /// Emitted when resolving dependencies starts.
    ResolutionStarted {
        /// Seconds elapsed from build start.
        elapsed: f64,
    },
    /// Emitted when resolving dependencies finishes.
    ResolutionFinished {
        /// Seconds elapsed from build start.
        elapsed: f64,
    },
    /// Emitted when unit graph generation starts.
    UnitGraphStarted {
        /// Seconds elapsed from build start.
        elapsed: f64,
    },
    /// Emitted when unit graph generation finishes.
    UnitGraphFinished {
        /// Seconds elapsed from build start.
        elapsed: f64,
    },
    /// Emitted when a compilation unit is registered in the unit graph,
    /// right before [`LogMessage::UnitGraphFinished`] that Cargo finalizes
    /// the unit graph.
    UnitRegistered {
        /// Package ID specification.
        package_id: PackageIdSpec,
        /// Cargo target (lib, bin, example, etc.).
        target: Target,
        /// The compilation action this unit is for (check, build, test, etc.).
        mode: CompileMode,
        /// The target platform this unit builds for.
        ///
        /// It is either a [target tuple] the compiler accepts,
        /// or a file name with the `json` extension for a [custom target].
        ///
        /// [target tuple]: https://doc.rust-lang.org/nightly/rustc/platform-support.html
        /// [custom target]: https://doc.rust-lang.org/nightly/rustc/targets/custom.html
        platform: String,
        /// Unit index for compact reference in subsequent events.
        index: UnitIndex,
        /// Enabled features.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        features: Vec<String>,
        /// Whether this is requested to build by user directly,
        /// like via the `-p` flag or the default workspace members.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        requested: bool,
        /// Unit indices that this unit depends on.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        dependencies: Vec<UnitIndex>,
    },
    /// Emitted when a compilation unit starts.
    UnitStarted {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Seconds elapsed from build start.
        elapsed: f64,
    },
    /// Emitted when a section (e.g., rmeta, link) of the compilation unit finishes.
    UnitRmetaFinished {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Seconds elapsed from build start.
        elapsed: f64,
        /// Unit indices that were unblocked by this rmeta completion.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        unblocked: Vec<UnitIndex>,
    },
    /// Emitted when a section (e.g., rmeta, link) of the compilation unit starts.
    ///
    /// Requires `-Zsection-timings` to be enabled.
    UnitSectionStarted {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Seconds elapsed from build start.
        elapsed: f64,
        /// Section name from rustc's `-Zjson=timings` (e.g., "codegen", "link").
        section: String,
    },
    /// Emitted when a section (e.g., rmeta, link) of the compilation unit finishes.
    ///
    /// Requires `-Zsection-timings` to be enabled.
    UnitSectionFinished {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Seconds elapsed from build start.
        elapsed: f64,
        /// Section name from rustc's `-Zjson=timings` (e.g., "codegen", "link").
        section: String,
    },
    /// Emitted when the peak memory usage of a compilation unit is captured.
    UnitPeakMemory {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Peak resident set size of the unit's process, in bytes.
        bytes: u64,
    },
    /// CPU from the unit owner's kernel wait: child plus descendants it waited for.
    /// Absence is unavailable accounting; a recorded zero is an actual zero.
    UnitCpuTimes {
        index: UnitIndex,
        user_ns: u64,
        system_ns: u64,
    },
    /// Emitted when a compilation unit finishes.
    UnitFinished {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Seconds elapsed from build start.
        elapsed: f64,
        /// Unit indices that were unblocked by this completion.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        unblocked: Vec<UnitIndex>,
    },
    /// Emitted when rebuild fingerprint information is determined for a unit.
    UnitFingerprint {
        /// Unit index from the associated unit-registered event.
        index: UnitIndex,
        /// Status of the rebuild detection fingerprint of this unit
        status: FingerprintStatus,
        /// Reason why the unit is dirty and needs rebuilding.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cause: Option<DirtyReason>,
        /// Trust: the one ordinary comparison repeated after taking the build
        /// lock. Missing in legacy logs and initial preparation observations.
        #[serde(default, skip_serializing_if = "is_false")]
        recheck: bool,
    },
}

fn is_false(value: &bool) -> bool {
    !value
}

#[cfg(test)]
mod fingerprint_recheck_tests {
    use super::{FingerprintStatus, LogMessage};
    use crate::compiler::UnitIndex;
    use crate::compiler::fingerprint::DirtyReason;

    #[test]
    fn initial_fingerprint_preserves_legacy_shape_and_default() {
        let legacy = serde_json::json!({
            "reason": "unit-fingerprint", "index": 7, "status": "fresh",
        });
        let message: LogMessage = serde_json::from_value(legacy.clone()).unwrap();
        assert!(matches!(
            &message,
            LogMessage::UnitFingerprint {
                recheck: false,
                cause: None,
                ..
            }
        ));
        assert_eq!(serde_json::to_value(message).unwrap(), legacy);
    }

    #[test]
    fn post_lock_fingerprint_retains_phase_and_typed_cause() {
        let message = LogMessage::UnitFingerprint {
            index: UnitIndex(7),
            status: FingerprintStatus::Dirty,
            cause: Some(DirtyReason::Forced),
            recheck: true,
        };
        let value = serde_json::to_value(message).unwrap();
        assert_eq!(
            value,
            serde_json::json!({
                "reason": "unit-fingerprint", "index": 7, "status": "dirty",
                "cause": {"dirty_reason": "forced"}, "recheck": true,
            })
        );
        let decoded: LogMessage = serde_json::from_value(value).unwrap();
        assert!(matches!(
            decoded,
            LogMessage::UnitFingerprint {
                recheck: true,
                cause: Some(DirtyReason::Forced),
                ..
            }
        ));
    }
}

/// Cargo target information.
#[derive(Serialize, Deserialize, Clone)]
pub struct Target {
    /// Target name.
    pub name: String,
    /// Target kind (lib, bin, test, bench, example, build-script).
    pub kind: Cow<'static, str>,
}

/// Status of the rebuild detection fingerprint.
#[derive(Serialize, Deserialize, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum FingerprintStatus {
    /// There is no previous fingerprints for this unit.
    /// Might be a brand-new build.
    New,
    /// The current fingerprint doesn't match the previous fingerprints.
    /// Rebuild needed.
    Dirty,
    /// The current fingerprint matches the previous fingerprints.
    /// No rebuild needed.
    Fresh,
}

impl From<&crate::workspace::Target> for Target {
    fn from(target: &crate::workspace::Target) -> Self {
        use crate::workspace::TargetKind;
        Self {
            name: target.name().to_string(),
            kind: match target.kind() {
                TargetKind::Lib(..) => "lib",
                TargetKind::Bin => "bin",
                TargetKind::Test => "test",
                TargetKind::Bench => "bench",
                TargetKind::ExampleLib(..) | TargetKind::ExampleBin => "example",
                TargetKind::CustomBuild => "build-script",
            }
            .into(),
        }
    }
}

impl LogMessage {
    /// Serializes this message as a JSON log line directly to the writer.
    pub fn write_json_log<W: Write>(&self, writer: &mut W, run_id: &str) -> std::io::Result<()> {
        #[derive(Serialize)]
        struct LogEntry<'a> {
            run_id: &'a str,
            timestamp: Timestamp,
            #[serde(flatten)]
            msg: &'a LogMessage,
        }

        let entry = LogEntry {
            run_id,
            timestamp: Timestamp::now(),
            msg: self,
        };

        serde_json::to_writer(&mut *writer, &entry)?;
        writer.write_all(b"\n")?;
        Ok(())
    }
}
