//! Compiler-owned tool readsets checked against the current Rustc parent.
//!
//! The saved recipe supplies the final linker lookup; Targo does not implement
//! a second linker resolver. Parent matching assumes unchanged compiler and
//! semantic command inputs, checked by the ordinary fingerprint/receipt gates.
//! These are invalidation facts, not proof or execution attestation.

use std::fs::{self, OpenOptions};
use std::io::Read as _;
use std::path::PathBuf;
use std::sync::Mutex;

use cargo_util::ProcessBuilder;
use trust_fs_observation::tool_lookup::{CurrentToolInputs, Profile, ToolInputs};

use super::configured_linker;
use super::dep_info::{EncodedDepInfo, ToolInputsState};
use super::output_integrity::ToolInputExpectation;
use crate::CargoResult;
use crate::compiler::{BuildRunner, CompileMode, CrateType, Unit};
use crate::context::FingerprintMethod;

// The encoded source readset also contains ordinary file/environment rows.
// Exceeding this cache-read budget refuses reuse, not valid compilation.
const MAX_ENCODED_BYTES: u64 = 64 * 1024 * 1024;

#[derive(Default)]
pub(super) enum Plan {
    NotRequired,
    Required {
        path: PathBuf,
        parent: Option<Parent>,
        profile: Profile,
        cache: Mutex<Option<CachedInputs>>,
    },
    #[default]
    Unavailable,
}

pub(super) struct Parent {
    cwd: PathBuf,
    path: Option<std::ffi::OsString>,
    profile: Profile,
}

pub(super) struct CachedInputs {
    inputs: ToolInputs,
    current: CurrentToolInputs,
}

impl CachedInputs {
    fn observe(inputs: ToolInputs, parent: &Parent) -> CargoResult<Self> {
        let current = observe_current(&inputs, parent)?;
        Ok(Self { inputs, current })
    }

    fn binding(&mut self, parent: &Parent) -> CargoResult<[u8; 32]> {
        if !self.current.is_current()? {
            // Reobserve against the SAME decoded facts. Replacing the recipe
            // here would bypass its earlier match against the output receipt.
            self.current = observe_current(&self.inputs, parent)?;
        }
        Ok(self.current.binding())
    }
}

impl Parent {
    fn capture(command: &ProcessBuilder, profile: Profile) -> CargoResult<Self> {
        anyhow::ensure!(
            !command.has_process_executor() && !command.has_action_sandbox(),
            "tool-input parent uses an unsupported execution owner"
        );
        #[cfg(unix)]
        {
            let cwd = command
                .get_cwd()
                .ok_or_else(|| anyhow::anyhow!("tool-input parent has no explicit cwd"))?
                .to_owned();
            anyhow::ensure!(cwd.is_absolute(), "tool-input parent cwd is not absolute");
            let environment = command.get_effective_envs()?;
            Ok(Self {
                cwd,
                path: environment.get(std::ffi::OsStr::new("PATH")).cloned(),
                profile,
            })
        }
        #[cfg(not(unix))]
        {
            let _ = profile;
            anyhow::bail!("tool-input parent is unsupported on this host")
        }
    }
}

pub(in crate::compiler) struct Execution {
    configured: configured_linker::Execution,
    parent: Option<Parent>,
}

impl Plan {
    pub(super) fn invalidate(&self, raw_dep_info: &std::path::Path) -> CargoResult<()> {
        if let Self::Required { path, cache, .. } = self {
            *cache.lock().unwrap() = None;
            // A successful compiler that omitted its terminal write cannot
            // reuse yesterday's raw or translated facts for a new output seal.
            for path in [raw_dep_info, path.as_path()] {
                match fs::remove_file(path) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error.into()),
                }
            }
        }
        Ok(())
    }

    pub(super) fn select(
        runner: &BuildRunner<'_, '_>,
        unit: &Unit,
        configured: &configured_linker::Selection,
        has_receipt: bool,
    ) -> CargoResult<Self> {
        if !has_receipt
            || !crate::is_targo_invocation()
            || runner.bcx.source_fingerprint != FingerprintMethod::Content
        {
            return Ok(Self::NotRequired);
        }
        // This first profile adds facts to native, explicitly unverified
        // compilation. It cannot authorize a different verification policy.
        if crate::compiler::verified_targo_protocol_active() {
            return Ok(Self::NotRequired);
        }
        let supported = runner
            .bcx
            .rustc()
            .supports_tool_input_depinfo(runner.bcx.gctx)?;
        if !supported {
            // Older compilers retain known no-link and explicit-linker routes.
            // Unknown default native tools have no fallback cache authority.
            let crate_types = unit.target.rustc_crate_types();
            let no_link = unit.mode.is_check()
                || (unit.mode == CompileMode::Build
                    && !crate_types.is_empty()
                    && crate_types
                        .iter()
                        .all(|kind| matches!(kind, CrateType::Lib | CrateType::Rlib)));
            return Ok(if no_link || configured.has_configured_selection() {
                Self::NotRequired
            } else {
                Self::Unavailable
            });
        }
        let profile = match crate::compiler::validate_tool_input_profile(runner, unit) {
            Ok(profile) => profile,
            Err(_) => return Ok(Self::Unavailable),
        };
        let path = runner.files().fingerprint_file_path(unit, "dep-");
        let parent = crate::compiler::tool_input_parent_command(runner, unit)
            .and_then(|command| Parent::capture(&command, profile))
            .ok();
        Ok(Self::Required {
            path,
            parent,
            profile,
            cache: Mutex::new(None),
        })
    }

    pub(super) fn expectation(&self) -> ToolInputExpectation {
        match self {
            Self::NotRequired => ToolInputExpectation::NotRequired,
            Self::Required {
                path,
                parent: Some(parent),
                cache,
                ..
            } => {
                let result = (|| -> CargoResult<[u8; 32]> {
                    let mut cached = cache.lock().unwrap();
                    if cached.is_none() {
                        *cached = Some(CachedInputs::observe(read_inputs(path)?, parent)?);
                    }
                    cached.as_mut().unwrap().binding(parent)
                })();
                result.map_or(
                    ToolInputExpectation::Unavailable,
                    ToolInputExpectation::Observed,
                )
            }
            Self::Required { parent: None, .. } | Self::Unavailable => {
                ToolInputExpectation::Unavailable
            }
        }
    }

    pub(super) fn begin(
        &self,
        configured: &configured_linker::Selection,
        command: &ProcessBuilder,
    ) -> Execution {
        let requested = command.get_args().any(|arg| arg == "-Ztrust-tool-inputs");
        Execution {
            configured: configured.begin(command),
            parent: match self {
                Self::Required { profile, .. } if requested => {
                    Parent::capture(command, *profile).ok()
                }
                _ => None,
            },
        }
    }

    pub(super) fn complete(
        &self,
        configured: &configured_linker::Selection,
        execution: Execution,
    ) -> ToolInputExpectation {
        if !configured.complete(execution.configured) {
            return ToolInputExpectation::Unavailable;
        }
        match self {
            Self::NotRequired => ToolInputExpectation::NotRequired,
            // Use the actual final dirty command's parent, not a missing/stale
            // planning recipe. First cold builds can publish newly made facts.
            Self::Required { path, .. } => execution
                .parent
                .as_ref()
                .map_or(ToolInputExpectation::Unavailable, |parent| {
                    current_binding(path, parent)
                }),
            Self::Unavailable => ToolInputExpectation::Unavailable,
        }
    }
}

fn current_binding(path: &std::path::Path, parent: &Parent) -> ToolInputExpectation {
    let observed = (|| -> CargoResult<[u8; 32]> {
        let inputs = read_inputs(path)?;
        Ok(observe_current(&inputs, parent)?.binding())
    })();
    observed.map_or(
        ToolInputExpectation::Unavailable,
        ToolInputExpectation::Observed,
    )
}

fn read_inputs(path: &std::path::Path) -> CargoResult<ToolInputs> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = options.open(path)?;
    let metadata = file.metadata()?;
    anyhow::ensure!(
        metadata.is_file() && metadata.len() <= MAX_ENCODED_BYTES,
        "invalid readset file"
    );
    let mut bytes = Vec::new();
    file.take(MAX_ENCODED_BYTES + 1).read_to_end(&mut bytes)?;
    anyhow::ensure!(bytes.len() as u64 <= MAX_ENCODED_BYTES, "readset grew");
    let encoded = EncodedDepInfo::parse(&bytes)?;
    let ToolInputsState::Observed(inputs) = encoded.tool_inputs else {
        anyhow::bail!("terminal compiler tool-input facts are unavailable");
    };
    Ok(inputs)
}

fn observe_current(inputs: &ToolInputs, parent: &Parent) -> CargoResult<CurrentToolInputs> {
    for record in inputs.records() {
        let context = record.context();
        anyhow::ensure!(
            context.matches_parent(&parent.cwd, parent.path.as_deref(), parent.profile),
            "compiler tool recipe has a different parent"
        );
    }
    inputs.check_current(
        &inputs
            .records()
            .iter()
            .map(|record| record.context().clone())
            .collect::<Vec<_>>(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parent(root: &std::path::Path) -> Parent {
        Parent {
            cwd: root.to_owned(),
            path: Some("/usr/bin:/bin".into()),
            profile: Profile::LocalUnixNativeV1,
        }
    }

    fn write_terminal(path: &std::path::Path) {
        let encoded = EncodedDepInfo {
            tool_inputs: ToolInputsState::Observed(ToolInputs::from_records(Vec::new()).unwrap()),
            ..EncodedDepInfo::default()
        };
        fs::write(path, encoded.serialize().unwrap()).unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn graph_fingerprint(root: &std::path::Path, name: &str) -> super::super::Fingerprint {
        use super::super::{Fingerprint, FsStatus, output_integrity};
        use crate::compiler::output_observation::Emit;

        let artifact = root.join(format!("{name}.rmeta"));
        fs::write(&artifact, format!("{name} artifact A")).unwrap();
        let mut fingerprint = Fingerprint::new();
        fingerprint.rustc = 1;
        fingerprint.fs_status = FsStatus::UpToDate {
            mtimes: Default::default(),
        };
        fingerprint.outputs = vec![artifact.clone()];
        fingerprint.compiler_outputs = vec![(artifact, Emit::Metadata)];
        fingerprint.output_policy = output_integrity::OutputPolicy::Standard;
        fingerprint.compiler_observation = output_integrity::CompilerObservation::selected(
            1,
            Some([7; 32]),
            true,
            CompileMode::Build,
            false,
        );
        fingerprint.output_receipt = Some(root.join(format!("{name}-receipt.json")));
        fingerprint
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn publish_graph_receipt(fingerprint: &super::super::Fingerprint, tools: ToolInputExpectation) {
        use super::super::output_integrity;
        use crate::compiler::output_observation::Observer;

        // These are real DATA artifacts/receipts for a simulated previously
        // validated graph. Report coverage is not compiler execution or proof.
        let receipt = fingerprint.output_receipt.as_ref().unwrap();
        let mut observer = Observer::new(
            fingerprint.compiler_outputs.clone(),
            receipt.parent().unwrap().into(),
        );
        for (artifact, _) in &fingerprint.compiler_outputs {
            observer.observe(
                &serde_json::json!({
                    "$message_type": "artifact", "emit": "metadata", "artifact": artifact,
                })
                .to_string(),
            );
        }
        output_integrity::publish(
            receipt,
            fingerprint.hash_u64(),
            &fingerprint.outputs,
            fingerprint.compiler_observation.as_ref(),
            fingerprint.output_policy,
            &fingerprint.compiler_outputs,
            Some(output_integrity::Completion::new(observer.finish().unwrap(), tools).unwrap()),
        )
        .unwrap();
        output_integrity::verify(
            receipt,
            fingerprint.hash_u64(),
            &fingerprint.outputs,
            fingerprint.compiler_observation.as_ref(),
            fingerprint.output_policy,
            &fingerprint.compiler_outputs,
            tools,
        )
        .unwrap();
    }

    #[test]
    fn required_missing_or_unavailable_facts_are_not_no_link_facts() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("dep-info");
        let plan = Plan::Required {
            path: path.clone(),
            parent: Some(parent(root.path())),
            profile: Profile::LocalUnixNativeV1,
            cache: Mutex::new(None),
        };
        assert_eq!(plan.expectation(), ToolInputExpectation::Unavailable);
        for tool_inputs in [ToolInputsState::Missing, ToolInputsState::Unavailable] {
            fs::write(
                &path,
                EncodedDepInfo {
                    tool_inputs,
                    ..EncodedDepInfo::default()
                }
                .serialize()
                .unwrap(),
            )
            .unwrap();
            assert_eq!(plan.expectation(), ToolInputExpectation::Unavailable);
        }
        write_terminal(&path);
        assert!(matches!(
            plan.expectation(),
            ToolInputExpectation::Observed(_)
        ));
        assert_eq!(
            Plan::default().expectation(),
            ToolInputExpectation::Unavailable
        );
        assert_eq!(
            Plan::NotRequired.expectation(),
            ToolInputExpectation::NotRequired
        );
    }

    #[test]
    fn cold_completion_cannot_reuse_yesterdays_terminal_record() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("encoded");
        let raw = root.path().join("compiler.d");
        write_terminal(&path);
        fs::write(&raw, b"old compiler dep-info\n").unwrap();
        let plan = Plan::Required {
            path: path.clone(),
            parent: None,
            profile: Profile::LocalUnixNativeV1,
            cache: Mutex::new(None),
        };
        // A cold/missing parent recipe does not prevent newly produced facts
        // from publishing, but neither old file may supply those facts.
        assert_eq!(plan.expectation(), ToolInputExpectation::Unavailable);
        plan.invalidate(&raw).unwrap();
        assert!(!path.exists());
        assert!(!raw.exists());
        let configured = configured_linker::Selection::default();
        let execution = || Execution {
            // This command is DATA only; the test claims no compiler execution
            // or output seal. The configured-selector check inspects only argv.
            configured: configured.begin(&ProcessBuilder::new("unexecuted-command-data")),
            parent: Some(parent(root.path())),
        };
        assert_eq!(
            plan.complete(&configured, execution()),
            ToolInputExpectation::Unavailable
        );
        write_terminal(&path);
        assert!(matches!(
            plan.complete(&configured, execution()),
            ToolInputExpectation::Observed(_)
        ));
        assert_eq!(plan.expectation(), ToolInputExpectation::Unavailable);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn identical_parent_path_and_cwd_cannot_hide_a_native_runtime_change() {
        use trust_fs_observation::tool_lookup::Context;
        super::super::build_script_inputs::settled(|root| {
            let candidate = root.path().join("missing-tool");
            let context = Context::new(
                candidate.as_os_str(),
                root.path(),
                Some(std::ffi::OsStr::new("/usr/bin:/bin")),
                Some(std::ffi::OsStr::new("/usr/bin:/bin")),
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let inputs =
                ToolInputs::from_records(vec![context.begin().unwrap().finish().unwrap()]).unwrap();
            let encoded = root.path().join("encoded");
            fs::write(
                &encoded,
                EncodedDepInfo {
                    tool_inputs: ToolInputsState::Observed(inputs),
                    ..EncodedDepInfo::default()
                }
                .serialize()
                .unwrap(),
            )
            .unwrap();
            let mut current = parent(root.path());
            assert!(matches!(
                current_binding(&encoded, &current),
                ToolInputExpectation::Observed(_)
            ));
            current.profile = Profile::LocalUnixNativeResourceV2;
            assert_eq!(
                current_binding(&encoded, &current),
                ToolInputExpectation::Unavailable
            );
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn parent_freshness_rechecks_memoized_child_tool_facts() {
        use super::super::{DepFingerprint, Fingerprint, FingerprintComparison, FsStatus};
        use std::sync::Arc;
        use trust_fs_observation::tool_lookup::Context;

        super::super::build_script_inputs::settled(|root| {
            let candidate = root.path().join("absent-tool");
            // An absence is an actual filesystem fact, not a fake compiler role.
            // The test simulates already validated outputs and graph planning;
            // neither this record nor the simulated fs_status grants a live seal.
            let context = Context::new(
                candidate.as_os_str(),
                root.path(),
                Some(std::ffi::OsStr::new("/usr/bin:/bin")),
                Some(std::ffi::OsStr::new("/usr/bin:/bin")),
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let inputs =
                ToolInputs::from_records(vec![context.begin().unwrap().finish().unwrap()]).unwrap();
            let binding = inputs.binding().unwrap();
            let encoded_path = root.path().join("encoded");
            fs::write(
                &encoded_path,
                EncodedDepInfo {
                    tool_inputs: ToolInputsState::Observed(inputs),
                    ..EncodedDepInfo::default()
                }
                .serialize()
                .unwrap(),
            )
            .unwrap();
            let mut child = graph_fingerprint(root.path(), "child");
            child.tool_inputs = Plan::Required {
                path: encoded_path,
                parent: Some(parent(root.path())),
                profile: Profile::LocalUnixNativeV1,
                cache: Mutex::new(None),
            };
            publish_graph_receipt(&child, ToolInputExpectation::Observed(binding));
            let mut parent_fp = Fingerprint::new();
            parent_fp.rustc = 1;
            parent_fp.fs_status = FsStatus::UpToDate {
                mtimes: Default::default(),
            };
            parent_fp.deps.push(DepFingerprint {
                pkg_id: 1,
                name: "child".into(),
                public: false,
                only_requires_rmeta: false,
                fingerprint: Arc::new(child),
            });
            let key = parent_fp.hash_u64();
            let loc = root.path().join("fingerprint");
            fs::write(&loc, crate::util::to_hex(key)).unwrap();
            assert!(matches!(
                super::super::_compare_old_fingerprint(&loc, &parent_fp).unwrap(),
                FingerprintComparison::Fresh
            ));
            fs::create_dir(&candidate).unwrap();
            assert!(parent_fp.fs_status.up_to_date());
            assert!(parent_fp.deps[0].fingerprint.fs_status.up_to_date());
            assert_eq!(parent_fp.hash_u64(), key);
            assert!(matches!(
                super::super::_compare_old_fingerprint(&loc, &parent_fp).unwrap(),
                FingerprintComparison::Dirty {
                    reason: super::super::DirtyReason::ContentFingerprintUnavailable,
                }
            ));
        });
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn parent_rechecks_child_receipt_after_tool_facts_return_to_planned_state() {
        use super::super::{DepFingerprint, FingerprintComparison, output_integrity};
        use std::os::unix::fs::PermissionsExt as _;
        use std::sync::Arc;
        use trust_fs_observation::tool_lookup::Context;

        super::super::build_script_inputs::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let tool = crate::compiler::native_input_fixture::materialize(&root.join("tool-image"));
            // The actual system-native image is an observed DATA input only;
            // this test never executes it or claims child compiler execution.
            fs::set_permissions(&tool, fs::Permissions::from_mode(0o700)).unwrap();
            let context = Context::new(
                tool.as_os_str(),
                &root,
                None,
                Some(std::ffi::OsStr::new("/usr/bin:/bin")),
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let inputs_a =
                ToolInputs::from_records(vec![context.begin().unwrap().finish().unwrap()]).unwrap();
            let binding_a = inputs_a.binding().unwrap();
            let encoded = root.join("encoded-child");
            fs::write(
                &encoded,
                EncodedDepInfo {
                    tool_inputs: ToolInputsState::Observed(inputs_a),
                    ..EncodedDepInfo::default()
                }
                .serialize()
                .unwrap(),
            )
            .unwrap();
            let mut child = graph_fingerprint(&root, "child");
            child.tool_inputs = Plan::Required {
                path: encoded.clone(),
                parent: Some(parent(&root)),
                profile: Profile::LocalUnixNativeV1,
                cache: Mutex::new(None),
            };
            publish_graph_receipt(&child, ToolInputExpectation::Observed(binding_a));
            let mut parent_fp = graph_fingerprint(&root, "parent");
            parent_fp.tool_inputs = Plan::NotRequired;
            parent_fp.deps.push(DepFingerprint {
                pkg_id: 1,
                name: "child".into(),
                public: false,
                only_requires_rmeta: false,
                fingerprint: Arc::new(child),
            });
            publish_graph_receipt(&parent_fp, ToolInputExpectation::NotRequired);
            let key = parent_fp.hash_u64();
            let loc = root.join("fingerprint");
            fs::write(&loc, crate::util::to_hex(key)).unwrap();
            assert!(matches!(
                super::super::_compare_old_fingerprint(&loc, &parent_fp).unwrap(),
                FingerprintComparison::Fresh
            ));

            // Model another producer's real artifact/encoded-facts/receipt
            // replacement under B while this graph retains its planned A.
            fs::set_permissions(&tool, fs::Permissions::from_mode(0o755)).unwrap();
            let inputs_b =
                ToolInputs::from_records(vec![context.begin().unwrap().finish().unwrap()]).unwrap();
            let binding_b = inputs_b.binding().unwrap();
            assert_ne!(binding_a, binding_b);
            fs::write(
                &encoded,
                EncodedDepInfo {
                    tool_inputs: ToolInputsState::Observed(inputs_b),
                    ..EncodedDepInfo::default()
                }
                .serialize()
                .unwrap(),
            )
            .unwrap();
            let child = &parent_fp.deps[0].fingerprint;
            fs::write(&child.outputs[0], b"replacement child artifact B").unwrap();
            publish_graph_receipt(child, ToolInputExpectation::Observed(binding_b));
            fs::set_permissions(&tool, fs::Permissions::from_mode(0o700)).unwrap();
            assert_eq!(
                child.tool_inputs.expectation(),
                ToolInputExpectation::Observed(binding_a)
            );
            assert_eq!(
                fs::read(&child.outputs[0]).unwrap(),
                b"replacement child artifact B"
            );
            assert!(
                output_integrity::verify_tool_inputs(
                    child.output_receipt.as_ref().unwrap(),
                    child.hash_u64(),
                    ToolInputExpectation::Observed(binding_a),
                )
                .is_err()
            );
            assert!(parent_fp.fs_status.up_to_date());
            assert!(child.fs_status.up_to_date());
            assert_eq!(parent_fp.hash_u64(), key);
            assert!(matches!(
                super::super::_compare_old_fingerprint(&loc, &parent_fp).unwrap(),
                FingerprintComparison::Dirty {
                    reason: super::super::DirtyReason::ContentFingerprintUnavailable,
                }
            ));
        });
    }
}
