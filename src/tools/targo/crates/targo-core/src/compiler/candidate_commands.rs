//! Independent expected compiler command DATA, prepared by the original parent.
//! No report or path can construct the native frontend/CPU/source/output owners.
use super::build_runner::{CandidateOutput, CompilationFiles};
use super::layout::LayoutPaths;
use super::rustc_command_context::RustcCommandContext;
use super::{BuildContext, Compilation, Unit, exact_unit};
use crate::resource_v3::workload::bank::broker::RegisteredArtifact;
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use cargo_util::{EnvironmentInputs, Jobserver, ProcessBuilder};
use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;
use trust_resource_controller::CommandSpec;
use trust_resource_controller::client::ContainedProducedMember;

/// Captured only through the SAME actual native prepared member. The caller
/// continues retaining that member through GO/retirement; this is planning
/// input custody, not a successful operation or a replacement member owner.
pub(crate) struct Preparation {
    frontend: Arc<RegisteredArtifact>,
    environment: EnvironmentInputs,
    // Equality DATA from the exact native Prepared, including member attempt
    // and kernel identity. Only observing the live original member sets it.
    member_preparation: [u8; 32],
    member_attempt: [u8; 16],
    deadline: Instant,
}
impl Preparation {
    pub(crate) fn observe(
        member: &mut ContainedProducedMember,
        frontend: Arc<RegisteredArtifact>,
        deadline: Instant,
    ) -> CargoResult<Option<Arc<Self>>> {
        frontend.validate(deadline)?;
        let Some(prepared) = member.coordinator_prepared(deadline)? else {
            return Ok(None);
        };
        ensure!(
            prepared.produced.key == frontend.registered().registration().key
                && prepared.command.program
                    == frontend.original().image().program().as_os_str().as_bytes(),
            "candidate preparation differs from original registered frontend"
        );
        let member_preparation = preparation_fingerprint(&prepared)?;
        let member_attempt = prepared.produced.member_attempt;
        let environment = EnvironmentInputs::from_variables(
            prepared
                .command
                .environment
                .into_iter()
                .map(|(name, value)| (OsString::from_vec(name), OsString::from_vec(value))),
        )?;
        let preparation = Arc::new(Self {
            frontend,
            environment,
            member_preparation,
            member_attempt,
            deadline,
        });
        preparation.validate()?;
        Ok(Some(preparation))
    }
    pub(crate) fn environment(&self) -> &EnvironmentInputs {
        &self.environment
    }
    pub(crate) fn require_member(
        &self,
        member: &mut ContainedProducedMember,
        deadline: Instant,
    ) -> CargoResult<()> {
        self.validate()?;
        let actual = member
            .coordinator_prepared(deadline.min(self.deadline))?
            .context("original member has no actual coordinator preparation")?;
        ensure!(
            preparation_fingerprint(&actual)? == self.member_preparation,
            "command expectations belong to another native prepared member"
        );
        self.validate()
    }
    pub(super) fn frontend(&self) -> CargoResult<&Path> {
        self.validate()?;
        Ok(self.frontend.original().image().program())
    }
    pub(super) fn validate(&self) -> CargoResult<()> {
        ensure!(
            Instant::now() < self.deadline,
            "candidate preparation expired"
        );
        self.frontend.validate(self.deadline)
    }
    pub(super) fn require_context(&self, bcx: &BuildContext<'_, '_>) -> CargoResult<()> {
        self.require_environment(bcx.gctx)
    }
    pub(crate) fn require_environment(&self, gctx: &crate::util::GlobalContext) -> CargoResult<()> {
        self.validate()?;
        ensure!(
            gctx.env_os().collect::<std::collections::BTreeMap<_, _>>()
                == self
                    .environment
                    .iter()
                    .collect::<std::collections::BTreeMap<_, _>>(),
            "parent context differs from complete original prepared environment"
        );
        Ok(())
    }
}

pub(crate) struct ExpectedUnitCommand {
    pub unit_sha256: String,
    pub outputs: Arc<Vec<super::build_runner::OutputFile>>,
    command: CommandSpec,
    key: UnitKey,
    package_root: PathBuf,
    predecessors: Vec<ExpectedPredecessor>,
    private_outputs: Option<super::build_runner::UnitOutputNamespace>,
    program: Option<ExpectedProgram>,
}
/// Executable/runtime equality DATA from the SAME resolved root and shared
/// ordinary target-process prefix. This never grants materialization or GO.
pub(super) struct ExpectedProgram {
    path: PathBuf,
    runtime_roots: Vec<PathBuf>,
}
impl ExpectedProgram {
    pub(super) fn path(&self) -> &Path {
        &self.path
    }
    pub(super) fn runtime_roots(&self) -> &[PathBuf] {
        &self.runtime_roots
    }
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct UnitKey {
    unit_sha256: String,
    unit_id: String,
}
impl UnitKey {
    pub(super) fn retained_bytes(&self) -> Option<usize> {
        self.unit_sha256
            .capacity()
            .checked_add(self.unit_id.capacity())
    }
}
#[cfg(test)]
pub(super) fn test_unit_key(unit: &str) -> UnitKey {
    UnitKey {
        unit_sha256: unit.into(),
        unit_id: "equality-data".into(),
    }
}
pub(super) struct ExpectedPredecessor {
    pub key: UnitKey,
    pub outputs: Vec<usize>,
}
impl ExpectedUnitCommand {
    pub(super) fn program(&self) -> Option<&ExpectedProgram> {
        self.program.as_ref()
    }
    pub(crate) fn publication_selection(
        &self,
    ) -> CargoResult<trust_resource_controller::workload::host::coordinator::PublicationSelection>
    {
        let mut destinations = self
            .outputs
            .iter()
            .flat_map(|output| output.hardlink.iter().chain(output.export_path.iter()))
            .map(|path| path.as_os_str().as_bytes().to_vec())
            .collect::<Vec<_>>();
        destinations.sort();
        let selection =
            trust_resource_controller::workload::host::coordinator::PublicationSelection {
                unit_sha256: self.key.unit_sha256.clone(),
                unit_id: self.key.unit_id.clone(),
                destinations,
            };
        selection.validate()?;
        Ok(selection)
    }
    pub(crate) fn private_outputs(&self) -> CargoResult<&super::build_runner::UnitOutputNamespace> {
        self.private_outputs
            .as_ref()
            .context("expected native command has no private unit output namespace")
    }
    pub(super) fn key(&self) -> &UnitKey {
        &self.key
    }
    pub(super) fn package_root(&self) -> &Path {
        &self.package_root
    }
    pub(super) fn predecessors(&self) -> &[ExpectedPredecessor] {
        &self.predecessors
    }
    pub(crate) fn command(&self) -> &CommandSpec {
        &self.command
    }
}
pub(crate) struct ExpectedCommands {
    entries: Vec<ExpectedUnitCommand>,
    preparation: Arc<Preparation>,
    // SAME original scheduler remains alive through command comparison.
    _jobserver: Jobserver,
}
impl ExpectedCommands {
    pub(crate) fn require_publication(
        &self,
        selection: &trust_resource_controller::workload::host::coordinator::PublicationSelection,
    ) -> CargoResult<&ExpectedUnitCommand> {
        self.validate()?;
        selection.validate()?;
        let mut matched = None;
        for row in &self.entries {
            if row.publication_selection()? == *selection {
                ensure!(
                    matched.is_none(),
                    "publication selection is ambiguous in exact expected graph"
                );
                matched = Some(row);
            }
        }
        matched.context("publication selection differs from SAME exact expected unit/output row")
    }
    pub(super) fn validate(&self) -> CargoResult<()> {
        self.preparation.validate()
    }
    pub(super) fn entry(&self, key: &UnitKey) -> CargoResult<&ExpectedUnitCommand> {
        let mut found = self.entries.iter().filter(|entry| entry.key == *key);
        let entry = found
            .next()
            .context("dependency unit is outside current independent graph")?;
        ensure!(
            found.next().is_none(),
            "dependency unit has ambiguous current graph identity"
        );
        Ok(entry)
    }
    pub(super) fn member_binding(&self) -> [u8; 32] {
        self.preparation.member_preparation
    }
    pub(super) fn coordinator_attempt(&self) -> [u8; 16] {
        self.preparation.member_attempt
    }
    pub(crate) fn require_member(
        &self,
        member: &mut ContainedProducedMember,
        deadline: Instant,
    ) -> CargoResult<()> {
        self.preparation.require_member(member, deadline)
    }
    /// Borrow the SAME original scheduler used while preparing these rows.
    /// No capability string or caller-created pool reconstructs this owner.
    pub(crate) fn jobserver(&self) -> &Jobserver {
        &self._jobserver
    }
    /// Compare after the actual original GNU constructor has materialized the
    /// local command. No variable-name exemption or argument parser exists.
    pub(crate) fn require(&self, proposed: &CommandSpec) -> CargoResult<&ExpectedUnitCommand> {
        self.preparation.validate()?;
        let index = matching_command(&self.entries, proposed)?;
        Ok(&self.entries[index])
    }
    pub(crate) fn entries(&self) -> &[ExpectedUnitCommand] {
        &self.entries
    }
}

fn preparation_fingerprint(
    prepared: &trust_resource_controller::workload::host::coordinator::Prepared,
) -> CargoResult<[u8; 32]> {
    let mut digest = cargo_util::Sha256::new();
    digest.update(b"trust.original-coordinator-prepared.v1");
    digest.update(&prepared.encode()?);
    Ok(digest.finish())
}

fn matching_command(entries: &[ExpectedUnitCommand], proposed: &CommandSpec) -> CargoResult<usize> {
    let mut found = None;
    for (index, expected) in entries.iter().enumerate() {
        if expected.command == *proposed {
            ensure!(
                found.is_none(),
                "candidate command matches ambiguous resolved units"
            );
            found = Some(index);
        }
    }
    found.context("candidate command differs from independently prepared resolved unit")
}

pub(super) fn prepare<'a, 'gctx>(
    bcx: &'a BuildContext<'a, 'gctx>,
    compilation: &Compilation<'gctx>,
    files: &CompilationFiles<'a, 'gctx, LayoutPaths>,
    lto: &crate::util::data_structures::HashMap<Unit, super::lto::Lto>,
    graph: &exact_unit::Graph,
    outputs: &[CandidateOutput],
    preparation: Arc<Preparation>,
    jobserver: &Jobserver,
) -> CargoResult<ExpectedCommands> {
    preparation.require_context(bcx)?;
    ensure!(
        !super::verified_targo_protocol_active()
            && crate::is_targo_invocation()
            && crate::trust_no_verify_fast()
            && !bcx.action_sandbox
            && !bcx.gctx.cli_unstable().section_timings
            && bcx
                .gctx
                .get_env_os(super::TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION)
                .is_none(),
        "candidate command planning requires the closed unverified native profile"
    );
    let primary_packages = bcx.roots.iter().map(|unit| unit.pkg.package_id()).collect();
    let extern_selections = std::cell::RefCell::new(Vec::new());
    let context = RustcCommandContext {
        bcx,
        compilation,
        files: Some(files),
        lto,
        primary_packages: &primary_packages,
        extern_selections: Some(&extern_selections),
    };
    let mut entries = Vec::with_capacity(bcx.unit_graph.len());
    let mut remaining = 128 * 1024 * 1024usize;
    for unit in bcx.unit_graph.keys() {
        preflight_unit(unit)?;
        let profile_flags = unit
            .profile
            .rustflags
            .iter()
            .map(|flag| flag.as_str())
            .collect::<Vec<_>>();
        let unit_flags = unit
            .rustflags
            .iter()
            .map(|flag| flag.as_str())
            .collect::<Vec<_>>();
        ensure!(
            super::caller_supplied_external_crate(&unit_flags).is_none()
                && super::caller_supplied_external_crate(&profile_flags).is_none(),
            "independent dependency custody refuses caller-supplied extern overrides"
        );
        ensure!(
            !unit.target.is_test() && !unit.target.is_bench() && !unit.pkg.manifest().is_embedded(),
            "candidate command planning refuses temporary/script targets"
        );
        let mut process = super::prepare_native_rustc_command(&context, unit, jobserver)?;
        super::resource_runtime_v3::finalize_compiler_command(&mut process, jobserver);
        let command = capture_command(&process, &mut remaining)?;
        let unit_sha256 = graph.capture(unit)?.digest.clone();
        let selections = extern_selections.replace(Vec::new());
        let mut predecessors = Vec::new();
        for dep in &bcx.unit_graph[unit] {
            let dep_outputs = files.outputs(&dep.unit, bcx)?;
            let mut selected_outputs = Vec::new();
            for selected in selections
                .iter()
                .filter(|selected| selected.unit == dep.unit)
            {
                ensure!(
                    Arc::ptr_eq(&selected.outputs, &dep_outputs),
                    "extern output lost same file plan association"
                );
                ensure!(
                    selected.index < dep_outputs.len(),
                    "extern selection index outside actual OutputFiles"
                );
                selected_outputs.push(selected.index);
            }
            selected_outputs.sort_unstable();
            selected_outputs.dedup();
            predecessors.push(ExpectedPredecessor {
                key: UnitKey {
                    unit_sha256: graph.capture(&dep.unit)?.digest.clone(),
                    unit_id: files.metadata(&dep.unit).unit_id().to_string(),
                },
                outputs: selected_outputs,
            });
        }
        let mut selected = outputs.iter().filter(|row| {
            row.unit_sha256 == unit_sha256
                && row.metadata.unit_id() == files.metadata(unit).unit_id()
        });
        let output = selected
            .next()
            .context("independent expected command omitted output metadata")?;
        ensure!(
            selected.next().is_none(),
            "independent expected command has ambiguous output metadata"
        );
        ensure!(
            output.private.unit_sha256() == unit_sha256
                && output.private.unit_id() == files.metadata(unit).unit_id(),
            "native private output namespace differs from exact resolved unit"
        );
        let program =
            if output.is_root && unit.target.is_bin() && unit.mode == super::CompileMode::Build {
                ensure!(
                    compilation.target_runner(unit.kind).is_none(),
                    "published native binary cannot use a custom target runner"
                );
                let path = expected_executable(&output.outputs)?;
                let runtime_roots =
                    crate::ops::cargo_test::workload::NativeOutput::project_runtime_roots(
                        bcx.ws.target_dir().as_path_unlocked(),
                        preparation.frontend.original().image().sdk_root(),
                        &path,
                        compilation.target_runtime_search_paths(&unit.pkg, unit.kind),
                    )?;
                Some(ExpectedProgram {
                    path,
                    runtime_roots,
                })
            } else {
                None
            };
        entries.push(ExpectedUnitCommand {
            program,
            private_outputs: Some(output.private.clone()),
            key: UnitKey {
                unit_sha256: unit_sha256.clone(),
                unit_id: files.metadata(unit).unit_id().to_string(),
            },
            package_root: unit.pkg.root().to_owned(),
            predecessors,
            unit_sha256,
            outputs: output.outputs.clone(),
            command,
        });
    }
    entries.sort_by(|left, right| left.unit_sha256.cmp(&right.unit_sha256));
    preparation.validate()?;
    Ok(ExpectedCommands {
        entries,
        preparation,
        _jobserver: jobserver.clone(),
    })
}
fn expected_executable(outputs: &[super::build_runner::OutputFile]) -> CargoResult<PathBuf> {
    let mut normal = outputs
        .iter()
        .filter(|output| matches!(output.flavor, super::FileFlavor::Normal));
    let output = normal
        .next()
        .context("expected binary root has no actual Normal output")?;
    ensure!(
        normal.next().is_none(),
        "expected binary root has ambiguous Normal outputs"
    );
    let destination = output
        .hardlink
        .as_ref()
        .context("expected binary root has no canonical publication destination")?;
    ensure!(
        destination != &output.path,
        "expected binary canonical output aliases private producer path"
    );
    Ok(destination.clone())
}

fn preflight_unit(unit: &Unit) -> CargoResult<()> {
    // Bound borrowed values BEFORE check_cfg's joins or package metadata's
    // author join/command overlays allocate them. Ordinary builds retain their
    // established policy; only this closed independent planning profile caps.
    let features = unit.pkg.summary().features();
    let metadata = unit.pkg.manifest().metadata();
    ensure!(
        features.len() <= 4096 && metadata.authors.len() <= 4096,
        "candidate package command input population exceeds finite bound"
    );
    let mut remaining = 8 * 1024 * 1024usize;
    let mut charge = |value: &str| -> CargoResult<()> {
        remaining = remaining
            .checked_sub(
                value
                    .len()
                    .checked_add(32)
                    .context("candidate package command input size overflow")?,
            )
            .context("candidate package command inputs exceed finite byte bound")?;
        Ok(())
    };
    for feature in features.keys() {
        charge(feature)?;
    }
    for value in metadata.authors.iter().map(String::as_str).chain([
        metadata.description.as_deref().unwrap_or_default(),
        metadata.homepage.as_deref().unwrap_or_default(),
        metadata.repository.as_deref().unwrap_or_default(),
        metadata.license.as_deref().unwrap_or_default(),
        metadata.license_file.as_deref().unwrap_or_default(),
        metadata.readme.as_deref().unwrap_or_default(),
    ]) {
        charge(value)?;
    }
    for flag in unit
        .pkg
        .manifest()
        .lint_rustflags()
        .iter()
        .map(String::as_str)
        .chain(unit.profile.rustflags.iter().map(|flag| &**flag))
        .chain(unit.rustflags.iter().map(|flag| &**flag))
    {
        charge(flag)?;
    }
    Ok(())
}

pub(super) fn capture_command(
    process: &ProcessBuilder,
    remaining: &mut usize,
) -> CargoResult<CommandSpec> {
    let actual = process.build_command();
    let environment = process.get_effective_envs()?;
    let cwd = actual
        .get_current_dir()
        .context("expected native command has no package working directory")?;
    let mut charge = |bytes: &[u8]| -> CargoResult<()> {
        *remaining = remaining
            .checked_sub(
                bytes
                    .len()
                    .checked_add(32)
                    .context("expected command size overflow")?,
            )
            .context("independent expected commands exceed finite retained bound")?;
        Ok(())
    };
    charge(actual.get_program().as_bytes())?;
    charge(cwd.as_os_str().as_bytes())?;
    if let Some(arg0) = process.get_arg0() {
        charge(arg0.as_bytes())?;
    }
    for arg in actual.get_args() {
        charge(arg.as_bytes())?;
    }
    for (name, value) in &environment {
        charge(name.as_bytes())?;
        charge(value.as_bytes())?;
    }
    Ok(CommandSpec {
        program: actual.get_program().as_bytes().to_vec(),
        arg0: process.get_arg0().map(|arg| arg.as_bytes().to_vec()),
        args: actual
            .get_args()
            .map(|arg| arg.as_bytes().to_vec())
            .collect(),
        environment: environment
            .into_iter()
            .map(|(name, value)| (name.as_bytes().to_vec(), value.as_bytes().to_vec()))
            .collect(),
        cwd: cwd.as_os_str().as_bytes().to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Literal command observations only. No SDK/CPU/registered frontend or
    // Prepared owner is fabricated and these controls establish no admission.
    fn data_command() -> ProcessBuilder {
        let mut process = ProcessBuilder::new("/original-sdk/bin/trustc");
        process
            .cwd("/original-package")
            .args(&[
                "--crate-name",
                "subject",
                "--cfg",
                "feature=\"selected\"",
                "-Ctarget-feature=+crc",
                "--extern",
                "dependency=/original-output/libdependency.rlib",
                "--out-dir",
                "/original-output",
                "-Zunstable-options",
            ])
            .environment_snapshot(
                EnvironmentInputs::from_variables([
                    (
                        OsString::from("CARGO_MAKEFLAGS"),
                        OsString::from("--jobserver-auth=7,8"),
                    ),
                    (
                        OsString::from_vec(b"raw_\xff".to_vec()),
                        OsString::from_vec(b"value_\xfe".to_vec()),
                    ),
                    (
                        OsString::from("OBSERVED_BY_ENV_MACRO"),
                        OsString::from("42"),
                    ),
                ])
                .unwrap(),
            );
        process
    }
    fn entry(command: CommandSpec, unit: &str) -> ExpectedUnitCommand {
        ExpectedUnitCommand {
            program: None,
            key: UnitKey {
                unit_sha256: unit.into(),
                unit_id: "equality-data".into(),
            },
            package_root: PathBuf::from("/equality-data"),
            predecessors: Vec::new(),
            private_outputs: None,
            unit_sha256: unit.into(),
            outputs: Arc::new(Vec::new()),
            command,
        }
    }
    #[test]
    fn executable_projection_requires_one_normal_output_and_actual_canonical_publication() {
        use super::super::FileFlavor;
        use super::super::build_runner::OutputFile;
        let output = |path: &str, hardlink: Option<&str>, flavor| OutputFile {
            path: path.into(),
            hardlink: hardlink.map(Into::into),
            export_path: None,
            flavor,
        };
        let normal = output(
            "/outputs/private/native",
            Some("/outputs/debug/native"),
            FileFlavor::Normal,
        );
        let symbols = output(
            "/outputs/private/native.dSYM",
            Some("/outputs/debug/native.dSYM"),
            FileFlavor::DebugInfo,
        );
        assert_eq!(
            expected_executable(&[normal, symbols]).unwrap(),
            PathBuf::from("/outputs/debug/native")
        );
        assert!(expected_executable(&[]).is_err());
        assert!(
            expected_executable(&[output("/outputs/private/native", None, FileFlavor::Normal)])
                .is_err()
        );
        assert!(
            expected_executable(&[output(
                "/outputs/private/native",
                Some("/outputs/private/native"),
                FileFlavor::Normal
            )])
            .is_err()
        );
        assert!(
            expected_executable(&[
                output(
                    "/outputs/private/native",
                    Some("/outputs/debug/native"),
                    FileFlavor::Normal
                ),
                output(
                    "/outputs/private/other",
                    Some("/outputs/debug/other"),
                    FileFlavor::Normal
                ),
            ])
            .is_err()
        );
        assert!(
            expected_executable(&[output(
                "/outputs/private/native",
                Some("/outputs/debug/native"),
                FileFlavor::Linkable
            )])
            .is_err()
        );
    }
    #[test]
    fn publication_selection_preserves_exact_unit_and_complete_alias_set() {
        let command = capture_command(&data_command(), &mut (1024 * 1024)).unwrap();
        let mut row = entry(command, &"a".repeat(64));
        row.outputs = Arc::new(vec![super::super::build_runner::OutputFile {
            path: "/outputs/private/unit/bin".into(),
            hardlink: Some("/outputs/debug/bin".into()),
            export_path: Some("/outputs/export/bin".into()),
            flavor: super::super::FileFlavor::Normal,
        }]);
        let selected = row.publication_selection().unwrap();
        assert_eq!(selected.unit_sha256, "a".repeat(64));
        assert_eq!(selected.unit_id, "equality-data");
        assert_eq!(
            selected.destinations,
            [
                b"/outputs/debug/bin".to_vec(),
                b"/outputs/export/bin".to_vec()
            ]
        );
        Arc::get_mut(&mut row.outputs).unwrap()[0].export_path = Some("/outputs/debug/bin".into());
        assert!(
            row.publication_selection().is_err(),
            "two output slots cannot collapse to one destination"
        );
    }
    #[test]
    fn actual_builder_snapshot_binds_all_arguments_and_full_raw_environment() {
        let command = capture_command(&data_command(), &mut (1024 * 1024)).unwrap();
        assert!(
            command
                .environment
                .iter()
                .any(|(name, value)| name == b"raw_\xff" && value == b"value_\xfe")
        );
        let entries = [entry(command.clone(), "equality-data")];
        assert_eq!(matching_command(&entries, &command).unwrap(), 0);
        for alteration in 0..12 {
            let mut changed = command.clone();
            match alteration {
                0 => changed.program.push(b'x'),
                1 => changed.arg0 = Some(b"another-compiler".to_vec()),
                2 => changed.cwd.push(b'x'),
                3 => changed.args[3] = b"feature=\"other\"".to_vec(),
                4 => changed.args[4] = b"-Ctarget-feature=-crc".to_vec(),
                5 => changed.args[6] = b"dependency=/foreign/libdependency.rlib".to_vec(),
                6 => changed.args[8] = b"/foreign-output".to_vec(),
                7 => changed.args.swap(0, 1),
                8 => changed
                    .environment
                    .retain(|(name, _)| name != b"OBSERVED_BY_ENV_MACRO"),
                9 => {
                    changed
                        .environment
                        .iter_mut()
                        .find(|(name, _)| name == b"raw_\xff")
                        .unwrap()
                        .1 = b"value_\xff".to_vec()
                }
                10 => {
                    changed
                        .environment
                        .iter_mut()
                        .find(|(name, _)| name == b"CARGO_MAKEFLAGS")
                        .unwrap()
                        .1 = b"--jobserver-auth=9,10".to_vec()
                }
                11 => changed
                    .environment
                    .push((b"ADDED_ENV_MACRO_INPUT".to_vec(), b"43".to_vec())),
                _ => unreachable!(),
            }
            assert!(
                matching_command(&entries, &changed).is_err(),
                "alteration {alteration}"
            );
        }
    }
    #[test]
    fn duplicate_resolved_command_rows_are_refused_without_deduplicating_units() {
        let command = capture_command(&data_command(), &mut (1024 * 1024)).unwrap();
        let entries = [
            entry(command.clone(), "first-data-unit"),
            entry(command.clone(), "second-data-unit"),
        ];
        assert!(
            matching_command(&entries, &command)
                .unwrap_err()
                .to_string()
                .contains("ambiguous")
        );
        assert_eq!(entries.len(), 2);
    }
    #[test]
    fn expected_command_capture_refuses_exhausted_retained_budget() {
        let mut remaining = 1;
        assert!(capture_command(&data_command(), &mut remaining).is_err());
        assert_eq!(remaining, 1);
    }
}
