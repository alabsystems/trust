//! Live original output/SDK input custody, separate from phase admission and
//! from proof-gated PreparedTests. Nothing here accepts a serialized grant.
use super::TestAction;
use crate::compiler::{Compilation, Unit};
use crate::util::CargoResult;
use std::sync::Arc;

#[cfg(unix)]
mod supported {
    use super::super::evidence::Evidence;
    use super::*;
    use anyhow::Context as _;
    use std::collections::BTreeMap;
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt as _;
    use std::path::{Path, PathBuf};
    use std::time::{Duration, Instant};
    use trust_resource_controller::workload::{InputFile, host::produced};
    use trust_resource_provenance::program::{
        HeldProgram,
        produced::{HeldOutputRoot, HeldProducedProgram},
    };
    use trust_test_execution::workload::TARGETS;

    /// These are the same actually opened owners retained before compilation.
    /// Their presence is input custody, never original host/phase authority.
    pub(crate) struct Inputs {
        invocation: InputPlan,
        output: OutputRoot,
        sdk: Arc<HeldProgram>,
        pub evidence: Arc<Evidence>,
        _program_reservation:
            Option<Arc<trust_resource_controller::descriptors::OriginalInputPermit>>,
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        paired_subject: Option<Arc<crate::compiler::qualification::subject::Subject>>,
        master: Option<Arc<Inputs>>,
        sources: Vec<Arc<trust_resource_controller::descriptors::AdmittedPackageSource>>,
        native_node: Option<trust_resource_controller::native_job::NodeId>,
    }
    enum OutputRoot {
        Original(HeldOutputRoot),
        Selected(Arc<trust_resource_controller::descriptors::AdmittedOutputRoot>),
    }
    impl std::ops::Deref for OutputRoot {
        type Target = HeldOutputRoot;
        fn deref(&self) -> &HeldOutputRoot {
            match self {
                Self::Original(root) => root,
                Self::Selected(root) => root.original(),
            }
        }
    }
    enum InputPlan {
        Workload(trust_resource_controller::workload::WorkloadInvocation),
        NativeJob(Arc<trust_resource_controller::native_job::Plan>),
    }
    impl InputPlan {
        fn header(&self) -> trust_resource_controller::native_job::RootHeader<'_> {
            match self {
                Self::Workload(plan) => {
                    trust_resource_controller::native_job::RootHeader::workload(plan)
                }
                Self::NativeJob(plan) => plan.header(),
            }
        }
    }
    impl std::fmt::Debug for Inputs {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("OriginalWorkloadInputs")
                .field("output", &self.output.path())
                .finish_non_exhaustive()
        }
    }
    impl Inputs {
        /// Borrow the SAME originally opened root; callers must not reopen or
        /// relabel a pathname as selected output custody.
        pub(crate) fn held_output_root(&self) -> &HeldOutputRoot {
            &self.output
        }
        pub(crate) fn sdk(&self) -> &Arc<HeldProgram> {
            &self.sdk
        }
        pub fn from_opened(
            invocation: trust_resource_controller::workload::WorkloadInvocation,
            output: HeldOutputRoot,
            sdk: Arc<HeldProgram>,
            evidence: Arc<Evidence>,
        ) -> CargoResult<Self> {
            invocation.validate()?;
            let mut digest = cargo_util::Sha256::new();
            digest.update(&invocation.encode()?);
            Self::from_original_binding(
                InputPlan::Workload(invocation),
                digest.finish(),
                output,
                sdk,
                evidence,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                None,
            )
        }
        /// Preserve the complete initial request binding after its actual
        /// native adopter. This owns the same opened DATA, not a Host grant;
        /// original Root/SDK/phase authority stays with Startup and its bank.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        pub(crate) fn from_initial_opened(
            request: &trust_resource_controller::workload::host::initial::ReadyRequest,
            output: HeldOutputRoot,
            sdk: Arc<HeldProgram>,
            evidence: Arc<Evidence>,
        ) -> CargoResult<Self> {
            request.validate()?;
            let mut digest = cargo_util::Sha256::new();
            digest.update(&request.encode()?);
            Self::from_original_binding(
                InputPlan::Workload(request.invocation.clone()),
                digest.finish(),
                output,
                sdk,
                evidence,
                None,
            )
        }
        /// Distinct complete-plan binding for actual paired startup. The old
        /// consumer subplan remains DATA; it never receives a fabricated v1
        /// startup or a hash of only Invocation40.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        pub fn from_paired_opened(
            invocation: &trust_resource_controller::paired_qualification::PairedInvocation,
            descriptor_budget: &Arc<trust_resource_controller::descriptors::DescriptorBudget>,
            output: HeldOutputRoot,
            sdk: Arc<HeldProgram>,
            evidence: Arc<Evidence>,
        ) -> CargoResult<Self> {
            invocation.validate()?;
            let mut digest = cargo_util::Sha256::new();
            digest.update(&invocation.binding_preimage()?);
            let subject = crate::compiler::qualification::subject::Subject::capture_admitted(
                &invocation.ay,
                evidence.deadline(),
                descriptor_budget,
                &path(&invocation.consumer.output_root),
                &path(&invocation.consumer.cargo_home),
            )?;
            Self::from_original_binding(
                InputPlan::Workload(invocation.consumer.clone()),
                digest.finish(),
                output,
                sdk,
                evidence,
                Some(subject),
            )
        }
        /// General-job input custody binds the actual full106 plan and SAME
        /// originally opened master output/SDK/evidence, without fixed harnesses.
        pub(crate) fn from_native_job_opened(
            plan: Arc<trust_resource_controller::native_job::Plan>,
            output: HeldOutputRoot,
            sdk: Arc<HeldProgram>,
            evidence: Arc<Evidence>,
            reservation: Arc<trust_resource_controller::descriptors::OriginalInputPermit>,
            sources: Vec<Arc<trust_resource_controller::descriptors::AdmittedPackageSource>>,
        ) -> CargoResult<Self> {
            plan.validate()?;
            let mut digest = cargo_util::Sha256::new();
            digest.update(&plan.binding_preimage()?);
            let mut inputs = Self::from_original_binding(
                InputPlan::NativeJob(plan),
                digest.finish(),
                output,
                sdk,
                evidence,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                None,
            )?;
            inputs._program_reservation = Some(reservation);
            let InputPlan::NativeJob(plan) = &inputs.invocation else {
                unreachable!()
            };
            anyhow::ensure!(
                sources.len() == plan.sources.len(),
                "native job omitted a declared original source"
            );
            for (source, declared) in sources.iter().zip(&plan.sources) {
                source.validate(inputs.evidence.deadline())?;
                anyhow::ensure!(
                    source.path() == path(&declared.root)
                        && source.content_digest() == &declared.namespace_sha256,
                    "native job source capsule differs from its full original plan"
                );
            }
            inputs.sources = sources;
            Ok(inputs)
        }
        fn from_original_binding(
            invocation: InputPlan,
            invocation_sha256: [u8; 32],
            output: HeldOutputRoot,
            sdk: Arc<HeldProgram>,
            evidence: Arc<Evidence>,
            #[cfg(any(target_os = "linux", target_os = "macos"))] paired_subject: Option<
                Arc<crate::compiler::qualification::subject::Subject>,
            >,
        ) -> CargoResult<Self> {
            let header = invocation.header();
            let until = Instant::now() + Duration::from_secs(20);
            output.validate(until)?;
            sdk.validate(until)?;
            anyhow::ensure!(
                !output.path().starts_with(sdk.root())
                    && !sdk.root().starts_with(output.path())
                    && evidence.path().starts_with(output.path())
                    && evidence.sdk_matches(&sdk)
                    && evidence.invocation_sha256() == invocation_sha256,
                "workload input/evidence owners are not the same disjoint output/SDK population"
            );
            anyhow::ensure!(
                output.path() == path(&header.output_root)
                    && sdk.root() == path(&header.root)
                    && sdk.program() == path(&header.program.path)
                    && sdk.observation().executable.sha256 == hex::encode(header.program.sha256),
                "workload invocation does not bind its actual original output/SDK inputs"
            );
            Ok(Self {
                invocation,
                output: OutputRoot::Original(output),
                sdk,
                evidence,
                _program_reservation: None,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                paired_subject,
                master: None,
                sources: Vec::new(),
                native_node: None,
            })
        }
        pub(crate) fn native_plan(
            &self,
        ) -> Option<&Arc<trust_resource_controller::native_job::Plan>> {
            match &self.invocation {
                InputPlan::NativeJob(plan) => Some(plan),
                _ => None,
            }
        }
        pub(crate) fn native_source(
            &self,
            index: usize,
        ) -> CargoResult<&Arc<trust_resource_controller::descriptors::AdmittedPackageSource>>
        {
            if let Some(master) = &self.master {
                return master.native_source(index);
            }
            self.sources.get(index).ok_or_else(|| {
                anyhow::anyhow!("native source omitted from actual original population")
            })
        }
        pub(crate) fn native_compile_node(
            &self,
        ) -> Option<trust_resource_controller::native_job::NodeId> {
            self.native_node
        }
        pub(crate) fn native_master(&self) -> Option<&Arc<Self>> {
            self.master.as_ref()
        }
        pub(crate) fn native_selected_root(
            &self,
        ) -> Option<&Arc<trust_resource_controller::descriptors::AdmittedOutputRoot>> {
            match &self.output {
                OutputRoot::Selected(owner) => Some(owner),
                _ => None,
            }
        }
        pub(crate) fn native_compile_inputs(
            self: &Arc<Self>,
            selected: Arc<trust_resource_controller::descriptors::AdmittedOutputRoot>,
            node: trust_resource_controller::native_job::NodeId,
        ) -> CargoResult<Arc<Self>> {
            self.validate()?;
            let plan = self
                .native_plan()
                .context("native compilation cannot use fixed workload inputs")?;
            anyhow::ensure!(
                self.master.is_none(),
                "native node inputs require the original master capsule"
            );
            let Some(trust_resource_controller::native_job::Node {
                kind: trust_resource_controller::native_job::Kind::Compile { source, output, .. },
                ..
            }) = plan.nodes.get(node.0 as usize)
            else {
                anyhow::bail!("native compile selected a different node kind")
            };
            self.native_source(*source as usize)?
                .validate(self.evidence.deadline())?;
            selected.validate(self.evidence.deadline())?;
            anyhow::ensure!(
                selected.original().derived_from(self.held_output_root())
                    && selected.original().path() == path(&plan.outputs[*output as usize].root),
                "native compile root is not its original master-derived declared selection"
            );
            Ok(Arc::new(Self {
                invocation: InputPlan::NativeJob(plan.clone()),
                output: OutputRoot::Selected(selected),
                sdk: self.sdk.clone(),
                evidence: self.evidence.clone(),
                _program_reservation: self._program_reservation.clone(),
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                paired_subject: None,
                master: Some(self.clone()),
                sources: Vec::new(),
                native_node: Some(node),
            }))
        }
        pub fn validate(&self) -> CargoResult<()> {
            let until = self
                .evidence
                .deadline()
                .min(Instant::now() + Duration::from_secs(60));
            if let Some(master) = &self.master {
                master.validate()?;
            }
            for source in &self.sources {
                source.validate(until)?;
            }
            let mut failures = Vec::new();
            if let Err(error) = self.output.validate(until) {
                failures.push(format!("original output: {error:#}"));
            }
            if let Err(error) = self.sdk.validate(until) {
                failures.push(format!("original SDK: {error:#}"));
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(subject) = &self.paired_subject
                && let Err(error) = subject.validate()
            {
                failures.push(format!("original AY subject: {error:#}"));
            }
            anyhow::ensure!(
                failures.is_empty(),
                "original workload inputs changed: {}",
                failures.join("; ")
            );
            Ok(())
        }
        pub fn validate_target(&self, target: &Path) -> CargoResult<()> {
            self.validate()?;
            anyhow::ensure!(
                target.as_os_str() == self.output.path().as_os_str(),
                "workload compilation selected a different original target/output root"
            );
            Ok(())
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        pub(crate) fn require_ay_default_policy(&self) -> CargoResult<()> {
            self.validate()?;
            self.paired_subject
                .as_ref()
                .ok_or_else(|| {
                    anyhow::anyhow!("AY policy requires actual complete paired input binding")
                })?
                .require_default_policy()
        }
        pub fn configure_harness(
            &self,
            command: &mut cargo_util::ProcessBuilder,
        ) -> CargoResult<()> {
            self.validate()?;
            let InputPlan::Workload(invocation) = &self.invocation else {
                anyhow::bail!("native job cannot use fixed workload harness configuration");
            };
            for (name, value) in [
                ("CARGO", path(&invocation.program.path)),
                ("RUSTC", path(&invocation.compiler.path)),
                ("CARGO_HOME", path(&invocation.cargo_home)),
                ("TRUST_TOOLCHAIN_BIN", path(&invocation.root).join("bin")),
                (
                    "AY_PB_REFUTATION_PROOF_SRC",
                    path(&invocation.refutation_step.path),
                ),
                (
                    "AY_PB_REFUTATION_LOOP_PROOF_SRC",
                    path(&invocation.refutation_loop.path),
                ),
                ("TRUST_SPEC_SRC", path(&invocation.trust_spec_source.path)),
            ] {
                command.env(name, value);
            }
            for (name, value) in [
                ("LANG", "C"),
                ("LC_ALL", "C"),
                ("CARGO_CACHE_RUSTC_INFO", "0"),
                ("TRUST_VC_DISABLE_VC_CACHE", "1"),
                ("RUST_TEST_THREADS", "1"),
            ] {
                command.env(name, value);
            }
            Ok(())
        }
    }
    fn path(bytes: &[u8]) -> PathBuf {
        PathBuf::from(OsString::from_vec(bytes.to_vec()))
    }
    struct Artifact {
        unit: Unit,
        path: PathBuf,
        original: Arc<NativeOutput>,
    }

    /// Same live produced-input/output/SDK owners, shareable only by retaining
    /// this actual owner. No descriptor/path/DTO constructor is exposed. The
    /// queue retains the Unit separately because Unit is coordinator-local.
    pub(crate) struct NativeOutput {
        inputs: Arc<Inputs>,
        leases: Arc<crate::compiler::build_runner::OriginalOutputLeases>,
        image: Arc<HeldProducedProgram>,
        runtime_roots: Vec<PathBuf>,
        materialization: Option<super::super::Materialization>,
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        published: Option<Arc<crate::compiler::candidate_dependencies::PublishedProgram>>,
    }
    impl NativeOutput {
        pub(crate) fn project_runtime_roots(
            output: &Path,
            sdk: &Path,
            program: &Path,
            normal: Vec<PathBuf>,
        ) -> CargoResult<Vec<PathBuf>> {
            produced_runtime_roots(output, sdk, program, normal)
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        pub(crate) fn from_published(
            published: Arc<crate::compiler::candidate_dependencies::PublishedProgram>,
        ) -> CargoResult<Arc<Self>> {
            // Pure original association only. All program/loader capture was
            // completed under paid local IO BEFORE coordinator acknowledgement.
            published.require_acknowledged()?;
            Ok(Arc::new(Self {
                inputs: published.master().clone(),
                leases: published.layout().clone(),
                image: published.image().clone(),
                runtime_roots: published.runtime_roots().to_vec(),
                materialization: None,
                published: Some(published),
            }))
        }
        /// Capture only a current native UnitOutput supplied by the live
        /// BuildRunner under its original precompile Layout owner. Saved path
        /// or digest data cannot call this as an execution grant.
        pub(crate) fn capture(
            inputs: Arc<Inputs>,
            compilation: &Compilation<'_>,
            output: &crate::compiler::UnitOutput,
            leases: Arc<crate::compiler::build_runner::OriginalOutputLeases>,
            materialization: super::super::Materialization,
        ) -> CargoResult<Arc<Self>> {
            inputs.validate()?;
            leases.validate(inputs.output.path())?;
            anyhow::ensure!(
                compilation.target_runner(output.unit.kind).is_none(),
                "native workload output cannot use a custom target runner"
            );
            let executable = output.path.canonicalize()?;
            anyhow::ensure!(
                executable.as_os_str() == output.path.as_os_str(),
                "workload output path is not the original canonical UnitOutput"
            );
            let (sha256, _) =
                super::super::super::exact_regular_test_executable_identity(&executable)?;
            let expected: [u8; 32] = hex::decode(sha256)?
                .try_into()
                .map_err(|_| anyhow::anyhow!("native output digest width"))?;
            let roots = produced_runtime_roots(
                inputs.output.path(),
                inputs.sdk.root(),
                &executable,
                compilation.target_runtime_search_paths(&output.unit.pkg, output.unit.kind),
            )?;
            let image = inputs.output.program(
                inputs.sdk.clone(),
                &executable,
                &expected,
                &roots,
                Instant::now() + Duration::from_secs(60),
            )?;
            let original = Arc::new(Self {
                inputs,
                leases,
                image: Arc::new(image),
                runtime_roots: roots,
                materialization: Some(materialization),
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                published: None,
            });
            original.validate(Instant::now() + Duration::from_secs(30))?;
            Ok(original)
        }
        pub(crate) fn image(&self) -> &HeldProducedProgram {
            &self.image
        }
        pub(crate) fn validate(&self, deadline: Instant) -> CargoResult<()> {
            self.leases.validate(self.image.output_root())?;
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(published) = &self.published {
                published.validate(deadline)?;
                return Ok(());
            }
            // The image retains these SAME output/SDK owners internally and
            // validates both. Avoid hashing them twice in one boundary check.
            self.image.validate(deadline)?;
            Ok(())
        }
        pub(crate) fn invocation_sha256(&self) -> [u8; 32] {
            self.inputs.evidence.invocation_sha256()
        }
        pub(crate) fn registration(
            &self,
            key: produced::Key,
            deadline: Instant,
        ) -> CargoResult<(produced::Registration, std::os::fd::BorrowedFd<'_>)> {
            use std::os::unix::ffi::OsStrExt;
            self.leases.validate(self.image.output_root())?;
            anyhow::ensure!(
                key.invocation_sha256 == self.invocation_sha256()
                    && key.root_attempt == self.inputs.evidence.root_attempt(),
                "native output registration selected a different original invocation"
            );
            let digest = hex::decode(&self.image.observation().executable.sha256)?;
            let request = produced::Registration {
                key,
                program: InputFile {
                    path: self.image.program().as_os_str().as_bytes().to_vec(),
                    sha256: digest
                        .try_into()
                        .map_err(|_| anyhow::anyhow!("native digest width"))?,
                },
                runtime_roots: self
                    .runtime_roots
                    .iter()
                    .map(|path| path.as_os_str().as_bytes().to_vec())
                    .collect(),
                producer_attempt: self.producer_attempt()?,
            };
            request.validate()?;
            Ok((request, self.image.executable_descriptor(deadline)?))
        }
        fn producer_attempt(&self) -> CargoResult<Option<[u8; 16]>> {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(published) = &self.published {
                anyhow::ensure!(
                    self.materialization.is_none(),
                    "published image cannot graft another materialization"
                );
                published.require_acknowledged()?;
                return Ok(Some(published.producer_attempt()));
            }
            Ok(self
                .materialization
                .context("native output lost its actual materialization owner")?
                .producer_attempt())
        }
    }

    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn actual_input_fixture(
        parent: &Path,
        materialization: super::super::Materialization,
    ) -> Arc<NativeOutput> {
        use std::os::unix::ffi::OsStrExt;
        use trust_resource_controller::workload::WorkloadInvocation;
        // Real thin input images and actual original Layout guards only.
        // These copied test images are NOT managed SDKs, compiler products or
        // authenticated host execution fixtures. No positive register is faked.
        let parent = parent.canonicalize().unwrap();
        let sdk_root = parent.join("input-sdk");
        std::fs::create_dir_all(sdk_root.join("bin")).unwrap();
        let program = sdk_root.join("bin/targo");
        std::fs::copy(std::env::current_exe().unwrap(), &program).unwrap();
        std::fs::copy(
            std::env::current_exe().unwrap(),
            sdk_root.join("bin/trustc"),
        )
        .unwrap();
        let mut digest = cargo_util::Sha256::new();
        digest.update_path(&program).unwrap();
        let image_digest = digest.finish();
        let deadline = Instant::now() + Duration::from_secs(60);
        let sdk =
            Arc::new(HeldProgram::open(&sdk_root, &program, &image_digest, deadline).unwrap());
        let leases = Arc::new(
            crate::compiler::build_runner::OriginalOutputLeases::actual_layout_fixture(&parent),
        );
        let output_path = parent.join("target");
        let source = parent.join("source");
        let home = parent.join("cargo-home");
        std::fs::create_dir(&source).unwrap();
        std::fs::create_dir(&home).unwrap();
        let input = |path: PathBuf| {
            std::fs::write(&path, b"fixture bound source input").unwrap();
            let mut hash = cargo_util::Sha256::new();
            hash.update_path(&path).unwrap();
            InputFile {
                path: path.as_os_str().as_bytes().to_vec(),
                sha256: hash.finish(),
            }
        };
        let invocation = WorkloadInvocation {
            invocation: [4; 16],
            observed_host_store: None,
            root: sdk_root.as_os_str().as_bytes().to_vec(),
            program: InputFile {
                path: program.as_os_str().as_bytes().to_vec(),
                sha256: image_digest,
            },
            compiler: InputFile {
                path: sdk_root.join("bin/trustc").as_os_str().as_bytes().to_vec(),
                sha256: image_digest,
            },
            cwd: source.as_os_str().as_bytes().to_vec(),
            cargo_home: home.as_os_str().as_bytes().to_vec(),
            output_root: output_path.as_os_str().as_bytes().to_vec(),
            refutation_step: input(source.join("step.rs")),
            refutation_loop: input(source.join("loop.rs")),
            trust_spec_source: input(source.join("spec.rs")),
            repetitions: 1,
            timeout_ns: 1_000_000_000,
        };
        let mut binding = cargo_util::Sha256::new();
        binding.update(&invocation.encode().unwrap());
        let (output, writer) =
            HeldOutputRoot::open_with_evidence(&output_path, &sdk, [1; 16], 4096, 8, deadline)
                .unwrap();
        let evidence =
            Evidence::new(writer, sdk.clone(), [1; 16], binding.finish(), deadline).unwrap();
        let inputs =
            Arc::new(Inputs::from_opened(invocation, output, sdk.clone(), evidence).unwrap());
        let executable = output_path.join("debug/deps/native-harness");
        std::fs::create_dir_all(executable.parent().unwrap()).unwrap();
        std::fs::copy(&program, &executable).unwrap();
        // Qualification may run an immutable source image (0500). This is an
        // independent fixture-owned output inode; its deliberate drift actors
        // need owner write permission BEFORE native input capture. Never alter
        // the preserved source image or permissions of already-held inputs.
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755)).unwrap();
        let image = inputs
            .output
            .program(sdk, &executable, &image_digest, &[], deadline)
            .unwrap();
        Arc::new(NativeOutput {
            inputs,
            leases,
            image: Arc::new(image),
            runtime_roots: Vec::new(),
            materialization: Some(materialization),
            published: None,
        })
    }
    /// NonClone actual compiled unit/output owner. The original output/SDK
    /// descriptors and complete supported runtime remain live through workers.
    /// Host preparation still must independently authorize every actual GO.
    pub(crate) struct OwnedOutputs {
        inputs: Arc<Inputs>,
        artifacts: BTreeMap<String, Artifact>,
        leases: Arc<crate::compiler::build_runner::OriginalOutputLeases>,
    }
    impl OwnedOutputs {
        pub fn capture(
            inputs: Arc<Inputs>,
            compilation: &Compilation<'_>,
            leases: Arc<crate::compiler::build_runner::OriginalOutputLeases>,
            materializations: &crate::util::data_structures::HashMap<
                Unit,
                super::super::Materialization,
            >,
        ) -> CargoResult<Self> {
            inputs.validate()?;
            leases.validate(inputs.output.path())?;
            anyhow::ensure!(
                compilation.tests.len() == TARGETS.len(),
                "workload output population does not contain exactly two native harnesses"
            );
            let mut artifacts = BTreeMap::new();
            for target in TARGETS {
                let outputs = compilation
                    .tests
                    .iter()
                    .filter(|output| output.unit.target.name() == target)
                    .collect::<Vec<_>>();
                anyhow::ensure!(
                    outputs.len() == 1,
                    "workload native output is missing or ambiguous: {target}"
                );
                let output = outputs[0];
                let materialization = *materializations.get(&output.unit).ok_or_else(|| {
                    anyhow::anyhow!("native output has no actual successful unit materialization")
                })?;
                anyhow::ensure!(
                    output.unit.target.harness()
                        && compilation.target_runner(output.unit.kind).is_none(),
                    "workload output requires the original native harness without a custom runner"
                );
                let original = NativeOutput::capture(
                    inputs.clone(),
                    compilation,
                    output,
                    leases.clone(),
                    materialization,
                )?;
                artifacts.insert(
                    target.to_owned(),
                    Artifact {
                        unit: output.unit.clone(),
                        path: output.path.clone(),
                        original,
                    },
                );
            }
            let owner = Self {
                inputs,
                artifacts,
                leases,
            };
            owner.validate()?;
            Ok(owner)
        }
        pub fn validate(&self) -> CargoResult<()> {
            self.inputs.validate()?;
            self.leases.validate(self.inputs.output.path())?;
            for artifact in self.artifacts.values() {
                artifact
                    .original
                    .validate(Instant::now() + Duration::from_secs(30))?;
            }
            Ok(())
        }
        pub fn observations(
            &self,
        ) -> BTreeMap<&str, &trust_resource_provenance::program::ProgramObservation> {
            self.artifacts
                .iter()
                .map(|(target, artifact)| (target.as_str(), artifact.original.image.observation()))
                .collect()
        }
        pub fn for_action(&self, action: &TestAction) -> CargoResult<&HeldProducedProgram> {
            self.validate()?;
            let artifact = self
                .artifacts
                .get(action.unit.target.name())
                .ok_or_else(|| {
                    anyhow::anyhow!("native action has no original compiled output owner")
                })?;
            anyhow::ensure!(
                artifact.unit == action.unit && artifact.path == action.path,
                "native action is not the same actual compiled unit/output"
            );
            Ok(&artifact.original.image)
        }
        pub(crate) fn native_outputs(&self) -> CargoResult<Vec<Arc<NativeOutput>>> {
            self.validate()?;
            TARGETS
                .iter()
                .map(|target| {
                    self.artifacts
                        .get(*target)
                        .map(|artifact| artifact.original.clone())
                        .ok_or_else(|| {
                            anyhow::anyhow!("complete original native output population changed")
                        })
                })
                .collect()
        }
    }
    fn produced_runtime_roots(
        output: &Path,
        sdk: &Path,
        program: &Path,
        normal: Vec<PathBuf>,
    ) -> CargoResult<Vec<PathBuf>> {
        let parent = program
            .parent()
            .ok_or_else(|| anyhow::anyhow!("native output has no parent"))?;
        // The held produced-image profile already includes the executable's
        // parent and these exact original-SDK defaults. Supplying them again
        // is refused as a duplicate by that profile, not additional custody.
        let sdk_defaults = [
            sdk.join("lib"),
            sdk.join("lib/rustlib/aarch64-apple-darwin/lib"),
        ];
        let mut roots = Vec::new();
        for path in normal {
            if path == parent || sdk_defaults.contains(&path) {
                continue;
            }
            anyhow::ensure!(
                path.starts_with(output),
                "native workload runtime search path escapes its original output/SDK profile"
            );
            roots.push(path);
        }
        roots.sort();
        roots.dedup();
        Ok(roots)
    }
    #[cfg(test)]
    #[test]
    fn normal_runtime_prefix_preserves_extra_roots_without_repeating_implicit_profile_inputs() {
        let output = Path::new("/owned/output");
        let sdk = Path::new("/owned/sdk");
        let program = output.join("debug/deps/harness");
        let root = output.join("debug");
        let native = output.join("debug/build/pkg/out");
        let actual = produced_runtime_roots(
            output,
            sdk,
            &program,
            vec![
                native.clone(),
                root.clone(),
                program.parent().unwrap().to_owned(),
                sdk.join("lib/rustlib/aarch64-apple-darwin/lib"),
                root.clone(),
                sdk.join("lib"),
            ],
        )
        .unwrap();
        assert_eq!(actual, vec![root, native]);
        assert!(
            produced_runtime_roots(
                output,
                sdk,
                &program,
                vec![PathBuf::from("/unbound/runtime")]
            )
            .is_err()
        );
    }
    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn initial_input_custody_retains_the_complete_request_instead_of_legacy_invocation_binding() {
        use std::os::unix::ffi::OsStrExt as _;
        use trust_resource_controller::{
            ContextQuery, JobBinding, workload::host::initial::ReadyRequest,
        };
        let directory = tempfile::tempdir().unwrap();
        let original = actual_input_fixture(directory.path(), super::super::Materialization::Warm);
        let InputPlan::Workload(invocation) = &original.inputs.invocation else {
            unreachable!()
        };
        let mut invocation = invocation.clone();
        let root = directory
            .path()
            .canonicalize()
            .unwrap()
            .join("initial-target");
        std::fs::create_dir(&root).unwrap();
        invocation.output_root = root.as_os_str().as_bytes().to_vec();
        let request = ReadyRequest {
            query: ContextQuery {
                binding: JobBinding {
                    session: "s-ab".into(),
                    root_attempt: [1; 16],
                    capability: [2; 32],
                },
                call_attempt: [9; 16],
            },
            invocation: invocation.clone(),
            phase: [10; 16],
        };
        let sdk = original.inputs.sdk.clone();
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut hash = cargo_util::Sha256::new();
        hash.update(&request.encode().unwrap());
        let digest = hash.finish();
        let (output, writer) =
            HeldOutputRoot::open_with_evidence(&root, &sdk, [1; 16], 4096, 8, deadline).unwrap();
        let evidence = Evidence::new(writer, sdk.clone(), [1; 16], digest, deadline).unwrap();
        assert!(Inputs::from_opened(invocation, output, sdk.clone(), evidence.clone()).is_err());
        let inputs = Inputs::from_initial_opened(
            &request,
            HeldOutputRoot::open(&root, deadline).unwrap(),
            sdk.clone(),
            evidence.clone(),
        )
        .unwrap();
        inputs.validate().unwrap();
        assert_eq!(inputs.evidence.invocation_sha256(), digest);
        let mut changed = request;
        changed.phase = [11; 16];
        assert!(
            Inputs::from_initial_opened(
                &changed,
                HeldOutputRoot::open(&root, deadline).unwrap(),
                sdk,
                evidence
            )
            .is_err()
        );
        // Held input/evidence DATA only: this fixture creates no managed SDK,
        // authenticated startup, execution grant or successful compiler proof.
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
pub(crate) use supported::actual_input_fixture;
#[cfg(unix)]
pub(crate) use supported::{Inputs, NativeOutput, OwnedOutputs};

#[cfg(not(unix))]
mod unsupported {
    use super::*;
    #[derive(Debug)]
    pub(crate) struct Inputs {
        _unavailable: std::convert::Infallible,
    }
    impl Inputs {
        pub fn validate(&self) -> CargoResult<()> {
            anyhow::bail!("native workload input custody unavailable")
        }
        pub fn validate_target(&self, _: &std::path::Path) -> CargoResult<()> {
            anyhow::bail!("native workload input custody unavailable")
        }
        pub fn configure_harness(&self, _: &mut cargo_util::ProcessBuilder) -> CargoResult<()> {
            anyhow::bail!("native workload input custody unavailable")
        }
    }
    pub(crate) struct OwnedOutputs {
        _unavailable: std::convert::Infallible,
    }
    impl OwnedOutputs {
        pub fn capture(
            _: Arc<Inputs>,
            _: &Compilation<'_>,
            _: Arc<crate::compiler::build_runner::OriginalOutputLeases>,
            _: &crate::util::data_structures::HashMap<Unit, super::super::Materialization>,
        ) -> CargoResult<Self> {
            anyhow::bail!("native workload produced-input custody unavailable")
        }
        pub fn validate(&self) -> CargoResult<()> {
            anyhow::bail!("native workload produced-input custody unavailable")
        }
        pub fn for_action(&self, _: &TestAction) -> CargoResult<()> {
            anyhow::bail!("native workload produced-input custody unavailable")
        }
    }
}
#[cfg(not(unix))]
pub(crate) use unsupported::{Inputs, OwnedOutputs};
