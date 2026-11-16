//! A produced coordinator borrows the SAME retained Root phase and bank.
//! Request bytes never create CPU, GNU, output or native retirement authority.
use super::*;
use crate::compiler::{candidate_dependencies::Ledger, candidate_runner};
use crate::ops::cargo_test::workload::{Inputs, NativeOutput};
use crate::resource_v3::workload::bank::broker::RegisteredArtifact;
use std::os::fd::{AsFd as _, AsRawFd as _};
use std::os::unix::ffi::OsStringExt as _;
use std::time::Instant;
use trust_resource_controller::client::{
    ContainedProducedError, CoordinatorBrokerServer, MetadataIo,
};
use trust_resource_controller::workload::host::{self, coordinator, produced::ProducedRequest};
use trust_resource_controller::{Delegations, Descriptor, GnuTransport, Request, Role};

pub(in crate::compiler) struct Completed {
    pub(in crate::compiler) attempt: candidate_runner::lifecycle::Attempt,
    pub(in crate::compiler) phase_failure: Option<anyhow::Error>,
    // LAST: actual member/relay/server descriptions close before capacity.
    _descriptors: trust_resource_controller::descriptors::OriginalInputPermit,
    _transport: trust_resource_controller::descriptors::OriginalInputPermit,
}
impl ResourceRuntime {
    pub(in crate::compiler) fn run_coordinator(
        &self,
        frontend: Arc<NativeOutput>,
        inputs: Arc<Inputs>,
        plan: coordinator::Plan,
        leases: Arc<crate::compiler::build_runner::OriginalOutputLeases>,
        dependencies: &mut Option<Ledger>,
        deadline: Instant,
    ) -> CargoResult<Completed> {
        plan.validate()?;
        anyhow::ensure!(
            Instant::now() < deadline,
            "coordinator operation expired before admission"
        );
        // Selection runs only after the lexical preparation unit has closed.
        // The existing adapter positively drains the SAME bank before RPC.
        self.retain_workload_outputs(leases.clone(), inputs.held_output_root().path())?;
        self.enter_workload_foreign(host::phase::Kind::Coordinator, vec![frontend])?;
        let prepared = (|| -> CargoResult<_> {
            let phase = self
                .foreign
                .lock()
                .map_err(|_| anyhow::anyhow!("native coordinator phase poisoned"))?
                .as_ref()
                .context("coordinator lost actual phase")?
                .clone();
            anyhow::ensure!(
                phase.artifacts.len() == 1,
                "coordinator requires one registered original frontend"
            );
            let artifact: Arc<RegisteredArtifact> = phase.artifacts[0].clone();
            let primary = self
                .startup
                .workload_control
                .as_ref()
                .context("coordinator lost original broker")?
                .lock()
                .map_err(|_| anyhow::anyhow!("coordinator broker poisoned"))?
                .as_ref()
                .context("coordinator broker already settled")?
                .coordinator_primary(&artifact)?
                .context("coordinator original primary unavailable")?;
            let selected = inputs
                .native_selected_root()
                .context("coordinator lost selected original root")?
                .original()
                .clone();
            let sources = (0..plan.sources.len())
                .map(|index| inputs.native_source(index).cloned())
                .collect::<CargoResult<Vec<_>>>()?;
            let owner = candidate_runner::Inputs::new(
                self.startup.clone(),
                inputs
                    .native_master()
                    .context("coordinator lacks actual master inputs")?
                    .clone(),
                selected,
                plan.clone(),
                sources,
                leases.clone(),
                deadline,
            )?;
            let budget = self
                .startup
                .descriptor_budget
                .as_ref()
                .context("coordinator lost original descriptor budget")?;
            // Socket pair + actual transport duplicates (primary, endpoint,
            // complete original output population) and bounded validation IO.
            let (output_request, output_fds) = leases.output_offer(
                self.outputs
                    .lock()
                    .map_err(|_| anyhow::anyhow!("coordinator output registry poisoned"))?
                    .get(inputs.held_output_root().path())
                    .context("coordinator omitted selected original OFD receipt")?
                    .retained
                    .observation()
                    .key
                    .clone(),
                inputs.held_output_root().path(),
            )?;
            let fee = budget.reserve_original_inputs(
                output_fds
                    .len()
                    .checked_add(8)
                    .context("coordinator descriptor population overflow")?,
            )?;
            let transport = budget.reserve_member_transport()?;
            let (server, endpoint) = CoordinatorBrokerServer::pair()?;
            let lease = primary.lease();
            let registration = artifact.registered().registration();
            let member_attempt =
                resource_v3::call_attempt(self.startup.query.binding.root_attempt)?;
            let mut process = ProcessBuilder::new(artifact.original().image().program());
            process.cwd(
                std::path::PathBuf::from(std::ffi::OsString::from_vec(plan.manifest.path.clone()))
                    .parent()
                    .context("coordinator manifest has no parent")?,
            );
            for arg in plan.startup_args()? {
                process.arg(std::ffi::OsString::from_vec(arg));
            }
            let (command, _observed) = resource_v3::workload::produced::command::command(
                &process,
                &artifact.original().image().runtime_environment()?,
            )?;
            let request = coordinator::Request {
                contained: host::contained::Request {
                    operation: resource_v3::call_attempt(self.startup.query.binding.root_attempt)?,
                    gnu: phase.phase.gnu,
                    produced: ProducedRequest {
                        member: Request {
                            binding: self.startup.query.binding.clone(),
                            member_attempt,
                            role: Role::WorkloadProduced,
                            command,
                            delegations: Delegations {
                                cpu: None,
                                gnu: GnuTransport::None,
                                fences: Vec::new(),
                            },
                            timeout_ns: Some(plan.timeout_ns),
                        },
                        key: registration.key.clone(),
                        kind: host::MemberKind::Coordinator,
                        program_sha256: registration.program.sha256,
                        runtime_roots: registration.runtime_roots.clone(),
                    },
                },
                plan,
                primary: Descriptor {
                    source: lease.as_fd().as_raw_fd() as u32,
                    target: 6,
                },
                broker: Descriptor {
                    source: endpoint.as_fd().as_raw_fd() as u32,
                    target: 8,
                },
                cpu_slot: lease.slot(),
                outputs: output_request,
            };
            request.validate()?;
            request
                .contained
                .produced
                .validate_registered(registration)?;
            let factory = resource_v3::coordinator_compiler_factory(
                self.startup.clone(),
                primary.clone(),
                self.jobserver(),
                owner.clone(),
                member_attempt,
                deadline,
            );
            // The factory requires the actual bound coordinator. Construct the
            // relay only after binding, with no fallible work before delivery.
            Ok((
                artifact, primary, owner, factory, request, server, endpoint, fee, transport,
            ))
        })();
        let (artifact, primary, owner, factory, request, server, endpoint, fee, transport) =
            match prepared {
                Ok(prepared) => prepared,
                Err(error) => {
                    // No member request was sent and every local unbound loan has
                    // closed. Real Leave, rather than a local refund, returns GNU.
                    let leave = self.finish_workload_foreign(host::phase::Kind::Coordinator);
                    return Err(match leave {
                        Ok(()) => error,
                        Err(post) => error
                            .context(format!("coordinator pre-admission Leave failed: {post:#}")),
                    });
                }
            };
        primary.begin_coordinator(request.contained.produced.member.member_attempt)?;
        let relay = match candidate_runner::CompilerRelay::new(
            server,
            factory,
            owner,
            dependencies.take(),
            primary.clone(),
        ) {
            Ok(relay) => relay,
            Err(_) => resource_v3::workload::abort_unknown(),
        };
        let (_, output_fds) = match leases.output_offer(
            request.outputs.key.clone(),
            inputs.held_output_root().path(),
        ) {
            Ok(output) => output,
            Err(_) => resource_v3::workload::abort_unknown(),
        };
        // SAFETY: same original registered image/phase, primary, endpoint and
        // complete close-only Layouts are held through the native lifecycle.
        let offered_lease = primary.lease();
        let member = match unsafe {
            self.startup.client.workload_coordinator(
                artifact.registered(),
                &request,
                [offered_lease.as_fd(), endpoint.as_fd()],
                &output_fds,
                MetadataIo {
                    descriptions: Vec::new(),
                },
                deadline,
            )
        } {
            Ok(member) => member,
            Err(ContainedProducedError::BeforeRequest(_))
            | Err(ContainedProducedError::Refused)
            | Err(ContainedProducedError::Unknown { .. }) => {
                // There is no opaque command-bound not-delivered receipt for
                // this already-bound primary. Preserve Unknown conservatively.
                resource_v3::workload::abort_unknown()
            }
        };
        drop(output_fds);
        drop(endpoint); // The parent must not keep a spare child socket alive.
        let attempt = candidate_runner::lifecycle::run(
            member,
            relay,
            primary.clone(),
            artifact.clone(),
            self.jobserver(),
        );
        if attempt
            .require_retired_originals(&primary, &artifact)
            .is_err()
        {
            resource_v3::workload::abort_unknown();
        }
        // Native target/helper/EOF retirement and the asynchronous SAME Host
        // Return are separate facts. The broker continues to service returns
        // while this owner waits; Leave must not convert a transient occupied
        // table into a refusal that strands its original GNU escrow.
        let bank = match self.startup.workload_bank.as_ref() {
            Some(bank) => bank,
            None => resource_v3::workload::abort_unknown(),
        };
        let process = match self.startup.workload_process.as_ref() {
            Some(process) => process,
            None => resource_v3::workload::abort_unknown(),
        };
        loop {
            if Instant::now() >= deadline.min(process.deadline)
                || process.cancelled.load(Ordering::Acquire)
                || process.poisoned.load(Ordering::Acquire)
            {
                resource_v3::workload::abort_unknown();
            }
            match bank.current_drained() {
                Ok(true) => break,
                Ok(false) => std::thread::sleep(std::time::Duration::from_millis(5)),
                Err(_) => resource_v3::workload::abort_unknown(),
            }
        }
        let phase_failure = self
            .finish_workload_foreign(host::phase::Kind::Coordinator)
            .err();
        Ok(Completed {
            attempt,
            phase_failure,
            _descriptors: fee,
            _transport: transport,
        })
    }
}
