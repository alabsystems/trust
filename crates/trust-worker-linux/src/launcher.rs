//! Owned static-worker diagnostics. This is not native macro admission.
//!
//! The owner supplies pinned tool provenance. The entire admitted static worker
//! is trusted startup; it installs B2 before consuming untrusted invocation data.
//! No interpreter, DSO, worker proof bit or authenticated report is supported.
pub(crate) mod child;
mod custody;
mod elf;
mod input_closure;
pub(crate) mod snapshot;
mod transport;
mod tree;

use std::fs::File;
use std::os::fd::AsRawFd;
use std::time::Instant;

pub use input_closure::InputClosureIdentity;
pub(crate) use transport::Capture;
pub use transport::{InputIdentity, Outcome, Receipt};
use trust_process_isolation::{
    Binding, Budget, Charge, Envelope, Message, Phase, Session, SessionOwner,
};

use crate::native::NativeClosure;
use crate::{Error, KernelLimits};

#[derive(Debug, Clone, Copy)]
pub struct InputSource<'a> {
    pub file: &'a File,
    pub sha256: [u8; 32],
    pub size: u64,
    pub executable: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct LaunchLimits {
    pub kernel: KernelLimits,
    /// Sampled threshold, not a hard aggregate memory claim.
    pub sampled_leader_rss_bytes: u64,
    pub output_bytes_per_stream: usize,
    pub input_bytes: u64,
}

#[derive(Debug)]
pub struct PreparedStaticWorker {
    worker: snapshot::Snapshot,
    inputs: [Option<snapshot::Snapshot>; 27],
    count: usize,
    binding: Binding,
    limits: LaunchLimits,
    budget: Budget,
    session_owner: SessionOwner,
    input_identity: InputClosureIdentity,
    native: Option<NativeClosure>,
    prepared_at: Instant,
    input_bytes: u64,
}

impl PreparedStaticWorker {
    pub(crate) fn native_configuration(
        &self,
        session: &Session,
        begin: &Envelope,
    ) -> Result<crate::native::Configuration, Error> {
        self.check_session(session, begin)?;
        let expected = self.native.as_ref().map_or(0, NativeClosure::object_count);
        if self.count != expected {
            return Err(contract("native static input graph count"));
        }
        if let Some(native) = &self.native {
            native.check_data_inputs(&self.inputs[..self.count])?;
        }
        crate::native::Configuration::prepare(
            InputIdentity { sha256: self.worker.sha256, size: self.worker.size, executable: true },
            self.limits.input_bytes,
            self.native.as_ref(),
            session,
        )
    }
    /// Budget/deadline must already exist before the caller opens its sources.
    /// The caller also owns the trusted worker's source/build provenance.
    pub fn prepare(
        worker: &InputSource<'_>,
        inputs: &[InputSource<'_>],
        native: Option<NativeClosure>,
        session: &Session,
        limits: LaunchLimits,
    ) -> Result<Self, Error> {
        let budget = session.budget();
        let result = Self::prepare_inner(worker, inputs, native, session, limits);
        if result.is_err() {
            budget.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    fn prepare_inner(
        worker: &InputSource<'_>,
        inputs: &[InputSource<'_>],
        native: Option<NativeClosure>,
        session: &Session,
        limits: LaunchLimits,
    ) -> Result<Self, Error> {
        let budget = session.budget().clone();
        let binding = session.binding().clone();
        let prepared_at = Instant::now();
        checked(&budget)?;
        if session.phase() != Phase::AwaitReady {
            return Err(contract("session already started"));
        }
        // Reserve fixed bounded setup/receipt/teardown bookkeeping before any
        // work. Cleanup remains mandatory after refusal; it cannot reset or
        // request another grant. Retained output/input bytes are priced below.
        budget.charge(Charge { work: 16384, ..Charge::default() }).map_err(Error::Budget)?;
        binding.validate().map_err(Error::Budget)?;
        if !worker.executable
            || inputs.len() > 27
            || limits.input_bytes == 0
            || limits.output_bytes_per_stream == 0
            || limits.output_bytes_per_stream > 1024 * 1024
            || limits.sampled_leader_rss_bytes == 0
            || limits.kernel.address_space_bytes == 0
            || limits.kernel.address_space_bytes == u64::MAX
            || limits.kernel.stack_bytes == 0
            || limits.kernel.stack_bytes > limits.kernel.address_space_bytes
            || limits.kernel.file_bytes == 0
            || limits.kernel.file_bytes == u64::MAX
            || limits.kernel.descriptors < 64
            || limits.kernel.descriptors > 4096
        {
            return Err(contract("launch limits"));
        }
        budget
            .charge(Charge { work: 256 + 41 * (inputs.len() + 1) as u64, ..Charge::default() })
            .map_err(Error::Budget)?;
        let input_identity = InputClosureIdentity::from_plan(
            worker,
            inputs,
            native.as_ref().map(NativeClosure::digest),
        )?;
        if binding.worker != worker.sha256 || binding.input_closure != input_identity.digest() {
            return Err(contract("owner worker/closure binding"));
        }
        if let Some(native) = &native {
            native.check_invocation(&input_identity, session)?;
        }
        let mut input_bytes = worker.size;
        for input in inputs {
            input_bytes = input_bytes
                .checked_add(input.size)
                .ok_or_else(|| contract("input size overflow"))?;
        }
        if let Some(native) = &native {
            input_bytes = input_bytes
                .checked_add(native.input_bytes())
                .ok_or_else(|| contract("native input size overflow"))?;
        }
        if input_bytes > limits.input_bytes {
            return Err(contract("input bytes"));
        }
        let worker = snapshot::copy(worker, &budget)?;
        elf::admit(&worker.file, worker.size, &budget)?;
        let mut snapshots = std::array::from_fn(|_| None);
        for (at, input) in inputs.iter().enumerate() {
            snapshots[at] = Some(snapshot::copy(input, &budget)?);
        }
        checked(&budget)?;
        Ok(Self {
            worker,
            inputs: snapshots,
            count: inputs.len(),
            binding,
            limits,
            budget,
            session_owner: session.owner(),
            input_identity,
            native,
            prepared_at,
            input_bytes,
        })
    }

    /// The begin envelope binds only compiler-owned handles; ownership/semantic
    /// checks still belong to the compiler adapter before invoking this method.
    pub fn launch(
        self,
        arguments: &[&str],
        scratch: &File,
        begin: Envelope,
        session: Session,
    ) -> Result<OwnedWorker, Error> {
        self.check_session(&session, &begin)?;
        let result = OwnedWorker::start(self, arguments, scratch, begin, session, None);
        result
    }

    /// Additive static-worker custody under a freshly created cgroup2 child of
    /// the caller's exclusive delegated finite kernel owner. The caller keeps
    /// namespace removal and an outer hard original-deadline backstop. This
    /// admits no dynamic tool/runtime or source/proof/release authority.
    pub fn launch_contained(
        self,
        arguments: &[&str],
        scratch: &File,
        begin: Envelope,
        session: Session,
        parent: &File,
        name: &std::ffi::CStr,
    ) -> Result<OwnedWorker, Error> {
        self.check_session(&session, &begin)?;
        let tree =
            tree::Tree::create(parent, name, self.limits.kernel.address_space_bytes, &self.budget)?;
        OwnedWorker::start(self, arguments, scratch, begin, session, Some(tree))
    }

    // Check before spawning or creating an owned cgroup. Equal binding fields
    // and limits cannot substitute a reconstructed compiler conversation.
    fn check_session(&self, session: &Session, begin: &Envelope) -> Result<(), Error> {
        checked(&self.budget)?;
        if !self.session_owner.matches(session)
            || !self.budget.shares_owner(session.budget())
            || session.binding() != &self.binding
            || session.phase() != Phase::AwaitReady
            || begin.binding != self.binding
            || !matches!(begin.message, Message::Begin { .. })
        {
            self.budget.refuse(trust_process_isolation::Error::Identity);
            return Err(contract("original session/begin binding/phase"));
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct OwnedWorker {
    child: custody::Custody,
    stdout: File,
    stderr: File,
    control: std::os::unix::net::UnixStream,
    status: File,
    prepared: PreparedStaticWorker,
    outbound: Vec<u8>,
    session: Session,
}
impl OwnedWorker {
    pub fn pid(&self) -> u32 {
        self.child.pid() as u32
    }
    pub fn used_pidfd(&self) -> bool {
        self.child.used_pidfd()
    }
    fn start(
        prepared: PreparedStaticWorker,
        arguments: &[&str],
        scratch: &File,
        begin: Envelope,
        session: Session,
        tree: Option<tree::Tree>,
    ) -> Result<Self, Error> {
        let budget = prepared.budget.clone();
        let result = (|| {
            checked(&budget)?;
            let outbound =
                trust_process_isolation::encode(&begin, &budget).map_err(Error::Budget)?;
            let channels = match tree {
                Some(tree) => {
                    child::spawn_contained(&prepared, arguments, scratch.as_raw_fd(), tree)?
                }
                None => child::spawn(&prepared, arguments, scratch.as_raw_fd())?,
            };
            Ok(Self {
                child: channels.child,
                stdout: channels.stdout,
                stderr: channels.stderr,
                control: channels.control,
                status: channels.status,
                prepared,
                outbound,
                session,
            })
        })();
        if result.is_err() {
            budget.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
}

fn checked(budget: &Budget) -> Result<(), Error> {
    budget.check().map_err(Error::Budget)
}
fn contract(message: &'static str) -> Error {
    Error::Contract(message)
}
