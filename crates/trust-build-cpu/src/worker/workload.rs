//! Compiler extras borrow only the sole root bank's authenticated originals.

use std::fs::File;
use std::io::{self, Read};
use std::sync::Arc;
use std::time::{Duration, Instant};

use trust_resource_controller::client::workload::{
    AuthenticatedMemberCpu, MemberOriginalContext, WorkerLoan,
};
use trust_resource_controller::workload::host::{MemberOriginalRequest, worker};
use trust_resource_controller::{ContextQuery, Subject};

use super::{Admission as Backend, WorkerClient, gate};
use crate::{Lease, Owner, invalid};

#[derive(Clone)]
pub(super) struct Admission {
    origin: Arc<MemberOriginalContext>,
}

pub(super) fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(8)
}

fn nonce(root: [u8; 16]) -> io::Result<[u8; 16]> {
    let mut nonce = [0; 16];
    File::open("/dev/urandom")?.read_exact(&mut nonce)?;
    if nonce == [0; 16] || nonce == root {
        return Err(invalid("compiler worker nonce unavailable"));
    }
    Ok(nonce)
}

impl WorkerClient {
    /// Bind the actual authenticated primary to its sole root's worker bank.
    /// This constructor creates no original credit, GNU pool or CPU grant.
    /// Every extra still requires a fresh authenticated original-description
    /// exchange, and every positive return requires explicit SDK settlement.
    pub fn new_workload(
        local: jobserver::Client,
        received: AuthenticatedMemberCpu,
        owner: Owner,
        deadline: Instant,
    ) -> io::Result<Self> {
        drop(local.try_acquire()?);
        let (reply, file, origin) = received.into_retained_original();
        origin.validate(deadline)?;
        let original = origin.request();
        let expected = origin.observation();
        if owner.pid != std::process::id()
            || &reply.context.context != expected
            || !matches!(expected.subject, Subject::RegisteredMember { attempt, identity }
                if attempt == original.member_attempt && identity.pid == owner.pid)
            || expected.root_attempt != original.query.binding.root_attempt
        {
            return Err(invalid("compiler bank member differs from its original binding"));
        }
        // No domain open, acquire, unlock, counter or saved manifest is used:
        // this SAME original came from the live Host's already-paid Root bank.
        let implicit =
            Arc::new(crate::unix::continue_original_workload_file(reply.cpu.slot, file)?);
        origin.validate(deadline)?;
        Ok(Self {
            local,
            admission: Backend::Workload(Admission { origin }),
            implicit,
            owner,
            fence: None,
            admission_gate: Some(gate::Gate::new()),
        })
    }
}

impl Admission {
    pub(super) fn try_acquire(&self) -> io::Result<Option<(Lease, WorkerLoan)>> {
        let deadline = deadline();
        self.origin.validate(deadline)?;
        let original = self.origin.request();
        let expected = self.origin.observation();
        let request = worker::Request {
            original: MemberOriginalRequest {
                query: ContextQuery {
                    binding: original.query.binding.clone(),
                    call_attempt: nonce(expected.root_attempt)?,
                },
                member_attempt: original.member_attempt,
            },
            worker_request: nonce(expected.root_attempt)?,
        };
        let Some(received) = self
            .origin
            .controller()
            .workload_extra(&request, deadline)
            .map_err(io::Error::other)?
        else {
            return Ok(None);
        };
        if &received.observation().context.context != expected {
            return Err(invalid("compiler bank worker changed its authenticated context"));
        }
        let (reply, file, loan, origin) = received.into_retained_original();
        let worker::Decision::Granted { slot, .. } = reply.decision else {
            return Err(invalid("original worker has no actual granted description"));
        };
        if loan.slot() != slot {
            return Err(invalid("original worker loan/description differ"));
        }
        origin.validate(deadline)?;
        let lease = crate::unix::continue_original_workload_file(slot, file)?;
        lease.report_owner(self.worker_owner()?)?;
        origin.validate(deadline)?;
        self.origin.validate(deadline)?;
        Ok(Some((lease, loan)))
    }

    fn worker_owner(&self) -> io::Result<Owner> {
        crate::process_cpu::read(std::process::id())
            .map(|sample| sample.owner)
            .ok_or_else(|| invalid("compiler worker CPU owner unavailable"))
    }
}
