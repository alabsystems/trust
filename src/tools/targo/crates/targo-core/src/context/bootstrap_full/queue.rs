//! Escrow the existing queue's actual original execution. This does not
//! create a GNU pool or native primary, schedule work, or decode retirement.
use super::*;
use bootstrap::engine::{OriginalBootstrapMemberFailure, RetiredOriginalBootstrapMember};
use jobserver::Acquired;
use trust_resource_controller::bootstrap_graph::compilation::MemberRequest;
use trust_resource_controller::client::Delivery;

struct OriginalImplicit(Arc<BootstrapFull>);
impl Drop for OriginalImplicit {
    fn drop(&mut self) {
        self.0.implicit_borrowed.store(false, Ordering::Release);
    }
}
enum OriginalCredit {
    Implicit { _original: OriginalImplicit },
    Supplementary { _original: Acquired },
}

/// Actual queue credit remains held after attachment, target exit, EOF and
/// failed observation. The existing execution-loan guard aborts unresolved
/// unwinding BEFORE the real GNU guard or implicit borrower can be dropped.
pub(crate) struct QueuePermit {
    delivery: crate::resource_v3::ExecutionLoan,
    credit: Option<OriginalCredit>,
    owner: Arc<BootstrapFull>,
    request: Option<MemberRequest>,
}
impl BootstrapFull {
    /// Restriction-only borrow of the SAME actual original Root implicit
    /// execution. All nested library queues share this one owner and gate.
    pub(crate) fn try_implicit(self: &Arc<Self>) -> io::Result<Option<QueuePermit>> {
        self.check_current()?;
        if self
            .implicit_borrowed
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Ok(None);
        }
        Ok(Some(QueuePermit::new(
            Arc::clone(self),
            OriginalCredit::Implicit {
                _original: OriginalImplicit(Arc::clone(self)),
            },
        )))
    }
    /// Consume a REAL acquired guard from the SAME original GNU client. The
    /// ordinary JobQueue performed this acquisition, not the Host/member API.
    pub(crate) fn supplementary(self: &Arc<Self>, credit: Acquired) -> io::Result<QueuePermit> {
        self.check_current()?;
        if !credit.belongs_to(self.scheduler.client()) {
            return Err(io::Error::other(
                "Full queue credit has a different original GNU owner",
            ));
        }
        Ok(QueuePermit::new(
            Arc::clone(self),
            OriginalCredit::Supplementary { _original: credit },
        ))
    }
}
impl QueuePermit {
    fn new(owner: Arc<BootstrapFull>, credit: OriginalCredit) -> Self {
        Self {
            delivery: crate::resource_v3::ExecutionLoan::new(),
            credit: Some(credit),
            owner,
            request: None,
        }
    }
    pub(crate) fn owner(&self) -> &Arc<BootstrapFull> {
        &self.owner
    }
    /// Arm before the actual direct native member call, including any unwind.
    pub(crate) fn begin_delivery(&mut self, request: &MemberRequest) -> io::Result<()> {
        self.owner.check_current()?;
        request.validate()?;
        if self.credit.is_none()
            || self.request.is_some()
            || request.key != self.owner.owner.data().key
            || request.gnu != self.owner.owner.data().gnu
            || request.fixed_units != 1
        {
            return Err(io::Error::other(
                "Full queued execution is already used or foreign",
            ));
        }
        self.request = Some(request.clone());
        self.delivery.begin_delivery();
        Ok(())
    }
    pub(crate) fn retired(&mut self, retired: &RetiredOriginalBootstrapMember) -> io::Result<()> {
        if self.credit.is_none()
            || !retired.belongs_to(&self.owner.owner)
            || self.request.as_ref() != Some(retired.native_retirement().request())
        {
            return Err(io::Error::other(
                "native retirement does not match this actual queue offer",
            ));
        }
        // Native closure settles execution even if a later source/artifact
        // bookend fails. No status/observation is converted to this witness.
        self.settle();
        Ok(())
    }
    pub(crate) fn failed(&mut self, failure: &OriginalBootstrapMemberFailure) -> io::Result<()> {
        if self.credit.is_none() {
            return Err(io::Error::other("Full queued execution is already settled"));
        }
        let request = self
            .request
            .as_ref()
            .ok_or_else(|| io::Error::other("Full queued execution was never offered"))?;
        if !failure.belongs_to(&self.owner.owner, request) {
            return Err(io::Error::other(
                "member failure belongs to another actual queue offer",
            ));
        }
        if failure.delivery() == Delivery::BeforeRequest
            || failure
                .native_retirement()
                .is_some_and(|retired| retired.request() == request)
        {
            self.settle();
            Ok(())
        } else {
            Err(io::Error::other(
                "Full execution has no actual native owning retirement",
            ))
        }
    }
    fn settle(&mut self) {
        self.delivery.settle();
        drop(self.credit.take());
    }
}
