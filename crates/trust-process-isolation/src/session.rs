use std::sync::Arc;

use crate::{Binding, Budget, Call, Charge, Envelope, Error, Message, Method, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    AwaitReady,
    Active,
    AwaitReply,
    Terminal,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Admission {
    Ready,
    Call(Call),
    Finished(Option<crate::Handle>),
    Failed(String),
}

/// An opaque in-process owner identity. Only Session::new creates one;
/// cloning it preserves identity across moves without using a stack address.
/// It is not a wire credential or sandbox/proof attestation.
#[derive(Debug, Clone)]
pub struct SessionOwner(Arc<()>);

impl SessionOwner {
    pub fn matches(&self, session: &Session) -> bool {
        Arc::ptr_eq(&self.0, &session.owner.0)
    }
}

#[derive(Debug)]
struct PendingCall {
    id: u64,
    method: Method,
    encoded: Vec<u8>,
}

/// Compiler-side conversation state. A readiness echo earns no sandbox or proof
/// authority. Ownership and semantic admission occur separately before callback.
/// Every refused protocol transition aborts the shared invocation budget, including
/// nested sessions. Normal child completion does not abort its parent's budget.
#[derive(Debug)]
pub struct Session {
    binding: Binding,
    budget: Budget,
    phase: Phase,
    next_id: u64,
    pending: Option<PendingCall>,
    owner: SessionOwner,
}
impl Session {
    pub fn new(binding: Binding, budget: Budget) -> Result<Self, Error> {
        binding.validate().map_err(|error| budget.refuse(error))?;
        budget.check()?;
        budget.allocation::<usize>(2)?;
        Ok(Self {
            binding,
            budget,
            phase: Phase::AwaitReady,
            next_id: 1,
            pending: None,
            owner: SessionOwner(Arc::new(())),
        })
    }
    pub fn owner(&self) -> SessionOwner {
        self.owner.clone()
    }
    pub fn phase(&self) -> Phase {
        self.phase
    }
    pub fn binding(&self) -> &Binding {
        &self.binding
    }
    pub fn budget(&self) -> &Budget {
        &self.budget
    }
    pub fn receive(&mut self, envelope: Envelope) -> Result<Admission, Error> {
        match self.receive_inner(envelope) {
            Ok(admission) => Ok(admission),
            Err(error) => {
                self.phase = Phase::Terminal;
                self.pending = None;
                Err(self.budget.refuse(error))
            }
        }
    }
    fn receive_inner(&mut self, envelope: Envelope) -> Result<Admission, Error> {
        self.budget.check()?;
        if envelope.binding != self.binding {
            return Err(Error::Identity);
        }
        match (self.phase, envelope.message) {
            (Phase::AwaitReady, Message::Ready) => {
                self.phase = Phase::Active;
                Ok(Admission::Ready)
            }
            (Phase::Active, Message::Call(call)) => {
                call.validate()?;
                if call.id != self.next_id {
                    return Err(Error::Sequence);
                }
                self.budget.charge(Charge { calls: 1, work: 1, ..Charge::default() })?;
                self.next_id = self.next_id.checked_add(1).ok_or(Error::Sequence)?;
                let encoded = crate::codec::call_snapshot(&call, &self.budget)?;
                self.pending = Some(PendingCall { id: call.id, method: call.method, encoded });
                self.phase = Phase::AwaitReply;
                Ok(Admission::Call(call))
            }
            (Phase::Active, Message::Finish { output }) => {
                if output.is_some_and(|h| {
                    h.invocation != self.binding.invocation
                        || h.kind != crate::HandleKind::Stream
                        || h.generation == 0
                }) {
                    return Err(Error::Handle("finish identity"));
                }
                self.phase = Phase::Terminal;
                Ok(Admission::Finished(output))
            }
            (
                Phase::AwaitReady | Phase::Active | Phase::AwaitReply,
                Message::Failure { reason },
            ) => {
                self.phase = Phase::Terminal;
                self.pending = None;
                Ok(Admission::Failed(reason))
            }
            _ => Err(Error::Phase),
        }
    }
    /// Check the complete call already admitted by `receive`, including every
    /// argument byte and handle field. The internal snapshot/comparison spends
    /// storage and work, but accepts no transition or additional call grant.
    /// A mismatch is terminal before compiler-side effects or handle consumption.
    pub fn validate_pending_call(&mut self, call: &Call) -> Result<(), Error> {
        let result = (|| {
            self.budget.check()?;
            call.validate()?;
            if self.phase != Phase::AwaitReply {
                return Err(Error::Phase);
            }
            let pending = self.pending.as_ref().ok_or(Error::Phase)?;
            if call.id != pending.id {
                return Err(Error::Sequence);
            }
            if call.method != pending.method {
                return Err(Error::Schema);
            }
            let encoded = crate::codec::call_snapshot(call, &self.budget)?;
            self.budget.charge(Charge {
                work: u64::try_from(encoded.len()).map_err(|_| Error::Overflow)?,
                ..Charge::default()
            })?;
            if encoded != pending.encoded {
                return Err(Error::Identity);
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.phase = Phase::Terminal;
            self.pending = None;
            return Err(self.budget.refuse(error));
        }
        Ok(())
    }

    /// Reply must be encoded and delivered by the owned bounded transport. It
    /// creates no handles: an adapter first inserts compiler-issued results.
    pub fn reply(&mut self, id: u64, value: Value) -> Result<Envelope, Error> {
        match self.reply_inner(id, value) {
            Ok(envelope) => Ok(envelope),
            Err(error) => {
                self.phase = Phase::Terminal;
                self.pending = None;
                Err(self.budget.refuse(error))
            }
        }
    }
    fn reply_inner(&mut self, id: u64, value: Value) -> Result<Envelope, Error> {
        self.budget.check()?;
        let pending = self.pending.as_ref().ok_or(Error::Phase)?;
        if self.phase != Phase::AwaitReply {
            return Err(Error::Phase);
        }
        if id != pending.id {
            return Err(Error::Sequence);
        }
        if !pending.method.response().accepts(&value) {
            return Err(Error::Schema);
        }
        self.pending = None;
        self.phase = Phase::Active;
        Ok(Envelope { binding: self.binding.clone(), message: Message::Reply { id, value } })
    }
    pub fn cancel(&mut self) -> Envelope {
        self.budget.cancel();
        self.phase = Phase::Terminal;
        self.pending = None;
        Envelope { binding: self.binding.clone(), message: Message::Cancel }
    }
}
