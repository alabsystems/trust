//! One authenticated original-host retention transfer, never an execution grant.
use std::io;
use std::os::fd::BorrowedFd;
use std::sync::Arc;
use std::time::Instant;

use trust_resource_provenance::{Host, PinnedHelper};

use super::{CallError, Client, Delivery, before};
use crate::runtime_input_retention::{Reply, Request, SupportQuery, SupportReply, transport};
use crate::{Channel, ContextReply, Subject};

/// Support DATA only. It neither reserves future retention nor keeps a costly
/// Step waiting on an old socket. Later transfer authenticates a NEW connection.
pub struct RuntimeInputSupport {
    reply: ContextReply,
}
impl RuntimeInputSupport {
    pub fn observation(&self) -> &ContextReply {
        &self.reply
    }
}

/// Retains the original connected Host/channel after positive custody observation.
/// It is not a completion, SDK, withholding/release capability or launch owner.
/// Dropping this value sends no release and cannot dispose Host-retained inputs.
pub struct RetainedRuntimeInputs {
    request: Request,
    context: ContextReply,
    _channel: Channel,
    original: Host,
    pin: Arc<PinnedHelper>,
}
impl RetainedRuntimeInputs {
    pub fn request(&self) -> &Request {
        &self.request
    }
    pub fn observation(&self) -> &ContextReply {
        &self.context
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        finish_observation(deadline, || {
            self.pin.validate(deadline)?;
            self.original.revalidate(deadline)?;
            live(&self.context)
        })
    }
}
// Every public positive samples the ORIGINAL deadline after its last native
// observation, ACK or owner construction. Earlier per-I/O checks do not cover
// late final fstat/process observations. This never renews the caller's budget.
fn finish_observation<T>(
    deadline: Instant,
    observe: impl FnOnce() -> io::Result<T>,
) -> io::Result<T> {
    if Instant::now() >= deadline {
        return Err(io::ErrorKind::TimedOut.into());
    }
    let value = observe()?;
    if Instant::now() >= deadline {
        return Err(io::ErrorKind::TimedOut.into());
    }
    Ok(value)
}
fn live(reply: &ContextReply) -> io::Result<()> {
    let member = match reply.context.subject {
        Subject::Root { .. } => None,
        Subject::RegisteredMember { attempt, .. } => Some(attempt),
    };
    super::workload::live_context(&reply.context, member)
}
impl Client {
    /// Observe actual current-root membership and protocol support BEFORE Steps.
    /// Missing old Host support refuses; no generic context or account fallback.
    pub fn runtime_input_support(
        &self,
        query: &SupportQuery,
        deadline: Instant,
    ) -> Result<RuntimeInputSupport, CallError> {
        let payload = query.encode().map_err(before)?;
        let hello = query.hello().map_err(before)?;
        let original = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(before)?).map_err(before)?;
        // From the first hello byte onward, failed delivery is never replayed.
        let result = finish_observation(deadline, || {
            original.revalidate(deadline)?;
            channel.send(&hello, deadline)?;
            channel.send(&payload, deadline)?;
            let reply = SupportReply::decode(&channel.receive(deadline)?, query)?;
            transport::require_reply_eof(&mut channel, deadline)?;
            original.revalidate(deadline)?;
            match reply {
                SupportReply::Supported { context } => {
                    live(&context)?;
                    channel.send(&[1], deadline)?;
                    Ok(RuntimeInputSupport { reply: *context })
                }
                SupportReply::Refused { reason, .. } => {
                    Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
                }
            }
        });
        result.map_err(|error| CallError { delivery: Delivery::Unknown, error })
    }
    /// Send the COMPLETE borrowed original runtime/output census exactly once.
    /// Caller must retain the actual producer/runtime/output owners; these bytes
    /// do not prove Steps completed and cannot replace durable manager custody.
    pub fn retain_runtime_inputs(
        &self,
        request: &Request,
        descriptions: &[BorrowedFd<'_>],
        deadline: Instant,
    ) -> Result<RetainedRuntimeInputs, CallError> {
        let payload = request.encode().map_err(before)?;
        let hello = request.hello().map_err(before)?;
        transport::check_inputs(request, descriptions).map_err(before)?;
        let original = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(before)?).map_err(before)?;
        let result = finish_observation(deadline, || {
            original.revalidate(deadline)?;
            channel.send(&hello, deadline)?;
            channel.send(&payload, deadline)?;
            let accepted = match Reply::decode(&channel.receive(deadline)?, request)? {
                Reply::Accepted { context, .. } => context,
                Reply::Refused { reason, .. } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                _ => return Err(crate::wire::invalid()),
            };
            original.revalidate(deadline)?;
            live(&accepted)?;
            transport::send_inputs(&mut channel, request, descriptions, deadline, || {
                original.revalidate(deadline)?;
                live(&accepted)
            })?;
            let retained = match Reply::decode(&channel.receive(deadline)?, request)? {
                Reply::Retained { context, .. } if context == accepted => context,
                _ => return Err(crate::wire::invalid()),
            };
            transport::require_reply_eof(&mut channel, deadline)?;
            original.revalidate(deadline)?;
            live(&retained)?;
            transport::check_inputs(request, descriptions)?;
            Ok(retained)
        });
        match result {
            Ok(context) => finish_observation(deadline, || {
                Ok(RetainedRuntimeInputs {
                    request: request.clone(),
                    context,
                    _channel: channel,
                    original,
                    pin: Arc::clone(&self.host),
                })
            })
            .map_err(|error| CallError { delivery: Delivery::Unknown, error }),
            Err(error) => Err(CallError { delivery: Delivery::Unknown, error }),
        }
    }
}

#[cfg(test)]
mod tests;
