//! Cooperative SDK worker requests. Bytes are binding data only; granted
//! workers additionally receive an original description from the sole bank.
use std::io;

use super::{MAX_CPU_SET, MemberOriginalRequest};
use crate::wire::{Encoder, header, invalid};
use crate::{ContextReply, Cpu, FileIdentity, Subject};

pub const PURPOSE: &str = "native-workload-worker-v1";
pub const RETURN_PURPOSE: &str = "native-workload-worker-return-v1";

#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub original: MemberOriginalRequest,
    pub worker_request: [u8; 16],
}
impl Request {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.worker_request == [0; 16] {
            return Err(invalid());
        }
        let mut e = Encoder::new(50);
        e.number(3);
        e.frame_bytes(&self.original.encode()?)?;
        e.0.extend(self.worker_request);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 50)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let value = Self {
            original: MemberOriginalRequest::decode(&d.frame_bytes()?)?,
            worker_request: d.array()?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.encode()?;
        hello(&self.original, PURPOSE)
    }
}
fn hello(original: &MemberOriginalRequest, purpose: &str) -> io::Result<Vec<u8>> {
    let attempt: String =
        original.query.binding.root_attempt.iter().map(|byte| format!("{byte:02x}")).collect();
    Ok(format!(
        "{{\"version\":3,\"role\":\"{purpose}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
        original.query.binding.session
    )
    .into_bytes())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Granted { loan: [u8; 16], slot: u32, backing: FileIdentity },
    Busy,
    Refused { reason: String },
}
#[derive(Clone, PartialEq, Eq)]
pub struct Reply {
    pub context: ContextReply,
    pub worker_request: [u8; 16],
    pub decision: Decision,
}
fn context(context: &ContextReply, member: Option<[u8; 16]>) -> io::Result<()> {
    if !matches!(context.context.cpu, Cpu::CooperativeShared { .. })
        || context.context.sdk.is_none()
        || !matches!(context.context.subject,Subject::RegisteredMember{attempt,..} if member.is_none_or(|member|member==attempt))
    {
        return Err(invalid());
    }
    Ok(())
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        context(&self.context, None)?;
        if self.worker_request == [0; 16] {
            return Err(invalid());
        }
        let mut e = Encoder::new(49);
        e.number(3);
        e.frame_bytes(&self.context.encode()?)?;
        e.0.extend(self.worker_request);
        match &self.decision {
            Decision::Granted { loan, slot, backing } => {
                if *loan == [0; 16] || *slot >= MAX_CPU_SET as u32 || backing.inode == 0 {
                    return Err(invalid());
                }
                e.number(0);
                e.0.extend(loan);
                e.number((*slot).into());
                e.number(backing.device);
                e.number(backing.inode);
            }
            Decision::Busy => e.number(1),
            Decision::Refused { reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(2);
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 49)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let reply = ContextReply::decode(&d.frame_bytes()?, &request.original.query)?;
        let worker_request = d.array()?;
        let decision = match d.number()? {
            0 => Decision::Granted {
                loan: d.array()?,
                slot: d.narrow()?,
                backing: FileIdentity { device: d.number()?, inode: d.number()? },
            },
            1 => Decision::Busy,
            2 => {
                Decision::Refused { reason: String::from_utf8(d.bytes()?).map_err(|_| invalid())? }
            }
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { context: reply, worker_request, decision };
        value.encode()?;
        context(&value.context, Some(request.original.member_attempt))?;
        if value.worker_request != request.worker_request {
            return Err(invalid());
        }
        Ok(value)
    }
}
#[derive(Clone, PartialEq, Eq)]
pub enum Settlement {
    UnusedOfferCancelled,
    SdkQuiescent,
}
impl Settlement {
    fn number(&self) -> u64 {
        match self {
            Self::UnusedOfferCancelled => 0,
            Self::SdkQuiescent => 1,
        }
    }
    fn decode(number: u64) -> io::Result<Self> {
        match number {
            0 => Ok(Self::UnusedOfferCancelled),
            1 => Ok(Self::SdkQuiescent),
            _ => Err(invalid()),
        }
    }
}
#[derive(Clone, PartialEq, Eq)]
pub struct Return {
    pub request: Request,
    pub loan: [u8; 16],
    pub slot: u32,
    pub settlement: Settlement,
}
impl Return {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.loan == [0; 16] || self.slot >= MAX_CPU_SET as u32 {
            return Err(invalid());
        }
        let mut e = Encoder::new(50);
        e.number(4);
        e.frame_bytes(&self.request.encode()?)?;
        e.0.extend(self.loan);
        e.number(self.slot.into());
        e.number(self.settlement.number());
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 50)?;
        if d.number()? != 4 {
            return Err(invalid());
        }
        let value = Self {
            request: Request::decode(&d.frame_bytes()?)?,
            loan: d.array()?,
            slot: d.narrow()?,
            settlement: Settlement::decode(d.number()?)?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.encode()?;
        hello(&self.request.original, RETURN_PURPOSE)
    }
}
/// The ACK confirms the same loan's SDK settlement, never process exit or CPU
/// accounting. Actual member outcome still requires its original owning wait.
#[derive(Clone, PartialEq, Eq)]
pub struct Returned {
    pub context: ContextReply,
    pub worker_request: [u8; 16],
    pub loan: [u8; 16],
    pub slot: u32,
    pub settlement: Settlement,
}
impl Returned {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        context(&self.context, None)?;
        if self.worker_request == [0; 16] || self.loan == [0; 16] || self.slot >= MAX_CPU_SET as u32
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(49);
        e.number(4);
        e.frame_bytes(&self.context.encode()?)?;
        e.0.extend(self.worker_request);
        e.0.extend(self.loan);
        e.number(self.slot.into());
        e.number(self.settlement.number());
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Return) -> io::Result<Self> {
        let mut d = header(bytes, 49)?;
        if d.number()? != 4 {
            return Err(invalid());
        }
        let value = Self {
            context: ContextReply::decode(&d.frame_bytes()?, &request.request.original.query)?,
            worker_request: d.array()?,
            loan: d.array()?,
            slot: d.narrow()?,
            settlement: Settlement::decode(d.number()?)?,
        };
        d.done()?;
        value.encode()?;
        context(&value.context, Some(request.request.original.member_attempt))?;
        if value.worker_request != request.request.worker_request
            || value.loan != request.loan
            || value.slot != request.slot
            || value.settlement != request.settlement
        {
            return Err(invalid());
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cooperative_worker_return_cannot_reenter_query_original_or_broker_request() {
        let query = super::super::tests::query();
        let request = Request {
            original: MemberOriginalRequest {
                query: crate::ContextQuery { binding: query.member.binding, call_attempt: [9; 16] },
                member_attempt: [3; 16],
            },
            worker_request: [4; 16],
        };
        let encoded = request.encode().unwrap();
        assert!(Request::decode(&encoded).unwrap() == request);
        assert!(MemberOriginalRequest::decode(&encoded).is_err());
        assert!(super::super::CompilerQuery::decode(&encoded).is_err());
        let returned =
            Return { request, loan: [5; 16], slot: 1, settlement: Settlement::SdkQuiescent };
        let bytes = returned.encode().unwrap();
        assert!(Return::decode(&bytes).unwrap() == returned);
        assert!(Request::decode(&bytes).is_err());
        assert!(super::super::bank::Request::decode(&bytes).is_err());
        for count in 0..bytes.len() {
            assert!(Return::decode(&bytes[..count]).is_err());
        }
    }
}
