//! A finite prepaid helper allowance, never a serialized compiler SessionOwner.
//! Only an authenticated trusted bootstrap channel may deliver these bytes.
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_process_isolation::{Binding, Budget, Charge, Limits, Phase, Session, SessionOwner};

use super::{charge, check, contract};
use crate::{Error, system};

pub(super) const WIRE: usize = 112;
const STARTUP: u64 = 64 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(super) enum Role {
    Worker = 0,
    Broker = 1,
}
pub(super) struct Grant {
    bytes: [u8; WIRE],
    owner: SessionOwner,
    budget: Budget,
    binding: Binding,
}
pub(super) struct LocalGrant {
    pub budget: Budget,
    pub capsule: [u8; 32],
    context: [u8; 32],
}

pub(super) fn context(binding: &Binding) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"trust-native-invocation-context-v1\0");
    h.update(binding.version.to_le_bytes());
    h.update(binding.invocation.to_le_bytes());
    for value in [
        binding.compiler,
        binding.worker,
        binding.artifact,
        binding.metadata,
        binding.unit,
        binding.input_closure,
        binding.host_abi,
    ] {
        h.update(value);
    }
    h.finalize().into()
}

impl Grant {
    /// Debit the entire local allowance before either owned child launches.
    /// STARTUP pays fixed trusted runtime/bootstrap bookkeeping before a local
    /// Budget exists. This is logical admission, not an allocator/RSS claim.
    pub fn reserve(session: &Session, role: Role, limits: Limits) -> Result<Self, Error> {
        let result = Self::reserve_inner(session, role, limits);
        if result.is_err() {
            session.budget().refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    fn reserve_inner(session: &Session, role: Role, limits: Limits) -> Result<Self, Error> {
        let b = session.budget();
        check(b)?;
        if session.phase() != Phase::AwaitReady
            || limits.frame_bytes == 0
            || limits.wire_bytes == 0
            || limits.allocation_bytes == 0
            || limits.values == 0
            || limits.work == 0
            || limits.calls == 0
            || limits.live_handles == 0
            || !(1..=128).contains(&limits.depth)
        {
            return Err(contract(b, "native delegated allowance profile/phase"));
        }
        let add = |n: u64, extra| {
            n.checked_add(extra).ok_or_else(|| contract(b, "native allowance overflow"))
        };
        charge(
            b,
            Charge {
                wire_bytes: add(limits.wire_bytes, WIRE as u64)?,
                allocation_bytes: add(limits.allocation_bytes, STARTUP)?,
                values: limits.values,
                work: add(limits.work, 4096)?,
                calls: limits.calls,
            },
        )?;
        // Clock first, then remaining Instant duration: setup latency makes
        // this endpoint earlier, never later than the original endpoint.
        let now = monotonic()?;
        let left = b
            .deadline()
            .checked_duration_since(Instant::now())
            .ok_or_else(|| Error::Budget(b.refuse(trust_process_isolation::Error::Deadline)))?;
        let left =
            u64::try_from(left.as_nanos()).map_err(|_| contract(b, "native allowance duration"))?;
        let endpoint = add(now, left)?;
        let mut bytes = [0; WIRE];
        bytes[..8].copy_from_slice(b"NGRANTv1");
        bytes[8] = role as u8;
        bytes[16..48].copy_from_slice(&context(session.binding()));
        bytes[48..56].copy_from_slice(&endpoint.to_le_bytes());
        bytes[56..60].copy_from_slice(&limits.frame_bytes.to_le_bytes());
        for (at, n) in
            [limits.wire_bytes, limits.allocation_bytes, limits.values, limits.work, limits.calls]
                .into_iter()
                .enumerate()
        {
            bytes[60 + 8 * at..68 + 8 * at].copy_from_slice(&n.to_le_bytes());
        }
        bytes[100..104].copy_from_slice(&limits.live_handles.to_le_bytes());
        bytes[104..106].copy_from_slice(&limits.depth.to_le_bytes());
        check(b)?;
        Ok(Self {
            bytes,
            owner: session.owner(),
            budget: b.clone(),
            binding: session.binding().clone(),
        })
    }
    pub fn wire(&self, session: &Session) -> Result<&[u8; WIRE], Error> {
        check(&self.budget)?;
        if !self.owner.matches(session)
            || !self.budget.shares_owner(session.budget())
            || session.binding() != &self.binding
            || session.phase() != Phase::AwaitReady
        {
            return Err(contract(&self.budget, "native allowance original session"));
        }
        Ok(&self.bytes)
    }
    pub fn capsule(&self) -> [u8; 32] {
        Sha256::digest(self.bytes).into()
    }
}

impl LocalGrant {
    /// Called only in the fresh pinned helper after authenticating its parent.
    /// The local meter enforces a prepaid suballowance; it neither shares nor
    /// reconstructs the compiler's in-process accounting/SessionOwner.
    pub fn adopt(bytes: &[u8], role: Role) -> Result<Self, Error> {
        if bytes.len() != WIRE
            || &bytes[..8] != b"NGRANTv1"
            || bytes[8] != role as u8
            || bytes[9..16] != [0; 7]
            || bytes[106..] != [0; 6]
        {
            return Err(Error::Contract("native allowance wire role/version/length"));
        }
        let n64 = |at| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap());
        let n32 = |at| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
        let limits = Limits {
            frame_bytes: n32(56),
            wire_bytes: n64(60),
            allocation_bytes: n64(68),
            values: n64(76),
            work: n64(84),
            calls: n64(92),
            live_handles: n32(100),
            depth: u16::from_le_bytes(bytes[104..106].try_into().unwrap()),
        };
        // Instant first, then kernel clock: adoption latency shortens the
        // allowance. Delayed delivery cannot renew the absolute endpoint.
        let instant = Instant::now();
        let now = monotonic()?;
        let left = n64(48)
            .checked_sub(now)
            .filter(|left| *left != 0)
            .ok_or(Error::Budget(trust_process_isolation::Error::Deadline))?;
        let deadline = instant
            .checked_add(Duration::from_nanos(left))
            .ok_or(Error::Contract("native allowance endpoint"))?;
        let budget = Budget::new(limits, deadline).map_err(Error::Budget)?;
        let context = bytes[16..48].try_into().unwrap();
        if context == [0; 32] {
            return Err(contract(&budget, "native allowance context"));
        }
        Ok(Self { budget, capsule: Sha256::digest(bytes).into(), context })
    }
    pub fn bind(&self, binding: &Binding) -> Result<(), Error> {
        check(&self.budget)?;
        binding.validate().map_err(|error| Error::Budget(self.budget.refuse(error)))?;
        charge(&self.budget, Charge { work: 1024, ..Charge::default() })?;
        if self.context != context(binding) {
            return Err(contract(&self.budget, "native allowance binding context"));
        }
        check(&self.budget)
    }
}

fn monotonic() -> Result<u64, Error> {
    let mut value = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    // SAFETY: exact writable timespec for a scalar monotonic clock query.
    if unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut value) } != 0 {
        return Err(system("native allowance clock"));
    }
    if value.tv_sec < 0 || !(0..1_000_000_000).contains(&value.tv_nsec) {
        return Err(Error::Contract("native allowance clock representation"));
    }
    (value.tv_sec as u64)
        .checked_mul(1_000_000_000)
        .and_then(|n| n.checked_add(value.tv_nsec as u64))
        .ok_or(Error::Contract("native allowance clock overflow"))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn session() -> Session {
        Session::new(
            Binding {
                version: 1,
                invocation: 1,
                compiler: [1; 32],
                worker: [2; 32],
                artifact: [3; 32],
                metadata: [4; 32],
                unit: [5; 32],
                input_closure: [6; 32],
                host_abi: [7; 32],
            },
            super::super::tests::budget(),
        )
        .unwrap()
    }
    fn limits() -> Limits {
        Limits {
            frame_bytes: 1024,
            wire_bytes: 4096,
            allocation_bytes: 4096,
            values: 32,
            work: 8192,
            calls: 8,
            live_handles: 2,
            depth: 8,
        }
    }
    #[test]
    fn delegated_meter_is_prepaid_local_and_keeps_the_original_endpoint() {
        let session = session();
        let before = session.budget().usage().unwrap();
        let grant = Grant::reserve(&session, Role::Broker, limits()).unwrap();
        let after = session.budget().usage().unwrap();
        assert_eq!(after.work - before.work, limits().work + 4096);
        assert_eq!(
            after.allocation_bytes - before.allocation_bytes,
            limits().allocation_bytes + STARTUP
        );
        let local = LocalGrant::adopt(grant.wire(&session).unwrap(), Role::Broker).unwrap();
        local.bind(session.binding()).unwrap();
        assert_eq!(local.capsule, grant.capsule());
        assert!(!local.budget.shares_owner(session.budget()));
        assert!(local.budget.deadline() <= session.budget().deadline());
        std::thread::sleep(Duration::from_millis(10));
        let delayed = LocalGrant::adopt(grant.wire(&session).unwrap(), Role::Broker).unwrap();
        assert!(delayed.budget.deadline() <= session.budget().deadline());
        assert!(
            delayed.budget.deadline().saturating_duration_since(Instant::now())
                < Duration::from_secs(30)
        );
    }
    #[test]
    fn allowance_cannot_move_to_an_equal_reconstructed_session() {
        let session = session();
        let grant = Grant::reserve(&session, Role::Worker, limits()).unwrap();
        let other = Session::new(session.binding().clone(), session.budget().clone()).unwrap();
        assert!(grant.wire(&other).is_err());
        assert!(session.budget().check().is_err());
    }
    #[test]
    fn malformed_role_context_reserved_bytes_and_expired_endpoint_refuse() {
        let session = session();
        let grant = Grant::reserve(&session, Role::Broker, limits()).unwrap();
        let wire = *grant.wire(&session).unwrap();
        assert!(LocalGrant::adopt(&wire[..WIRE - 1], Role::Broker).is_err());
        assert!(LocalGrant::adopt(&wire, Role::Worker).is_err());
        let mut reserved = wire;
        reserved[111] = 1;
        assert!(LocalGrant::adopt(&reserved, Role::Broker).is_err());
        let mut context = wire;
        context[16] ^= 1;
        let local = LocalGrant::adopt(&context, Role::Broker).unwrap();
        assert!(local.bind(session.binding()).is_err());
        assert!(local.budget.check().is_err());
        let mut expired = wire;
        expired[48..56].fill(0);
        assert!(matches!(
            LocalGrant::adopt(&expired, Role::Broker),
            Err(Error::Budget(trust_process_isolation::Error::Deadline))
        ));
    }
    #[test]
    fn one_short_parent_allowance_refuses_before_delegation_and_cannot_retry() {
        let session = session();
        let b = session.budget();
        let current = b.usage().unwrap();
        b.charge(Charge {
            allocation_bytes: b.limits().allocation_bytes
                - current.allocation_bytes
                - STARTUP
                - limits().allocation_bytes
                + 1,
            ..Charge::default()
        })
        .unwrap();
        let before = b.usage().unwrap();
        assert!(Grant::reserve(&session, Role::Broker, limits()).is_err());
        assert_eq!(b.usage().unwrap(), before);
        assert!(Grant::reserve(&session, Role::Broker, limits()).is_err());
    }
}
