use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::Error;

/// Explicit caller-selected limits. These are admission limits, not RSS claims.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    pub frame_bytes: u32,
    pub wire_bytes: u64,
    pub allocation_bytes: u64,
    pub values: u64,
    pub work: u64,
    pub calls: u64,
    pub live_handles: u32,
    pub depth: u16,
}

#[cfg(test)]
mod tests {
    use super::*;
    fn limits() -> Limits {
        Limits {
            frame_bytes: 1024,
            wire_bytes: 4096,
            allocation_bytes: 4096,
            values: 100,
            work: 100,
            calls: 10,
            live_handles: 2,
            depth: 8,
        }
    }
    #[test]
    fn poison_is_sticky_and_cleanup_still_releases() {
        let b = Budget::new(limits(), Instant::now() + std::time::Duration::from_secs(30)).unwrap();
        b.acquire_handle().unwrap();
        let result = std::panic::catch_unwind(|| {
            let _guard = b.usage.lock().unwrap();
            panic!("poison fixture");
        });
        assert!(result.is_err());
        assert_eq!(b.clone().charge(Charge::default()), Err(Error::Poisoned));
        b.release_handles(1).unwrap();
        assert_eq!(b.check(), Err(Error::Poisoned));
    }
    #[test]
    fn expired_owner_latches_the_shared_deadline() {
        let mut b =
            Budget::new(limits(), Instant::now() + std::time::Duration::from_secs(30)).unwrap();
        let sibling = b.clone();
        b.deadline = Instant::now() - std::time::Duration::from_secs(1);
        assert_eq!(b.check(), Err(Error::Deadline));
        assert_eq!(sibling.charge(Charge::default()), Err(Error::Deadline));
    }
    #[test]
    fn equal_profiles_are_not_shared_owners() {
        let deadline = Instant::now() + std::time::Duration::from_secs(30);
        let b = Budget::new(limits(), deadline).unwrap();
        let clone = b.clone();
        let separate = Budget::new(limits(), deadline).unwrap();
        assert!(b.shares_owner(&clone));
        assert!(!b.shares_owner(&separate));
        clone.cancel();
        assert_eq!(b.check(), Err(Error::Phase));
        assert_eq!(separate.check(), Ok(()));
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Charge {
    pub wire_bytes: u64,
    pub allocation_bytes: u64,
    pub values: u64,
    pub work: u64,
    pub calls: u64,
}

pub type Usage = Charge;

#[derive(Debug, Default)]
struct Accounting {
    usage: Usage,
    live_handles: u32,
    failure: Option<Error>,
}

/// Clones and nested sessions share cumulative counters and one absolute deadline.
#[derive(Debug, Clone)]
pub struct Budget {
    limits: Limits,
    deadline: Instant,
    usage: Arc<Mutex<Accounting>>,
}

impl Budget {
    /// The caller establishes this deadline before launch, never per callback.
    pub fn new(limits: Limits, deadline: Instant) -> Result<Self, Error> {
        if limits.frame_bytes == 0
            || limits.wire_bytes == 0
            || limits.allocation_bytes == 0
            || limits.values == 0
            || limits.work == 0
            || limits.calls == 0
            || limits.live_handles == 0
            || limits.depth == 0
            || limits.depth > 128
        {
            return Err(Error::InvalidLimits);
        }
        let result = Self { limits, deadline, usage: Arc::new(Mutex::new(Accounting::default())) };
        result.check()?;
        Ok(result)
    }

    pub fn limits(&self) -> Limits {
        self.limits
    }
    pub fn deadline(&self) -> Instant {
        self.deadline
    }
    /// True only for clones of this same in-process accounting owner. Equal
    /// numeric limits and deadlines do not establish shared accounting. This
    /// is not a transferable process credential: fork copies the address space.
    pub fn shares_owner(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.usage, &other.usage)
            && self.limits == other.limits
            && self.deadline == other.deadline
    }
    pub fn check(&self) -> Result<(), Error> {
        let mut state = self.state();
        self.check_state(&mut state)
    }
    pub fn depth(&self, depth: u16) -> Result<(), Error> {
        self.check()?;
        if depth > self.limits.depth { Err(self.refuse(Error::Budget("depth"))) } else { Ok(()) }
    }
    pub fn usage(&self) -> Result<Usage, Error> {
        let state = self.state();
        if matches!(state.failure, Some(Error::Poisoned)) {
            return Err(Error::Poisoned);
        }
        Ok(state.usage)
    }

    /// All counters advance together, or none do. Refused allocations never run.
    pub fn charge(&self, delta: Charge) -> Result<(), Error> {
        let mut accounting = self.state();
        self.check_state(&mut accounting)?;
        let current = accounting.usage;
        fn sum(a: u64, b: u64, max: u64, name: &'static str) -> Result<u64, Error> {
            let n = a.checked_add(b).ok_or(Error::Overflow)?;
            if n > max { Err(Error::Budget(name)) } else { Ok(n) }
        }
        let next: Result<Charge, Error> = (|| {
            Ok(Charge {
                wire_bytes: sum(
                    current.wire_bytes,
                    delta.wire_bytes,
                    self.limits.wire_bytes,
                    "wire bytes",
                )?,
                allocation_bytes: sum(
                    current.allocation_bytes,
                    delta.allocation_bytes,
                    self.limits.allocation_bytes,
                    "allocation bytes",
                )?,
                values: sum(current.values, delta.values, self.limits.values, "values")?,
                work: sum(current.work, delta.work, self.limits.work, "work")?,
                calls: sum(current.calls, delta.calls, self.limits.calls, "calls")?,
            })
        })();
        let next = match next {
            Ok(next) => next,
            Err(error) => {
                accounting.failure = Some(error.clone());
                return Err(error);
            }
        };
        accounting.usage = next;
        Ok(())
    }

    pub(crate) fn allocation<T>(&self, count: usize) -> Result<(), Error> {
        let bytes = count
            .checked_mul(std::mem::size_of::<T>())
            .ok_or_else(|| self.refuse(Error::Overflow))?;
        self.charge(Charge {
            allocation_bytes: u64::try_from(bytes).map_err(|_| self.refuse(Error::Overflow))?,
            ..Charge::default()
        })
    }

    pub(crate) fn acquire_handle(&self) -> Result<(), Error> {
        let mut accounting = self.state();
        self.check_state(&mut accounting)?;
        if accounting.live_handles >= self.limits.live_handles {
            let error = Error::Budget("live handles");
            accounting.failure = Some(error.clone());
            return Err(error);
        }
        accounting.live_handles += 1;
        Ok(())
    }
    pub(crate) fn release_handles(&self, count: u32) -> Result<(), Error> {
        let mut accounting = self.state();
        accounting.live_handles =
            accounting.live_handles.checked_sub(count).ok_or(Error::Handle("accounting"))?;
        Ok(())
    }

    fn state(&self) -> std::sync::MutexGuard<'_, Accounting> {
        match self.usage.lock() {
            Ok(state) => state,
            Err(poisoned) => {
                let mut state = poisoned.into_inner();
                state.failure = Some(Error::Poisoned);
                state
            }
        }
    }
    fn check_state(&self, state: &mut Accounting) -> Result<(), Error> {
        if let Some(error) = &state.failure {
            return Err(error.clone());
        }
        if Instant::now() >= self.deadline {
            state.failure = Some(Error::Deadline);
            return Err(Error::Deadline);
        }
        Ok(())
    }
    /// Terminal refusal is shared with every nested owner. Cleanup release is
    /// still permitted, but neither charge nor a new owner can resume execution.
    pub fn refuse(&self, error: Error) -> Error {
        let mut state = self.state();
        state.failure.get_or_insert(error).clone()
    }
    pub fn cancel(&self) {
        self.refuse(Error::Phase);
    }
}
