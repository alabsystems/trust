use crate::{Budget, Charge, Error};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum HandleKind {
    Stream = 1,
    Span = 2,
}

/// Public wire identity is checked against a compiler-owned table before use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Handle {
    pub invocation: u64,
    pub kind: HandleKind,
    pub slot: u32,
    pub generation: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseMode {
    Borrow,
    Consume,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HandleUse {
    pub handle: Handle,
    pub mode: UseMode,
}

#[derive(Debug)]
struct Slot<T> {
    generation: u32,
    kind: HandleKind,
    value: Option<T>,
}

/// Invocation-local authority. No table survives terminal cleanup.
#[derive(Debug)]
pub struct HandleTable<T> {
    invocation: u64,
    slots: Vec<Slot<T>>,
    /// Every slot below this index is occupied or retired, so the search for a
    /// reusable slot starts here and still finds the lowest one. Without it an
    /// expansion that only adds handles scans all of them for each new one.
    first_reusable: usize,
    live: u32,
    budget: Budget,
    closed: bool,
}

impl<T> HandleTable<T> {
    pub fn new(invocation: u64, budget: Budget) -> Result<Self, Error> {
        if invocation == 0 {
            return Err(Error::Handle("zero invocation"));
        }
        budget.check()?;
        let count = usize::try_from(budget.limits().live_handles)
            .map_err(|_| budget.refuse(Error::Overflow))?;
        budget.allocation::<Slot<T>>(count)?;
        let mut slots = Vec::new();
        slots.try_reserve_exact(count).map_err(|_| budget.refuse(Error::Allocation))?;
        budget.allocation::<Slot<T>>(slots.capacity().saturating_sub(count))?;
        budget.check()?;
        Ok(Self { invocation, slots, first_reusable: 0, live: 0, budget, closed: false })
    }

    pub fn insert(&mut self, kind: HandleKind, value: T) -> Result<Handle, Error> {
        self.budget.check()?;
        if self.closed {
            return Err(Error::Phase);
        }
        if self.live >= self.budget.limits().live_handles {
            return Err(self.budget.refuse(Error::Budget("live handles")));
        }
        self.budget.charge(Charge {
            work: u64::try_from(self.slots.len())
                .map_err(|_| Error::Overflow)?
                .checked_add(1)
                .ok_or(Error::Overflow)?,
            ..Charge::default()
        })?;
        // Retire exhausted generations permanently; never wrap an old identity.
        let reusable = self.slots[self.first_reusable..]
            .iter()
            .position(|s| s.value.is_none() && s.generation < u32::MAX)
            .map(|offset| self.first_reusable + offset);
        let index = if let Some(index) = reusable {
            self.budget.acquire_handle()?;
            let slot = &mut self.slots[index];
            slot.generation += 1;
            slot.kind = kind;
            slot.value = Some(value);
            index
        } else {
            if self.slots.len() >= self.budget.limits().live_handles as usize {
                return Err(self.budget.refuse(Error::Budget("handle slots")));
            }
            // Complete slot capacity is priced and reserved at construction.
            self.budget.acquire_handle()?;
            self.slots.push(Slot { generation: 1, kind, value: Some(value) });
            self.slots.len() - 1
        };
        // The slots from the old mark up to `index` were searched and are not
        // reusable; `index` itself is now occupied.
        self.first_reusable = index + 1;
        self.live += 1;
        Ok(Handle {
            invocation: self.invocation,
            kind,
            slot: u32::try_from(index).map_err(|_| Error::Overflow)?,
            generation: self.slots[index].generation,
        })
    }

    pub fn get(&self, handle: Handle) -> Result<&T, Error> {
        self.budget.check()?;
        self.slot(handle)?.value.as_ref().ok_or(Error::Handle("consumed"))
    }

    /// Find an existing live value without creating an aliasing owner or
    /// changing its generation. Callers may intern immutable borrowed values;
    /// consuming values retain the same transaction checks as all other handles.
    pub fn find(
        &self,
        kind: HandleKind,
        mut matches: impl FnMut(&T) -> bool,
    ) -> Result<Option<Handle>, Error> {
        self.budget.check()?;
        if self.closed {
            return Err(Error::Phase);
        }
        self.budget.charge(Charge {
            work: u64::try_from(self.slots.len())
                .map_err(|_| self.budget.refuse(Error::Overflow))?,
            ..Charge::default()
        })?;
        for (index, slot) in self.slots.iter().enumerate() {
            if slot.kind == kind {
                if let Some(value) = &slot.value {
                    if matches(value) {
                        return Ok(Some(Handle {
                            invocation: self.invocation,
                            kind,
                            slot: u32::try_from(index)
                                .map_err(|_| self.budget.refuse(Error::Overflow))?,
                            generation: slot.generation,
                        }));
                    }
                }
            }
        }
        Ok(None)
    }

    fn slot(&self, handle: Handle) -> Result<&Slot<T>, Error> {
        if self.closed {
            return Err(Error::Phase);
        }
        if handle.invocation != self.invocation || handle.invocation == 0 {
            return Err(Error::Handle("invocation"));
        }
        let slot = self.slots.get(handle.slot as usize).ok_or(Error::Handle("slot"))?;
        if handle.generation == 0 || slot.generation != handle.generation {
            return Err(Error::Handle("generation"));
        }
        if slot.kind != handle.kind {
            return Err(Error::Handle("kind"));
        }
        if slot.value.is_none() {
            return Err(Error::Handle("consumed"));
        }
        Ok(slot)
    }

    /// Validate the complete argument set before taking any value. Repeated
    /// borrowing is fine; consuming aliases, including borrow+consume, refuse.
    pub fn consume(&mut self, uses: &[HandleUse]) -> Result<Vec<T>, Error> {
        self.budget.check()?;
        if self.closed {
            return Err(Error::Phase);
        }
        let work = uses
            .len()
            .checked_mul(uses.len())
            .ok_or_else(|| self.budget.refuse(Error::Overflow))?;
        self.budget.charge(Charge {
            work: u64::try_from(work).map_err(|_| self.budget.refuse(Error::Overflow))?,
            ..Charge::default()
        })?;
        for (i, usage) in uses.iter().enumerate() {
            self.slot(usage.handle)?;
            if usage.mode == UseMode::Consume && usage.handle.kind != HandleKind::Stream {
                return Err(Error::Handle("span consumption"));
            }
            for other in &uses[..i] {
                if other.handle == usage.handle
                    && (other.mode == UseMode::Consume || usage.mode == UseMode::Consume)
                {
                    return Err(Error::Handle("duplicate consumption"));
                }
            }
        }
        let count = uses.iter().filter(|u| u.mode == UseMode::Consume).count();
        self.budget.allocation::<T>(count)?;
        let mut result = Vec::new();
        result.try_reserve_exact(count).map_err(|_| self.budget.refuse(Error::Allocation))?;
        self.budget.allocation::<T>(result.capacity().saturating_sub(count))?;
        self.budget.check()?;
        self.budget.release_handles(
            u32::try_from(count).map_err(|_| self.budget.refuse(Error::Overflow))?,
        )?;
        for usage in uses {
            if usage.mode == UseMode::Consume {
                let index = usage.handle.slot as usize;
                let value = self.slots[index].value.take().ok_or(Error::Handle("consumed"))?;
                self.first_reusable = self.first_reusable.min(index);
                result.push(value);
                self.live -= 1;
            }
        }
        Ok(result)
    }

    pub fn clear(&mut self) {
        let _ = self.budget.release_handles(self.live);
        self.slots.clear();
        self.first_reusable = 0;
        self.live = 0;
        self.closed = true;
    }
    pub fn live(&self) -> u32 {
        self.live
    }
}

impl<T> Drop for HandleTable<T> {
    fn drop(&mut self) {
        let _ = self.budget.release_handles(self.live);
    }
}
