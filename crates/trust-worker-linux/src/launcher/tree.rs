//! Private cgroup-v2 custody for a fresh, single-thread static worker.
//!
//! The caller still supplies a delegated finite kernel owner and an outer hard
//! deadline. This module creates no grant and authenticates no source or result.
use std::ffi::CStr;
use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd, RawFd};
use std::time::Duration;

use trust_process_isolation::{Budget, Charge};

use super::{checked, contract};
use crate::{Error, system};

mod control;
pub(super) use control::{Access, Control, Identity, Role};

fn scalar(bytes: &[u8]) -> Result<u64, Error> {
    let digits = bytes.strip_suffix(b"\n").ok_or_else(|| contract("tree scalar terminator"))?;
    if digits.is_empty()
        || digits.len() > 20
        || !digits.iter().all(u8::is_ascii_digit)
        || (digits.len() > 1 && digits[0] == b'0')
    {
        return Err(contract("tree scalar grammar"));
    }
    digits.iter().try_fold(0u64, |value, digit| {
        value
            .checked_mul(10)
            .and_then(|v| v.checked_add((*digit - b'0') as u64))
            .ok_or_else(|| contract("tree scalar overflow"))
    })
}

pub(super) fn empty_events(bytes: &[u8]) -> Result<bool, Error> {
    match bytes {
        b"populated 0\nfrozen 0\n" => Ok(true),
        b"populated 1\nfrozen 0\n" => Ok(false),
        _ => Err(contract("tree events grammar or frozen domain")),
    }
}

#[derive(Debug)]
pub(super) struct Tree {
    pub(super) directory: File,
    pub(super) identity: Identity,
    kill: Control,
    events: Control,
    memory: Control,
    swap: Control,
    tasks: Control,
    kind: Control,
    oom: Control,
    memory_bound: u64,
    budget: Budget,
    pub(super) armed: bool,
    closed: bool,
    cleanup_polls: u64,
}
impl Tree {
    /// Create only a new name beneath the caller's delegated finite cgroup2
    /// owner. Existing names refuse. The caller retains namespace removal and
    /// outer hard-preemption custody even after a partial creation error.
    pub(super) fn create(
        parent: &File,
        name: &CStr,
        address_space: u64,
        budget: &Budget,
    ) -> Result<Self, Error> {
        let result = Self::create_inner(parent, name, address_space, budget);
        if result.is_err() {
            budget.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    fn create_inner(
        parent: &File,
        name: &CStr,
        address_space: u64,
        budget: &Budget,
    ) -> Result<Self, Error> {
        checked(budget)?;
        let bytes = name.to_bytes();
        if bytes.is_empty()
            || bytes.len() > 255
            || !bytes.iter().all(|b| b.is_ascii_alphanumeric() || matches!(*b, b'-' | b'_'))
            || address_space == 0
            || address_space == u64::MAX
        {
            return Err(contract("tree creation arguments"));
        }
        let cleanup_polls = cleanup_reservation(budget)?;
        budget
            .charge(Charge {
                allocation_bytes: std::mem::size_of::<Self>() as u64,
                work: 8192,
                calls: 1,
                ..Charge::default()
            })
            .map_err(Error::Budget)?;
        Identity::capture(parent, Role::Directory)?;
        require_domain(parent, budget)?;
        let parent_memory = Control::open(parent, c"memory.max", Access::Read)?.scalar(budget)?;
        let parent_tasks = Control::open(parent, c"pids.max", Access::Read)?.scalar(budget)?;
        if parent_memory == 0 || parent_tasks == 0 {
            return Err(contract("tree parent limits"));
        }
        // A tightening of the existing finite parent/profile, never a grant.
        let memory_bound = address_space.min(parent_memory);
        checked(budget)?;
        // SAFETY: a live delegated cgroup2 directory and one checked basename.
        // mkdirat success establishes a fresh group; EEXIST never adopts one.
        if unsafe { libc::mkdirat(parent.as_raw_fd(), name.as_ptr(), 0o700) } != 0 {
            return Err(system("fresh tree create"));
        }
        // SAFETY: open the newly created directory without following aliases.
        let fd = unsafe {
            libc::openat(
                parent.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        if fd < 0 {
            return Err(system("fresh tree open"));
        }
        // SAFETY: successful openat returned a new uniquely owned descriptor.
        let directory = unsafe { File::from_raw_fd(fd) };
        let identity = Identity::capture(&directory, Role::Directory)?;
        require_domain(&directory, budget)?;
        let mut tree = Self {
            kill: Control::open(&directory, c"cgroup.kill", Access::Write)?,
            events: Control::open(&directory, c"cgroup.events", Access::Read)?,
            memory: Control::open(&directory, c"memory.max", Access::Read)?,
            swap: Control::open(&directory, c"memory.swap.max", Access::Read)?,
            tasks: Control::open(&directory, c"pids.max", Access::Read)?,
            kind: Control::open(&directory, c"cgroup.type", Access::Read)?,
            oom: Control::open(&directory, c"memory.oom.group", Access::Read)?,
            directory,
            identity,
            memory_bound,
            budget: budget.clone(),
            armed: false,
            closed: false,
            cleanup_polls,
        };
        if !tree.empty()? {
            return Err(contract("fresh tree is populated"));
        }
        set_scalar(&tree.directory, c"memory.max", memory_bound)?;
        set_scalar(&tree.directory, c"memory.swap.max", 0)?;
        // B2 permits no threads/processes, and trusted pre-B2 entry is single-
        // threaded. This is that actual profile, not an unrelated magic cap.
        set_scalar(&tree.directory, c"pids.max", 1)?;
        set_scalar(&tree.directory, c"memory.oom.group", 1)?;
        tree.same_limits()?;
        tree.closed = false;
        Ok(tree)
    }
    fn same_limits(&self) -> Result<(), Error> {
        checked(&self.budget)?;
        if Identity::capture(&self.directory, Role::Directory)? != self.identity
            || self.memory.scalar(&self.budget)? != self.memory_bound
            || self.swap.scalar(&self.budget)? != 0
            || self.tasks.scalar(&self.budget)? != 1
            || self.oom.scalar(&self.budget)? != 1
        {
            return Err(contract("tree limits or directory changed"));
        }
        let mut bytes = [0; 32];
        let n = self.kind.read(&mut bytes, &self.budget)?;
        if &bytes[..n] != b"domain\n" {
            return Err(contract("tree domain changed"));
        }
        Ok(())
    }
    pub(super) fn check_active(&self) -> Result<(), Error> {
        let result = self.same_limits();
        if result.is_err() {
            self.budget.cancel();
        }
        result
    }
    pub(super) fn arm_birth(&mut self, budget: &Budget) -> Result<RawFd, Error> {
        let result = self.arm_birth_inner(budget);
        if result.is_err() {
            self.budget.cancel();
            budget.cancel();
        }
        result
    }
    fn arm_birth_inner(&mut self, budget: &Budget) -> Result<RawFd, Error> {
        if !self.budget.shares_owner(budget) || self.armed {
            self.budget.cancel();
            budget.cancel();
            return Err(contract("tree owner or repeated birth"));
        }
        self.same_limits()?;
        if !self.empty()? {
            return Err(contract("tree populated before birth"));
        }
        self.armed = true;
        Ok(self.directory.as_raw_fd())
    }
    pub(super) fn stop(&self) -> Result<(), Error> {
        // Cleanup is permitted after the original grant latches refusal.
        let result = self.kill.write(b"1");
        if result.is_err() {
            self.budget.cancel();
        }
        result
    }
    pub(super) fn empty(&self) -> Result<bool, Error> {
        let mut bytes = [0; 64];
        let n = self.events.read(&mut bytes, &self.budget)?;
        empty_events(&bytes[..n])
    }
    pub(super) fn cleanup_poll(&mut self) -> Result<(), Error> {
        original_endpoint(&self.budget)?;
        self.cleanup_polls = self
            .cleanup_polls
            .checked_sub(1)
            .ok_or_else(|| contract("prepaid tree cleanup exhausted"))?;
        Ok(())
    }
    pub(super) fn pause(&self) {
        let left = self.budget.deadline().saturating_duration_since(std::time::Instant::now());
        std::thread::sleep(left.min(Duration::from_millis(1)));
    }
    fn cleanup_limits(&self) -> Result<(), Error> {
        if Identity::capture(&self.directory, Role::Directory)? != self.identity {
            return Err(contract("tree cleanup directory changed"));
        }
        for (control, expected) in
            [(&self.memory, self.memory_bound), (&self.swap, 0), (&self.tasks, 1), (&self.oom, 1)]
        {
            let mut bytes = [0; 22];
            let n = control.cleanup_read(&mut bytes, &self.budget)?;
            if scalar(&bytes[..n])? != expected {
                return Err(contract("tree cleanup limits changed"));
            }
        }
        let mut kind = [0; 32];
        let n = self.kind.cleanup_read(&mut kind, &self.budget)?;
        if &kind[..n] != b"domain\n" {
            return Err(contract("tree cleanup domain changed"));
        }
        Ok(())
    }
    pub(super) fn cleanup_empty(&self) -> Result<bool, Error> {
        if Identity::capture(&self.directory, Role::Directory)? != self.identity {
            return Err(contract("tree cleanup directory changed"));
        }
        let mut bytes = [0; 64];
        let n = self.events.cleanup_read(&mut bytes, &self.budget)?;
        empty_events(&bytes[..n])
    }
    pub(super) fn finish(&mut self) -> Result<(), Error> {
        let result = self.finish_inner();
        if result.is_err() {
            self.budget.cancel();
        }
        result
    }
    fn finish_inner(&mut self) -> Result<(), Error> {
        self.stop()?;
        loop {
            self.cleanup_poll()?;
            if self.cleanup_empty()? {
                self.cleanup_limits()?;
                self.closed = true;
                // A negative structural receipt can retain proven closure.
                // The unchanged transport publication check still observes
                // the sticky owner before any Finished outcome is returned.
                return Ok(());
            }
            self.pause();
        }
    }
}
impl Drop for Tree {
    fn drop(&mut self) {
        if self.armed && !self.closed {
            self.budget.cancel();
            let _ = self.stop();
        }
        // No path is reopened or removed here. The outer owner retains the
        // created namespace and must observe/remove its exact empty group.
    }
}
fn require_domain(directory: &File, budget: &Budget) -> Result<(), Error> {
    let kind = Control::open(directory, c"cgroup.type", Access::Read)?;
    let mut bytes = [0; 32];
    let n = kind.read(&mut bytes, budget)?;
    if &bytes[..n] != b"domain\n" {
        return Err(contract("tree requires an ordinary domain"));
    }
    Ok(())
}
pub(super) fn set_scalar(directory: &File, name: &CStr, value: u64) -> Result<(), Error> {
    let control = Control::open(directory, name, Access::Write)?;
    let mut bytes = [0; 20];
    let mut at = bytes.len();
    let mut rest = value;
    loop {
        at -= 1;
        bytes[at] = b'0' + (rest % 10) as u8;
        rest /= 10;
        if rest == 0 {
            break;
        }
    }
    control.write(&bytes[at..])
}

#[cfg(test)]
mod tests;

fn original_endpoint(budget: &Budget) -> Result<(), Error> {
    if std::time::Instant::now() >= budget.deadline() {
        budget.refuse(trust_process_isolation::Error::Deadline);
        return Err(contract("original tree cleanup deadline"));
    }
    Ok(())
}
fn cleanup_reservation(budget: &Budget) -> Result<u64, Error> {
    checked(budget)?;
    // At most one polling attempt per millisecond plus two terminal reads,
    // spanning leader observation and recursive populated=0. Prepay once from
    // this same owner's finite work limit; unused work is never refunded.
    let left = budget.deadline().saturating_duration_since(std::time::Instant::now());
    let polls = u64::try_from(left.as_millis().saturating_add(2))
        .map_err(|_| contract("tree cleanup reservation overflow"))?;
    let work = polls.checked_mul(8192).ok_or_else(|| contract("tree cleanup work overflow"))?;
    budget.charge(Charge { work, ..Charge::default() }).map_err(Error::Budget)?;
    Ok(polls)
}
