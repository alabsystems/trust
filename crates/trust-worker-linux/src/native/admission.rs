use trust_process_isolation::Charge;

use super::closure::Inventory;
use super::{BANK_FIRST, BANK_LAST, charge, check, contract};
use crate::Error;

#[cfg(target_arch = "aarch64")]
pub(super) const ARCH: u32 = 0xc00000b7;
#[cfg(target_arch = "x86_64")]
pub(super) const ARCH: u32 = 0xc000003e;
#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
pub(super) const ARCH: u32 = 0;

#[repr(C)]
#[derive(Debug, Default, Clone, Copy)]
pub(super) struct Data {
    pub nr: i32,
    pub arch: u32,
    pub ip: u64,
    pub args: [u64; 6],
}
#[repr(C)]
#[derive(Debug, Default, Clone, Copy)]
pub(super) struct Notification {
    pub id: u64,
    pub pid: u32,
    pub flags: u32,
    pub data: Data,
}

/// Only implementations bound to the owned listener and the retained one-mm FD
/// belong in the kernel path. Target bytes never become borrowed Rust objects.
pub(super) trait Memory {
    fn copy(&mut self, id: u64, address: u64, bytes: &mut [u8]) -> Result<usize, Error>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    Configured,
    Active,
    Pending(u64, usize, u32),
    Terminal,
}
#[derive(Debug)]
pub(super) struct Admission {
    pub closure: Inventory,
    task: u32,
    phase: Phase,
    next: u32,
}
#[derive(Debug, Clone, Copy)]
pub(super) struct Grant {
    pub id: u64,
    pub object: usize,
    pub target: u32,
}

impl Admission {
    pub fn new(closure: impl Into<Inventory>) -> Self {
        Self { closure: closure.into(), task: 0, phase: Phase::Configured, next: BANK_FIRST }
    }
    pub fn activate(&mut self, task: u32) -> Result<(), Error> {
        check(&self.closure.budget)?;
        if self.phase != Phase::Configured || task == 0 || ARCH == 0 {
            return self.fail("native service activation");
        }
        self.task = task;
        self.phase = Phase::Active;
        Ok(())
    }
    fn fail<T>(&mut self, why: &'static str) -> Result<T, Error> {
        self.phase = Phase::Terminal;
        Err(contract(&self.closure.budget, why))
    }
    pub fn admit(&mut self, n: Notification, memory: &mut impl Memory) -> Result<Grant, Error> {
        let result = self.inner(n, memory);
        if result.is_err() {
            self.phase = Phase::Terminal;
            self.closure.budget.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    fn inner(&mut self, n: Notification, memory: &mut impl Memory) -> Result<Grant, Error> {
        let b = &self.closure.budget;
        check(b)?;
        charge(b, Charge { calls: 1, work: 256, ..Charge::default() })?;
        if self.phase != Phase::Active
            || n.pid != self.task
            || n.id == 0
            || n.flags != 0
            || n.data.arch != ARCH
            || self.next > BANK_LAST
        {
            return self.fail("native notification identity/phase/bank");
        }
        let a = n.data.args;
        let (pointer, flags, mode) = match i64::from(n.data.nr) {
            nr if is_open(nr) => (a[0], a[1], a[2]),
            nr if nr == libc::SYS_openat => {
                if !cwd(a[0]) {
                    return self.fail("native openat directory authority");
                }
                (a[1], a[2], a[3])
            }
            nr if nr == libc::SYS_openat2 => {
                if !cwd(a[0]) || a[3] != 24 {
                    return self.fail("native openat2 directory/layout");
                }
                let mut how = [0; 24];
                copied(memory, n.id, a[2], &mut how, b)?;
                let flags = u64::from_le_bytes(
                    how[..8].try_into().map_err(|_| contract(b, "open_how flags"))?,
                );
                let mode = u64::from_le_bytes(
                    how[8..16].try_into().map_err(|_| contract(b, "open_how mode"))?,
                );
                let resolve = u64::from_le_bytes(
                    how[16..].try_into().map_err(|_| contract(b, "open_how resolve"))?,
                );
                if resolve != 0 {
                    return self.fail("native openat2 resolve");
                }
                (a[1], flags, mode)
            }
            _ => return self.fail("native notification syscall"),
        };
        let allowed = (libc::O_CLOEXEC | libc::O_LARGEFILE) as u64;
        if flags & !allowed != 0 || mode != 0 {
            return self.fail("native open flags/mode");
        }
        let mut path = [0; 4096];
        let mut used = 0;
        let end;
        loop {
            if used == path.len() {
                return self.fail("native pathname bound");
            }
            let count = (path.len() - used).min(64);
            let at = pointer
                .checked_add(used as u64)
                .ok_or_else(|| contract(b, "native pathname pointer"))?;
            let got = partial(memory, n.id, at, &mut path[used..used + count], b)?;
            if got == 0 || got > count {
                return self.fail("native pathname read");
            }
            charge(b, Charge { work: got as u64, ..Charge::default() })?;
            if let Some(nul) = path[used..used + got].iter().position(|c| *c == 0) {
                end = used + nul;
                break;
            }
            used += got;
        }
        if end == 0 || path[0] != b'/' {
            return self.fail("native literal absolute alias");
        }
        let mut found = None;
        for (at, object) in self.closure.objects.iter().enumerate() {
            for alias in &object.aliases {
                charge(b, Charge { work: (alias.len() + end) as u64, ..Charge::default() })?;
                if alias == &path[..end] {
                    found = Some(at);
                }
            }
        }
        let object = found.ok_or_else(|| contract(b, "unknown native open alias"))?;
        check(b)?;
        let grant = Grant { id: n.id, object, target: self.next };
        self.phase = Phase::Pending(n.id, object, self.next);
        Ok(grant)
    }
    pub fn commit(&mut self, grant: Grant, issued: u32) -> Result<(), Error> {
        check(&self.closure.budget)?;
        if self.phase != Phase::Pending(grant.id, grant.object, grant.target) || issued != self.next
        {
            return self.fail("native descriptor issuance identity");
        }
        self.next += 1;
        self.phase = Phase::Active;
        Ok(())
    }
}
fn cwd(fd: u64) -> bool {
    fd == libc::AT_FDCWD as u32 as u64 || fd == libc::AT_FDCWD as i64 as u64
}
fn is_open(nr: i64) -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        nr == libc::SYS_open
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let _ = nr;
        false
    }
}
fn partial(
    m: &mut impl Memory,
    id: u64,
    address: u64,
    dst: &mut [u8],
    b: &trust_process_isolation::Budget,
) -> Result<usize, Error> {
    if address == 0 || address.checked_add(dst.len() as u64).is_none_or(|end| end > i64::MAX as u64)
    {
        return Err(contract(b, "native target address"));
    }
    charge(b, Charge { work: 3 * dst.len() as u64 + 128, ..Charge::default() })?;
    let n = m.copy(id, address, dst)?;
    if n > dst.len() {
        return Err(contract(b, "native target count"));
    }
    check(b)?;
    Ok(n)
}
fn copied(
    m: &mut impl Memory,
    id: u64,
    mut address: u64,
    mut dst: &mut [u8],
    b: &trust_process_isolation::Budget,
) -> Result<(), Error> {
    while !dst.is_empty() {
        let n = partial(m, id, address, dst, b)?;
        if n == 0 {
            return Err(contract(b, "native target short copy"));
        }
        address += n as u64;
        dst = &mut dst[n..];
    }
    Ok(())
}
