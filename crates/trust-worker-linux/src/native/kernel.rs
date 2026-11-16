//! Private kernel capability service. This is not a complete production launch
//! route: its caller still owns trusted entry/one-mm custody and kill/reap.
use std::fs::File;
use std::os::fd::AsRawFd;
use std::os::unix::fs::MetadataExt;

use trust_process_isolation::{Budget, Charge};

use super::admission::{Admission, Memory, Notification};
use super::closure::Inventory;
use super::{BANK_FIRST, BANK_LAST, charge, check, contract, reserve};
use crate::{Error, system};

#[repr(C)]
#[derive(Default)]
struct Sizes {
    notif: u16,
    response: u16,
    data: u16,
}
#[repr(C)]
#[derive(Default)]
struct Response {
    id: u64,
    value: i64,
    error: i32,
    flags: u32,
}
#[repr(C)]
#[derive(Default)]
struct AddFd {
    id: u64,
    flags: u32,
    source: u32,
    target: u32,
    target_flags: u32,
}

// Use the pinned libc's ABI type/encoding: GNU takes unsigned long, whereas
// musl takes int. In particular RECEIVE has bit31 set; a numeric TryFrom into
// musl's signed int would wrongly reject that valid 32-bit UAPI pattern.
// Admission below still checks exact layouts and never decodes worker C data.
const RECEIVE: libc::Ioctl = libc::_IOWR::<Notification>(b'!' as u32, 0);
const VALID: libc::Ioctl = libc::_IOW::<u64>(b'!' as u32, 2);
const ADD: libc::Ioctl = libc::_IOW::<AddFd>(b'!' as u32, 3);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct FileIdentity {
    pub device: u64,
    pub inode: u64,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct IssuedDescriptor {
    pub object: u8,
    pub target: u32,
    pub file: FileIdentity,
    pub sha256: [u8; 32],
    pub size: u64,
}

pub(super) struct Service {
    listener: File,
    memory: File,
    admission: Admission,
    // Open all finite fresh descriptions during trusted broker setup. No path
    // open, including /proc/self/fd, belongs to notification-time service.
    // Each bank slot can issue any admitted object once; shared offsets across
    // independent opens are not silently substituted for fresh descriptions.
    sources: Vec<Vec<File>>,
    identities: Vec<FileIdentity>,
}
impl Service {
    /// The caller must already own the unreaped single-thread child and exact
    /// post-exec mm; no later exec/clone or untrusted pre-entry code is allowed.
    /// These owned FDs come from the trusted handoff, not a worker proof marker.
    pub fn adopt(
        listener: File,
        memory: File,
        task: u32,
        closure: impl Into<Inventory>,
    ) -> Result<Self, Error> {
        let closure = closure.into();
        let owner = closure.budget.clone();
        let result = (|| {
            let b = &closure.budget;
            charge(b, Charge { work: 512, ..Charge::default() })?;
            let mut sizes = Sizes::default();
            // SAFETY: sizes has the exact kernel UAPI layout and writable size;
            // GET_NOTIF_SIZES is a scalar query, not filter activation.
            if unsafe { libc::syscall(libc::SYS_seccomp, 3u32, 0u32, &mut sizes) } != 0 {
                return Err(system("native notification sizes"));
            }
            if sizes.notif as usize != std::mem::size_of::<Notification>()
                || sizes.response as usize != std::mem::size_of::<Response>()
                || sizes.data as usize != std::mem::size_of::<super::admission::Data>()
            {
                return Err(contract(b, "native kernel notification layout"));
            }
            let mut sources = reserve(closure.objects.len(), b)?;
            let mut identities = reserve(closure.objects.len(), b)?;
            for object in &closure.objects {
                let metadata =
                    object.snapshot.file.metadata().map_err(|error| {
                        Error::System("native immutable source identity", error)
                    })?;
                identities.push(FileIdentity { device: metadata.dev(), inode: metadata.ino() });
                let mut fresh = reserve((BANK_LAST - BANK_FIRST + 1) as usize, b)?;
                for _ in BANK_FIRST..=BANK_LAST {
                    fresh.push(crate::launcher::snapshot::fresh_readonly(&object.snapshot, b)?);
                }
                sources.push(fresh);
            }
            let mut admission = Admission::new(closure);
            admission.activate(task)?;
            Ok(Self { listener, memory, admission, sources, identities })
        })();
        // A caller retaining the original shared allowance observes every
        // adoption failure. Descriptors drop on all errors, never leak/retry.
        if result.is_err() {
            owner.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    pub fn listener_fd(&self) -> i32 {
        self.listener.as_raw_fd()
    }
    pub fn memory_fd(&self) -> i32 {
        self.memory.as_raw_fd()
    }
    /// Fixed retained capabilities for trusted broker clamping, allocated and
    /// charged before irreversible policy. No numeric worker FD is accepted.
    pub fn descriptors(&self, maps: &File) -> Result<Vec<i32>, Error> {
        let b = &self.admission.closure.budget;
        let count = self
            .sources
            .iter()
            .try_fold(3 + self.admission.closure.objects.len(), |n, list| n.checked_add(list.len()))
            .ok_or_else(|| contract(b, "native broker descriptor count"))?;
        let mut result = reserve(count, b)?;
        result.extend([self.listener.as_raw_fd(), self.memory.as_raw_fd(), maps.as_raw_fd()]);
        for object in &self.admission.closure.objects {
            result.push(object.snapshot.file.as_raw_fd());
        }
        for sources in &self.sources {
            for source in sources {
                result.push(source.as_raw_fd());
            }
        }
        check(b)?;
        Ok(result)
    }

    /// One readiness-confirmed request, not an unbounded drain. A caller polls
    /// with the original deadline alongside capture/status and never on HUP.
    /// Kernel RECV/ADDFD and retained-mm pread are opaque blocking intervals.
    /// A production owner must retain an independent child/broker watchdog and
    /// kill/reap custody through them; this substrate promises no hard latency.
    pub fn ready_once(&mut self) -> Result<IssuedDescriptor, Error> {
        self.ready_with(|| {})
    }
    #[cfg(test)]
    pub(super) fn ready_once_after_poll(
        &mut self,
        after_ready: impl FnOnce(),
    ) -> Result<IssuedDescriptor, Error> {
        self.ready_with(after_ready)
    }
    fn ready_with(&mut self, after_ready: impl FnOnce()) -> Result<IssuedDescriptor, Error> {
        let b = self.admission.closure.budget.clone();
        let result = self.once(after_ready);
        if result.is_err() {
            b.refuse(trust_process_isolation::Error::Phase);
        }
        result
    }
    fn once(&mut self, after_ready: impl FnOnce()) -> Result<IssuedDescriptor, Error> {
        let b = self.admission.closure.budget.clone();
        charge(&b, Charge { work: 512, ..Charge::default() })?;
        let mut event =
            libc::pollfd { fd: self.listener.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one complete live pollfd with zero timeout cannot retain its
        // pointer. Readability is mandatory before the potentially blocking RECV.
        if unsafe { libc::poll(&mut event, 1, 0) } != 1 || event.revents != libc::POLLIN {
            return Err(contract(&b, "native notification not exclusively readable"));
        }
        // Target cancellation may race readiness. A sole-reader RECV must
        // still validate the kernel result; no readiness bit is an authority.
        after_ready();
        check(&b)?;
        let mut n = Notification::default();
        // SAFETY: the zeroed complete fixed-layout record lives for the ioctl;
        // the caller owns the sole listener reader and readiness was checked.
        if unsafe { libc::ioctl(self.listener.as_raw_fd(), RECEIVE, &mut n) } != 0 {
            return Err(system("native notification receive"));
        }
        check(&b)?;
        let mut memory =
            RetainedMemory { listener: &self.listener, memory: &self.memory, budget: &b };
        let grant = self.admission.admit(n, &mut memory)?;
        valid(&self.listener, grant.id, &b)?;
        // Only descriptions prepaid and prepared for this exact immutable ELF
        // inventory can reach ADDFD. A consumed source is never put back after
        // an opaque failure; all errors terminally refuse the service.
        let fresh = self
            .sources
            .get_mut(grant.object)
            .and_then(Vec::pop)
            .ok_or_else(|| contract(&b, "native prepared source exhausted"))?;
        let source =
            u32::try_from(fresh.as_raw_fd()).map_err(|_| contract(&b, "native source FD"))?;
        charge(&b, Charge { work: 256, ..Charge::default() })?;
        let mut add = AddFd {
            id: grant.id,
            flags: 1 | 2,
            source,
            target: grant.target,
            target_flags: libc::O_CLOEXEC as u32,
        };
        // SAFETY: the exact initialized UAPI record and owned immutable source
        // stay live. SETFD|SEND atomically issues/replies; target is one-use bank
        // state, never a worker-selected number. No CONTINUE or host-path open.
        let issued = unsafe { libc::ioctl(self.listener.as_raw_fd(), ADD, &mut add) };
        if issued < 0 {
            return Err(system("native atomic descriptor issuance"));
        }
        drop(fresh);
        check(&b)?;
        let object = self
            .admission
            .closure
            .objects
            .get(grant.object)
            .ok_or_else(|| contract(&b, "native issued object"))?;
        let record = IssuedDescriptor {
            object: u8::try_from(grant.object).map_err(|_| contract(&b, "native issued index"))?,
            target: grant.target,
            file: *self
                .identities
                .get(grant.object)
                .ok_or_else(|| contract(&b, "native issued inode"))?,
            sha256: object.snapshot.sha256,
            size: object.snapshot.size,
        };
        self.admission.commit(grant, issued as u32)?;
        Ok(record)
    }
}

fn valid(listener: &File, id: u64, b: &Budget) -> Result<(), Error> {
    charge(b, Charge { work: 64, ..Charge::default() })?;
    let mut id = id;
    // SAFETY: ID_VALID reads one complete u64; listener is the retained owned
    // filter FD. No process path is opened or task supplied by a worker.
    if unsafe { libc::ioctl(listener.as_raw_fd(), VALID, &mut id) } != 0 {
        return Err(system("native notification ID invalid"));
    }
    check(b)
}
struct RetainedMemory<'a> {
    listener: &'a File,
    memory: &'a File,
    budget: &'a Budget,
}
impl Memory for RetainedMemory<'_> {
    fn copy(&mut self, id: u64, address: u64, dst: &mut [u8]) -> Result<usize, Error> {
        valid(self.listener, id, self.budget)?;
        let offset =
            i64::try_from(address).map_err(|_| contract(self.budget, "native mm address"))?;
        // SAFETY: the bounded writable destination stays live, offset fits
        // off_t, and this read-only FD retains the exact owned post-exec mm.
        let n = unsafe {
            libc::pread(self.memory.as_raw_fd(), dst.as_mut_ptr().cast(), dst.len(), offset)
        };
        valid(self.listener, id, self.budget)?;
        if n < 0 {
            return Err(system("native retained-mm read"));
        }
        let n = n as usize;
        if n > dst.len() {
            return Err(contract(self.budget, "native mm count"));
        }
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn uapi_layouts_and_ioctl_directions_are_exact() {
        assert_eq!(std::mem::size_of::<Notification>(), 80);
        assert_eq!(std::mem::offset_of!(Notification, data), 16);
        assert_eq!(std::mem::size_of::<Response>(), 24);
        assert_eq!(std::mem::size_of::<AddFd>(), 24);
        // Compare the exact UAPI bit patterns across signed/unsigned libc ABI.
        assert_eq!(RECEIVE as u32, 0xc0502100);
        assert_eq!(VALID as u32, 0x40082102);
        assert_eq!(ADD as u32, 0x40182103);
        assert_eq!(RECEIVE as u32, crate::filter::broker::RECEIVE);
        assert_eq!(VALID as u32, crate::filter::broker::VALID);
        assert_eq!(ADD as u32, crate::filter::broker::ADD);
    }

    #[test]
    fn all_finite_sources_are_prepared_readonly_with_independent_offsets() {
        use std::io::{Read, Seek, SeekFrom};
        let b = super::super::tests::budget();
        let closure = super::super::tests::closure(b.clone());
        let null = || File::open("/dev/null").unwrap();
        // Source preparation is independent of listener activation; these
        // stand-ins cannot service a notification and confer no kernel result.
        let mut service = Service::adopt(null(), null(), 1, closure).unwrap();
        assert_eq!(service.sources.len(), 1);
        assert_eq!(service.sources[0].len(), (BANK_LAST - BANK_FIRST + 1) as usize);
        let first = service.sources[0].pop().unwrap();
        let expected = first.metadata().unwrap();
        use std::os::unix::fs::MetadataExt;
        for mut source in service.sources[0].drain(..) {
            let actual = source.metadata().unwrap();
            assert_eq!((actual.dev(), actual.ino()), (expected.dev(), expected.ino()));
            // SAFETY: scalar flag/seal observations on this owned source.
            let flags = unsafe { libc::fcntl(source.as_raw_fd(), libc::F_GETFL) };
            assert_eq!(flags & libc::O_ACCMODE, libc::O_RDONLY);
            assert_eq!(source.seek(SeekFrom::Current(0)).unwrap(), 0);
            let mut magic = [0; 4];
            source.read_exact(&mut magic).unwrap();
            assert_eq!(&magic, b"\x7fELF");
        }
        let mut first = first;
        assert_eq!(first.seek(SeekFrom::Current(0)).unwrap(), 0);
        b.check().unwrap();
    }
}
