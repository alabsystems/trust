use std::io::Read;
use std::os::fd::RawFd;

use sha2::{Digest, Sha256};
use trust_process_isolation::{Budget, Charge};

use crate::{Error, filter, system};

const HANDLED: u64 = (1 << 15) - 1;
const SEALS: i32 = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;

#[derive(Debug, Clone, Copy)]
pub struct PinnedInput {
    pub fd: RawFd,
    pub sha256: [u8; 32],
    pub size: u64,
    pub executable: bool,
}
#[derive(Debug, Clone, Copy)]
pub struct KernelLimits {
    pub address_space_bytes: u64,
    pub stack_bytes: u64,
    /// Per-file kernel limit; the parent still owns aggregate scratch quota.
    pub file_bytes: u64,
    pub descriptors: u32,
}
#[derive(Debug)]
pub struct Profile<'a> {
    pub parent_pid: libc::pid_t,
    pub inputs: &'a [PinnedInput],
    pub limits: KernelLimits,
}

/// Local installation marker only. It has no serialization or proof authority.
#[derive(Debug)]
pub struct Installed {
    landlock_abi: u32,
    budget: Budget,
    control_closed: bool,
}
impl Installed {
    pub fn landlock_abi(&self) -> u32 {
        self.landlock_abi
    }
    /// Borrow the authenticated, non-recyclable FD3 installed by trusted entry.
    /// Dropping or closing this one connection is terminal even if this marker
    /// is borrowed again. This grants no native loader/readiness authority.
    pub fn control(
        &mut self,
    ) -> Result<crate::RetainedControl<'_>, trust_process_isolation::Error> {
        crate::RetainedControl::new(&self.budget, &mut self.control_closed)
    }
    fn new(landlock_abi: u32, budget: &Budget) -> Self {
        Self { landlock_abi, budget: budget.clone(), control_closed: false }
    }
}

#[repr(C)]
struct Ruleset {
    handled_access_fs: u64,
}
#[repr(C)]
struct Program {
    len: u16,
    filter: *const filter::Instruction,
}

mod broker_entry;
mod native_entry;
mod resources;
pub(crate) use broker_entry::{install_broker, validate_handoff as validate_broker_handoff};
pub(crate) use native_entry::{authenticate_bootstrap, install_native};

/// Only call from a trusted single-threaded worker entry before user constructors.
/// On any error the caller must terminate this process, including partial install.
pub fn install(profile: &Profile<'_>, budget: &Budget) -> Result<Installed, Error> {
    let result = install_inner(profile, budget, Entry::Single);
    if result.is_err() {
        budget.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
fn checked(budget: &Budget) -> Result<(), Error> {
    budget.check().map_err(Error::Budget)
}

/// Fixed restriction-only entry for the internally embedded static checker.
///
/// The trusted startup must be single threaded and terminate on any error, as
/// for `install`. Its parent must apply the same finite RLIMIT_AS before exec,
/// retain exclusive unreaped leader/pidfd ownership, enforce the original
/// absolute deadline, and kill/reap the entire thread group on every exit path.
/// Threads inherit this filter and share that mm/AS limit. AS is not RSS or a
/// kernel task-count limit: aggregate memory/pids containment remains external.
/// This local installation marker authenticates no executable or solver result.
/// There is no selectable policy, flag mask, retry or renewed budget here.
#[doc(hidden)]
pub fn install_checker_threads(profile: &Profile<'_>, budget: &Budget) -> Result<Installed, Error> {
    let result = install_inner(profile, budget, Entry::CheckerThreads);
    if result.is_err() {
        budget.refuse(trust_process_isolation::Error::Phase);
    }
    result
}

/// Fixed checker profile with separate live read-only kernel resource roles:
/// FD6 is this worker's statm and FD7 is kernel meminfo. They are independently
/// authenticated, retained and read only by bounded pread; they are not sealed
/// source inputs. Trusted startup installs the corresponding AY observations
/// before this call. All thread/parent/deadline/containment prerequisites of
/// install_checker_threads remain mandatory; no proof authority is granted.
#[doc(hidden)]
pub fn install_checker_resources(
    profile: &Profile<'_>,
    budget: &Budget,
) -> Result<Installed, Error> {
    let result = install_inner(profile, budget, Entry::CheckerResources);
    if result.is_err() {
        budget.refuse(trust_process_isolation::Error::Phase);
    }
    result
}

enum Entry {
    Single,
    CheckerThreads,
    CheckerResources,
}

fn install_inner(profile: &Profile<'_>, budget: &Budget, entry: Entry) -> Result<Installed, Error> {
    checked(budget)?;
    validate(profile, budget)?;
    prepare_control(budget)?;
    let first_dynamic = if matches!(entry, Entry::CheckerResources) {
        resources::validate(profile, budget)?;
        8
    } else {
        u32::try_from(5 + profile.inputs.len()).map_err(|_| Error::Contract("FD count"))?
    };
    let mut executable = [0; 27];
    let mut count = 0;
    for input in profile.inputs {
        if input.executable {
            executable[count] = input.fd as u32;
            count += 1;
        }
    }
    let filter = match entry {
        Entry::Single => filter::build(first_dynamic, &executable[..count])?,
        Entry::CheckerThreads => filter::checker_threads(first_dynamic, &executable[..count])?,
        Entry::CheckerResources => filter::checker_resources()?,
    };
    checked(budget)?;
    restrict_entry(profile, budget, first_dynamic, None)?;
    let abi = landlock(budget)?;
    let program = Program {
        len: u16::try_from(filter.len).map_err(|_| Error::Contract("filter length"))?,
        filter: filter.instructions.as_ptr(),
    };
    // SAFETY: the live immutable instruction array and C-layout program remain
    // valid until the kernel copies them. TSYNC applies this restrictive filter
    // to all threads; trusted startup separately rejects preexisting threads.
    if unsafe { libc::syscall(libc::SYS_seccomp, 1u32, 1u32, &program) } != 0 {
        return Err(system("seccomp TSYNC"));
    }
    checked(budget)?;
    Ok(Installed::new(abi, budget))
}

/// Trusted single-thread entry only, after FD3/parent authentication and before
/// seccomp. No alias, signal handler or constructor may mutate its open-file
/// flags concurrently. F_SETFL remains forbidden by every installed policy.
fn prepare_control(budget: &Budget) -> Result<(), Error> {
    checked(budget)?;
    budget.charge(Charge { work: 3, ..Charge::default() }).map_err(Error::Budget)?;
    let current = flags(3)?;
    checked(budget)?;
    // SAFETY: validated FD3 is the retained parent stream. Preserve all status
    // flags and set only O_NONBLOCK before irreversible filter installation.
    if unsafe { libc::fcntl(3, libc::F_SETFL, current | libc::O_NONBLOCK) } != 0 {
        return Err(system("control nonblocking setup"));
    }
    checked(budget)?;
    if flags(3)? & libc::O_NONBLOCK == 0 {
        return Err(Error::Contract("control remains blocking"));
    }
    checked(budget)
}

/// Shared irreversible clamp. The native entry may preserve exactly one
/// separately validated high bootstrap descriptor; the B2 path preserves none.
fn restrict_entry(
    profile: &Profile<'_>,
    budget: &Budget,
    first_dynamic: u32,
    transfer: Option<u32>,
) -> Result<(), Error> {
    restrict_identity()?;
    let end = transfer.map_or(u32::MAX, |fd| fd - 1);
    // SAFETY: retained FD0..N-1 were validated. All higher capabilities close
    // except the already validated native bootstrap socket, if one is supplied.
    if unsafe { libc::syscall(libc::SYS_close_range, first_dynamic, end, 0u32) } != 0 {
        return Err(system("close_range"));
    }
    if let Some(fd) = transfer {
        // SAFETY: the checked native layout has fd<=4096, so fd+1 cannot
        // overflow and this closes the remaining higher ambient capabilities.
        if unsafe { libc::syscall(libc::SYS_close_range, fd + 1, u32::MAX, 0u32) } != 0 {
            return Err(system("close_range above transfer"));
        }
    }
    restrict_limits(profile, budget)
}

fn restrict_identity() -> Result<(), Error> {
    // SAFETY: prctl receives scalar arguments for the calling worker only. No
    // pointers or privileges are introduced; failures abort this installation.
    if unsafe {
        libc::prctl(
            libc::PR_SET_DUMPABLE,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        )
    } != 0
    {
        return Err(system("PR_SET_DUMPABLE"));
    }
    // SAFETY: no_new_privs is an irreversible scalar restriction on this worker.
    if unsafe {
        libc::prctl(
            libc::PR_SET_NO_NEW_PRIVS,
            1 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        )
    } != 0
    {
        return Err(system("PR_SET_NO_NEW_PRIVS"));
    }
    Ok(())
}

fn restrict_limits(profile: &Profile<'_>, budget: &Budget) -> Result<(), Error> {
    checked(budget)?;
    for (resource, limit) in [
        (libc::RLIMIT_CORE, 0),
        (libc::RLIMIT_AS, profile.limits.address_space_bytes),
        (libc::RLIMIT_STACK, profile.limits.stack_bytes),
        (libc::RLIMIT_FSIZE, profile.limits.file_bytes),
        (libc::RLIMIT_NOFILE, u64::from(profile.limits.descriptors)),
    ] {
        let value = libc::rlimit { rlim_cur: limit, rlim_max: limit };
        // SAFETY: value lives through the syscall and has libc's rlimit layout;
        // both limits restrict the current worker without addressing another PID.
        if unsafe { libc::setrlimit(resource, &value) } != 0 {
            return Err(system("setrlimit"));
        }
        checked(budget)?;
    }
    Ok(())
}

pub(crate) fn validate(profile: &Profile<'_>, budget: &Budget) -> Result<(), Error> {
    validate_inner(profile, budget, 64)
}

fn validate_inner(profile: &Profile<'_>, budget: &Budget, maximum: u32) -> Result<(), Error> {
    // SAFETY: querying personality uses the documented all-ones sentinel and
    // makes no change to the current worker's execution domain.
    let persona = unsafe { libc::personality(0xffff_ffff) };
    if persona < 0 {
        return Err(system("personality query"));
    }
    native_personality(persona as u32)?;
    entry_mappings(budget)?;
    if profile.parent_pid <= 0
        || profile.inputs.len() > 27
        || profile.limits.address_space_bytes == 0
        || profile.limits.stack_bytes == 0
        || profile.limits.file_bytes == 0
        || profile.limits.address_space_bytes == u64::MAX
        || profile.limits.stack_bytes == u64::MAX
        || profile.limits.file_bytes == u64::MAX
        || profile.limits.stack_bytes > profile.limits.address_space_bytes
        || !(u32::try_from(6 + profile.inputs.len()).map_err(|_| Error::Contract("FD count"))?
            ..=maximum)
            .contains(&profile.limits.descriptors)
    {
        return Err(Error::Contract("finite kernel envelope"));
    }
    if std::env::vars_os().next().is_some() {
        return Err(Error::Contract("ambient environment"));
    }
    let threads = std::fs::read_dir("/proc/self/task")
        .map_err(|error| Error::System("task inventory", error))?;
    let mut count = 0;
    for entry in threads {
        entry.map_err(|error| Error::System("task inventory entry", error))?;
        count += 1;
        if count > 1 {
            return Err(Error::Contract("worker is not single threaded"));
        }
    }
    if count != 1 {
        return Err(Error::Contract("task inventory"));
    }
    let input = stat(0)?;
    if input.st_mode & libc::S_IFMT != libc::S_IFCHR
        || libc::major(input.st_rdev) != 1
        || libc::minor(input.st_rdev) != 3
        || flags(0)? & libc::O_ACCMODE != libc::O_RDONLY
    {
        return Err(Error::Contract("null stdin"));
    }
    for fd in [1, 2] {
        if stat(fd)?.st_mode & libc::S_IFMT != libc::S_IFIFO
            || flags(fd)? & libc::O_ACCMODE != libc::O_WRONLY
        {
            return Err(Error::Contract("diagnostic output pipe"));
        }
    }
    if stat(3)?.st_mode & libc::S_IFMT != libc::S_IFSOCK
        || flags(3)? & libc::O_ACCMODE != libc::O_RDWR
    {
        return Err(Error::Contract("control socket"));
    }
    for (option, expected) in [(libc::SO_DOMAIN, libc::AF_UNIX), (libc::SO_TYPE, libc::SOCK_STREAM)]
    {
        let mut value: libc::c_int = 0;
        let mut length = std::mem::size_of_val(&value) as libc::socklen_t;
        // SAFETY: getsockopt can write only to the live integer and length;
        // their exact byte sizes are provided and verified after the syscall.
        if unsafe {
            libc::getsockopt(
                3,
                libc::SOL_SOCKET,
                option,
                (&mut value as *mut libc::c_int).cast(),
                &mut length,
            )
        } != 0
        {
            return Err(system("control getsockopt"));
        }
        if value != expected || length as usize != std::mem::size_of_val(&value) {
            return Err(Error::Contract("control socket type"));
        }
    }
    let mut peer = libc::ucred { pid: 0, uid: 0, gid: 0 };
    let mut length = std::mem::size_of_val(&peer) as libc::socklen_t;
    // SAFETY: peer and length are writable for their supplied exact sizes.
    if unsafe {
        libc::getsockopt(
            3,
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut peer as *mut libc::ucred).cast(),
            &mut length,
        )
    } != 0
    {
        return Err(system("control peer"));
    }
    if length as usize != std::mem::size_of_val(&peer) || peer.pid != profile.parent_pid {
        return Err(Error::Contract("control parent binding"));
    }
    let scratch = stat(4)?;
    // SAFETY: geteuid is a scalar observation, not a credential change.
    if scratch.st_mode & libc::S_IFMT != libc::S_IFDIR
        || scratch.st_mode & 0o7777 != 0o700
        || scratch.st_uid != unsafe { libc::geteuid() }
        || flags(4)? & libc::O_PATH == 0
    {
        return Err(Error::Contract("private scratch directory"));
    }
    let mut entries = std::fs::read_dir("/proc/self/fd/4")
        .map_err(|error| Error::System("scratch inventory", error))?;
    if let Some(entry) = entries.next() {
        entry.map_err(|error| Error::System("scratch inventory entry", error))?;
        return Err(Error::Contract("scratch not empty"));
    }
    drop(entries);
    for (index, input) in profile.inputs.iter().enumerate() {
        if input.fd != i32::try_from(5 + index).map_err(|_| Error::Contract("input FD"))? {
            return Err(Error::Contract("dense input FDs"));
        }
        verify_input(input, budget)?;
    }
    checked(budget)
}

fn flags(fd: RawFd) -> Result<i32, Error> {
    // SAFETY: F_GETFL reads flags for an existing descriptor, with no pointer.
    let result = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if result < 0 { Err(system("descriptor flags")) } else { Ok(result) }
}
fn stat(fd: RawFd) -> Result<libc::stat, Error> {
    let mut result = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: fstat writes a full libc::stat to valid aligned storage; the
    // record is read only after the syscall reports success.
    if unsafe { libc::fstat(fd, result.as_mut_ptr()) } != 0 {
        return Err(system("descriptor stat"));
    }
    // SAFETY: successful fstat initialized the complete C-layout record.
    Ok(unsafe { result.assume_init() })
}
fn verify_input(input: &PinnedInput, budget: &Budget) -> Result<(), Error> {
    if input.sha256 == [0; 32] || input.size > i64::MAX as u64 {
        return Err(Error::Contract("input identity"));
    }
    let metadata = stat(input.fd)?;
    if metadata.st_mode & libc::S_IFMT != libc::S_IFREG
        || u64::try_from(metadata.st_size).ok() != Some(input.size)
        || flags(input.fd)? & libc::O_ACCMODE != libc::O_RDONLY
    {
        return Err(Error::Contract("read-only regular input identity"));
    }
    // SAFETY: F_GET_SEALS only observes seals on the validated open descriptor.
    let seals = unsafe { libc::fcntl(input.fd, libc::F_GET_SEALS) };
    if seals < 0 {
        return Err(system("input seals"));
    }
    if seals & SEALS != SEALS {
        return Err(Error::Contract("input not immutable"));
    }
    let work = input
        .size
        .checked_mul(2)
        .ok_or_else(|| Error::Budget(budget.refuse(trust_process_isolation::Error::Overflow)))?;
    budget.charge(Charge { work, ..Charge::default() }).map_err(Error::Budget)?;
    let mut hash = Sha256::new();
    let mut block = [0u8; 8192];
    let mut offset = 0u64;
    while offset < input.size {
        checked(budget)?;
        let count = usize::try_from((input.size - offset).min(block.len() as u64))
            .map_err(|_| Error::Contract("input block"))?;
        // SAFETY: block is writable for count<=8192; the checked offset fits
        // off_t. pread neither changes the capability's position nor reopens it.
        let read = unsafe {
            libc::pread(input.fd, block.as_mut_ptr().cast(), count, offset as libc::off_t)
        };
        if read < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return Err(Error::System("input read", error));
        }
        if read == 0 {
            return Err(Error::Contract("input truncated"));
        }
        let read = usize::try_from(read).map_err(|_| Error::Contract("input read count"))?;
        if read > count {
            return Err(Error::Contract("input read count"));
        }
        hash.update(&block[..read]);
        offset += read as u64;
        checked(budget)?;
    }
    let actual: [u8; 32] = hash.finalize().into();
    if actual != input.sha256 {
        return Err(Error::Contract("input digest"));
    }
    Ok(())
}

pub(crate) fn landlock(budget: &Budget) -> Result<u32, Error> {
    // SAFETY: the version query uses no pointer, zero size, and ABI query flag.
    let abi = unsafe {
        libc::syscall(libc::SYS_landlock_create_ruleset, std::ptr::null::<Ruleset>(), 0usize, 1u32)
    };
    if abi < 0 {
        return Err(system("Landlock ABI"));
    }
    if abi < 3 {
        return Err(Error::Contract("Landlock ABI below 3"));
    }
    let attr = Ruleset { handled_access_fs: HANDLED };
    // SAFETY: the exact first-version attribute prefix is live for its size;
    // ABI>=3 supports every handled filesystem bit through TRUNCATE.
    let fd = unsafe {
        libc::syscall(libc::SYS_landlock_create_ruleset, &attr, std::mem::size_of_val(&attr), 0u32)
    };
    if fd < 0 {
        return Err(system("Landlock create"));
    }
    let fd = i32::try_from(fd).map_err(|_| Error::Contract("Landlock FD"))?;
    // SAFETY: this fresh successful syscall returned unique ownership of fd.
    let rules = unsafe { <std::os::fd::OwnedFd as std::os::fd::FromRawFd>::from_raw_fd(fd) };
    // No path grants: even the reserved scratch directory requires a future
    // typed broker. In particular Landlock cannot secure procfs reopenings of
    // anonymous pipes/sockets, so seccomp also denies every ambient open path.
    checked(budget)?;
    // SAFETY: ruleset descriptor belongs to this worker; no_new_privs is already
    // set. The call only restricts the trusted single startup thread.
    if unsafe { libc::syscall(libc::SYS_landlock_restrict_self, fd, 0u32) } != 0 {
        return Err(system("Landlock restrict"));
    }
    drop(rules);
    checked(budget)?;
    u32::try_from(abi).map_err(|_| Error::Contract("Landlock ABI"))
}

fn native_personality(persona: u32) -> Result<(), Error> {
    // READ_IMPLIES_EXEC would turn a permitted readable anonymous mapping into
    // executable memory even when the requested protection omits PROT_EXEC.
    if persona != 0 { Err(Error::Contract("non-native personality")) } else { Ok(()) }
}
fn entry_mappings(budget: &Budget) -> Result<(), Error> {
    // Reserve the fixed read/UTF-8/scan bound before work, including any short
    // reads. No untrusted mapping inventory can expand this stack buffer.
    budget.charge(Charge { work: 8 * 65536, ..Charge::default() }).map_err(Error::Budget)?;
    let mut maps = std::fs::File::open("/proc/self/maps")
        .map_err(|error| Error::System("entry mappings", error))?;
    let mut bytes = [0u8; 65536];
    let mut used = 0;
    loop {
        checked(budget)?;
        if used == bytes.len() {
            return Err(Error::Contract("entry mapping inventory bound"));
        }
        let count = maps
            .read(&mut bytes[used..])
            .map_err(|error| Error::System("entry mappings read", error))?;
        if count == 0 {
            break;
        }
        used += count;
    }
    let text = std::str::from_utf8(&bytes[..used])
        .map_err(|_| Error::Contract("entry mapping encoding"))?;
    for line in text.lines() {
        let permissions =
            line.split_whitespace().nth(1).ok_or(Error::Contract("entry mapping record"))?;
        if permissions.len() != 4 {
            return Err(Error::Contract("entry mapping permissions"));
        }
        if permissions.as_bytes()[1] == b'w' && permissions.as_bytes()[2] == b'x' {
            return Err(Error::Contract("existing writable executable mapping"));
        }
    }
    checked(budget)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn only_exact_native_personality_is_admitted() {
        assert!(native_personality(0).is_ok());
        for persona in [0x0400000, 8, 0x40000, u32::MAX] {
            assert!(native_personality(persona).is_err());
        }
    }
}
