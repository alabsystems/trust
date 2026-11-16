//! Close-only descriptor custody across ordinary libc `fork` and exec.
//!
//! `pthread_atfork` excludes fork throughout nonblocking creation/adoption and
//! registration. Its child handler uses only native `close`/`_exit` and
//! lock-free atomic operations: it never unlocks a pthread mutex or allocates.
//! This is not a resource grant, worker closure or arbitrary child handover.
//! Direct `_Fork`/raw fork syscalls bypass POSIX atfork handlers and are outside
//! this contract. After unsafe fork the child must exec or `_exit`, rather than
//! use the parent's Rust owners of descriptors that were deliberately closed.

use std::cell::UnsafeCell;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd, RawFd};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use std::{io, ptr};

// This native POSIX boundary belongs to the custody kernel. Some consumers
// intentionally expose only a measured subset of libc; their metadata must
// not select whether the real fork exclusion exists. The void callback/int
// result ABI matches pthread.h and the pinned native libc oracle signature.
unsafe extern "C" {
    fn pthread_atfork(
        prepare: Option<unsafe extern "C" fn()>,
        parent: Option<unsafe extern "C" fn()>,
        child: Option<unsafe extern "C" fn()>,
    ) -> std::ffi::c_int;
}

struct Header {
    next: *mut Header,
    raw: *const RawFd,
    len: usize,
}
struct Registry {
    held: AtomicBool,
    head: UnsafeCell<*mut Header>,
}
// SAFETY: head and every linked node are accessed only with held acquired.
// The fork child inherits that consistent protected snapshot and closes it
// before returning from the handler. Nodes stay pinned until unlinked.
unsafe impl Sync for Registry {}
static REGISTRY: Registry =
    Registry { held: AtomicBool::new(false), head: UnsafeCell::new(ptr::null_mut()) };
static INSTALLED: OnceLock<Result<(), i32>> = OnceLock::new();

fn lock() {
    while REGISTRY
        .held
        .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        std::hint::spin_loop();
    }
}
unsafe extern "C" fn prepare() {
    #[cfg(test)]
    PREPARE_ATTEMPTS.fetch_add(1, Ordering::SeqCst);
    lock();
}
unsafe extern "C" fn parent() {
    REGISTRY.held.store(false, Ordering::Release);
}
unsafe extern "C" fn child() {
    // SAFETY: prepare holds exclusion across fork. The child has a consistent
    // private snapshot; no other thread exists here and no allocator runs.
    let mut header = unsafe { *REGISTRY.head.get() };
    while !header.is_null() {
        // SAFETY: every linked pinned node remains live through fork.
        let (raw, len, next) = unsafe { ((*header).raw, (*header).len, (*header).next) };
        for index in 0..len {
            // SAFETY: raw names this node's initialized owned descriptor array.
            let fd = unsafe { *raw.add(index) };
            // SAFETY: this closes only the child's inherited original copy.
            if unsafe { libc::close(fd) } != 0 {
                #[cfg(target_os = "macos")]
                // SAFETY: the native thread-local errno location is valid.
                let errno = unsafe { *libc::__error() };
                #[cfg(target_os = "linux")]
                // SAFETY: the native thread-local errno location is valid.
                let errno = unsafe { *libc::__errno_location() };
                if errno != libc::EBADF {
                    // SAFETY: uncertain close must not let this child continue
                    // with private originals. _exit is async-signal-safe.
                    unsafe { libc::_exit(126) };
                }
            }
        }
        header = next;
    }
    // SAFETY: child-private snapshot only. No stale registration can close a
    // reused descriptor if this unsafe fork child subsequently forks again.
    unsafe { *REGISTRY.head.get() = ptr::null_mut() };
    REGISTRY.held.store(false, Ordering::Release);
}

struct Exclusion;
impl Exclusion {
    fn enter(deadline: Option<Instant>) -> io::Result<Self> {
        let installed = INSTALLED.get_or_init(|| {
            // SAFETY: static non-unwinding handlers outlive every registration.
            let code = unsafe { pthread_atfork(Some(prepare), Some(parent), Some(child)) };
            if code == 0 { Ok(()) } else { Err(code) }
        });
        if let Err(code) = installed {
            return Err(io::Error::from_raw_os_error(*code));
        }
        loop {
            if deadline.is_some_and(|end| Instant::now() >= end) {
                return Err(io::ErrorKind::TimedOut.into());
            }
            if REGISTRY
                .held
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                break;
            }
            std::hint::spin_loop();
        }
        Ok(Self)
    }
}
impl Drop for Exclusion {
    fn drop(&mut self) {
        REGISTRY.held.store(false, Ordering::Release);
    }
}

struct Node<const N: usize> {
    header: Header,
    raw: [RawFd; N],
    owned: [Option<OwnedFd>; N],
    used: usize,
}
/// Destination for a bounded nonblocking native receive. This creates no
/// descriptor itself; it adopts the actual freshly received originals.
pub struct CapturedDescriptors<'a, const N: usize> {
    node: &'a mut Node<N>,
}
struct CaptureClose<'a, const N: usize> {
    node: &'a mut Node<N>,
    accepted: bool,
}
impl<const N: usize> Drop for CaptureClose<'_, N> {
    fn drop(&mut self) {
        if !self.accepted {
            for original in &mut self.node.owned {
                drop(original.take());
            }
        }
    }
}
impl<const N: usize> CapturedDescriptors<'_, N> {
    /// Own one actual descriptor. Rejection closes it before exclusion ends.
    pub fn push(&mut self, mut original: OwnedFd) -> io::Result<()> {
        if self.node.used == N {
            return Err(io::ErrorKind::InvalidData.into());
        }
        if original.as_raw_fd() <= libc::STDERR_FILENO {
            // SAFETY: duplicate this actual newly owned description above
            // stdio while creation/fork exclusion is still held.
            let raw = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 3) };
            if raw < 0 {
                return Err(io::Error::last_os_error());
            }
            use std::os::fd::FromRawFd as _;
            // SAFETY: successful fcntl returned this fresh owned descriptor.
            original = unsafe { OwnedFd::from_raw_fd(raw) };
        }
        // SAFETY: set only the freshly owned original's descriptor-local flag
        // while creation/fork exclusion is still held. Native producers need
        // not already have used an atomic close-on-exec open/receive variant.
        let flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFD) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: set CLOEXEC only on this same newly owned descriptor while
        // the capture interval still excludes ordinary libc fork.
        if unsafe { libc::fcntl(original.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC) } < 0
        {
            return Err(io::Error::last_os_error());
        }
        let index = self.node.used;
        self.node.raw[index] = original.as_raw_fd();
        self.node.owned[index] = Some(original);
        self.node.used += 1;
        Ok(())
    }
}

/// MOVE-only actual originals. No descriptor copies are made by this owner.
/// All originals remain registered until they are unlinked and closed under
/// the same creation/fork exclusion. It exposes no extraction/grant API.
pub struct ProtectedOriginals<const N: usize> {
    node: Box<Node<N>>,
}
// SAFETY: a moved Box keeps the pinned node and its raw array at the same
// address. Cross-thread registry mutation is serialized by REGISTRY. OwnedFd
// ownership and shared borrowing have their ordinary Send/Sync properties.
unsafe impl<const N: usize> Send for ProtectedOriginals<N> {}
// SAFETY: shared access only borrows immutable original descriptors. A node
// cannot be unlinked or dropped until all safe shared borrows have ended.
unsafe impl<const N: usize> Sync for ProtectedOriginals<N> {}
impl<const N: usize> ProtectedOriginals<N> {
    /// Capture exactly N originals. Allocate the fixed node BEFORE exclusion.
    /// `create` must only perform nonblocking native creation/adoption and must
    /// not allocate, spawn/fork, wait, or recursively capture descriptors.
    /// WouldBlock/Interrupted return without leaving partial originals behind.
    /// # Errors
    /// Native exclusion installation, creation or exact descriptor count fails.
    pub fn capture(
        deadline: Instant,
        create: impl FnOnce(&mut CapturedDescriptors<'_, N>) -> io::Result<()>,
    ) -> io::Result<Self> {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        if N == 0 {
            return Err(io::ErrorKind::InvalidInput.into());
        }
        let mut node = Box::new(Node {
            header: Header { next: ptr::null_mut(), raw: ptr::null(), len: N },
            raw: [-1; N],
            owned: [const { None }; N],
            used: 0,
        });
        let exclusion = Exclusion::enter(Some(deadline))?;
        // Declared after exclusion: unwind closes partial originals BEFORE
        // releasing creation exclusion, while Box deallocation occurs later.
        let result = {
            let mut close = CaptureClose { node: &mut node, accepted: false };
            let result = create(&mut CapturedDescriptors { node: close.node }).and_then(|()| {
                if Instant::now() >= deadline {
                    Err(io::ErrorKind::TimedOut.into())
                } else {
                    Ok(())
                }
            });
            close.accepted = result.is_ok() && close.node.used == N;
            result
        };
        if result.is_err() || node.used != N {
            for original in &mut node.owned {
                drop(original.take());
            }
            drop(exclusion);
            return result.and(Err(io::ErrorKind::InvalidData.into()));
        }
        node.header.raw = node.raw.as_ptr();
        // SAFETY: pinned node is complete before publication. Fork cannot
        // observe it until exclusion ends; Drop unlinks it before freeing it.
        unsafe {
            node.header.next = *REGISTRY.head.get();
            *REGISTRY.head.get() = &mut node.header;
        }
        drop(exclusion);
        Ok(Self { node })
    }
    /// Borrow an actual original without transferring ownership or authority.
    pub fn get(&self, index: usize) -> Option<BorrowedFd<'_>> {
        self.node.owned.get(index).and_then(Option::as_ref).map(AsFd::as_fd)
    }
}
impl<const N: usize> Drop for ProtectedOriginals<N> {
    fn drop(&mut self) {
        let Ok(exclusion) = Exclusion::enter(None) else {
            // SAFETY: no unknown registry/descriptor lifetime can be exposed
            // after native exclusion failure. Process failure is not closure.
            unsafe { libc::_exit(126) };
        };
        let target: *mut Header = &mut self.node.header;
        let mut found = false;
        // SAFETY: exclusion protects all next links; this pinned node was
        // published exactly once and has not yet been freed or unlinked.
        unsafe {
            let mut link = REGISTRY.head.get();
            while !(*link).is_null() {
                if *link == target {
                    *link = (*target).next;
                    found = true;
                    break;
                }
                link = &mut (**link).next;
            }
        }
        if !found {
            // SAFETY: unknown registry currency cannot leave a dangling child
            // pointer or silently authorize use of an inherited owner.
            unsafe { libc::_exit(126) };
        }
        for original in &mut self.node.owned {
            drop(original.take());
        }
        drop(exclusion);
    }
}

#[cfg(test)]
static PREPARE_ATTEMPTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
#[path = "tests/fork_custody.rs"]
mod tests;
