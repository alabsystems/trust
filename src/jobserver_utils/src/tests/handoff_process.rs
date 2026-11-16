use super::*;

#[test]
fn registered_refresh_never_replaces_lifetime_or_parent() {
    let mut birth = Process::current().unwrap();
    birth.identity.birth ^= 1;
    assert!(birth.refresh_registered_member().is_err());
    let mut parent = Process::current().unwrap();
    parent.identity.parent ^= 1;
    assert!(parent.refresh_registered_member().is_err());
    #[cfg(target_os = "macos")]
    {
        let mut parent_birth = Process::current().unwrap();
        parent_birth.identity.parent_birth ^= 1;
        assert!(parent_birth.refresh_registered_member().is_err());
    }
}

#[cfg(target_os = "macos")]
thread_local! {
    /// Calls the stand-ins have answered, and the one that fails (0: none).
    static READS: std::cell::Cell<(u32, u32)> = const { std::cell::Cell::new((0, 0)) };
    /// The flavor of every call the stand-ins answered, in order.
    static FLAVORS: std::cell::RefCell<Vec<libc::c_int>> = const { std::cell::RefCell::new(Vec::new()) };
    /// The errno `gone_at` plants on its failing call.
    static GONE: std::cell::Cell<i32> = const { std::cell::Cell::new(0) };
}

#[cfg(target_os = "macos")]
fn reset(fail: u32) {
    READS.with(|reads| reads.set((0, fail)));
    FLAVORS.with(|flavors| flavors.borrow_mut().clear());
}

/// Count this call and note its flavor; true when it is the one to fail.
/// Every other call reads the real record, so the reader gets past its
/// earlier reads.
#[cfg(target_os = "macos")]
fn failing_read(flavor: libc::c_int) -> bool {
    FLAVORS.with(|flavors| flavors.borrow_mut().push(flavor));
    READS.with(|reads| {
        let (done, fail) = reads.get();
        reads.set((done + 1, fail));
        done + 1 == fail
    })
}

#[cfg(target_os = "macos")]
fn calls() -> u32 {
    READS.with(|reads| reads.get().0)
}

#[cfg(target_os = "macos")]
fn plant(errno: i32) {
    // SAFETY: __error is this thread's errno slot.
    unsafe { *libc::__error() = errno };
}

/// Answers like `native_info`, except that the chosen call returns half a
/// record with EIO planted.
///
/// # Safety
///
/// `native_info`'s.
#[cfg(target_os = "macos")]
unsafe fn short_at(
    pid: libc::c_int,
    flavor: libc::c_int,
    buffer: *mut libc::c_void,
    size: libc::c_int,
) -> libc::c_int {
    if !failing_read(flavor) {
        // SAFETY: forwarded from this function's caller.
        return unsafe { native_info(pid, flavor, buffer, size) };
    }
    plant(libc::EIO);
    size / 2
}

/// Answers like `native_info`, except that the chosen call returns 0 with
/// `GONE`'s errno planted.
///
/// # Safety
///
/// `native_info`'s.
#[cfg(target_os = "macos")]
unsafe fn gone_at(
    pid: libc::c_int,
    flavor: libc::c_int,
    buffer: *mut libc::c_void,
    size: libc::c_int,
) -> libc::c_int {
    if !failing_read(flavor) {
        // SAFETY: forwarded from this function's caller.
        return unsafe { native_info(pid, flavor, buffer, size) };
    }
    plant(GONE.with(std::cell::Cell::get));
    0
}

/// A short positive count sets no errno, so it must not report one: before
/// `read_record`, a short identity record reported whatever errno an earlier
/// call had left. A round that fails nothing pins the reads `read_identity_with`
/// makes through the `proc_pidinfo` it is handed: exactly unique, BSD, unique,
/// in that order. Each later round lets the earlier reads see the real record
/// and fails the next, with a short count (no errno reported) or with 0 and a
/// planted errno that differs per round (that errno reported), and checks that
/// the failing call was the last one made.
#[cfg(target_os = "macos")]
#[test]
fn a_short_identity_record_never_reports_a_stale_errno() {
    let pid = std::process::id();
    reset(0);
    // SAFETY: short_at keeps native_info's contract.
    let identity = unsafe { read_identity_with(pid, short_at) }.unwrap();
    assert_eq!(identity.pid, pid);
    assert_eq!(FLAVORS.with(|flavors| flavors.borrow().clone()), [17, libc::PROC_PIDTBSDINFO, 17]);

    for (read, errno) in [(1, libc::ESRCH), (2, libc::EPERM), (3, libc::EINVAL)] {
        reset(read);
        // SAFETY: short_at keeps native_info's contract.
        let short = unsafe { read_identity_with(pid, short_at) }.unwrap_err();
        assert_eq!(short.raw_os_error(), None, "read {read}: {short}");
        assert_eq!(short.kind(), io::ErrorKind::InvalidData, "read {read}");
        assert_eq!(short.to_string(), "incomplete native process identity record");
        assert_eq!(calls(), read, "read {read} was the last");

        reset(read);
        GONE.with(|gone| gone.set(errno));
        // SAFETY: gone_at keeps native_info's contract.
        let gone = unsafe { read_identity_with(pid, gone_at) }.unwrap_err();
        assert_eq!(gone.raw_os_error(), Some(errno), "read {read}");
        assert_eq!(calls(), read, "read {read} was the last");
    }

    // SAFETY: native_info is the production reader.
    let identity = unsafe { read_identity_with(pid, native_info) }.unwrap();
    assert_eq!(identity, read_identity(pid).unwrap());
}
