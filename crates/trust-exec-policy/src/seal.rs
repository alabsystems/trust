//! Fixed self-restriction, not a sandbox profile supplied by a request.
use std::io;

#[link(name = "sandbox")]
unsafe extern "C" {
    fn sandbox_init(profile: *const libc::c_char, flags: u64, error: *mut *mut libc::c_char)
    -> i32;
    fn sandbox_free_error(error: *mut libc::c_char);
    // Native ABI also used by Chromium's sandbox/mac/seatbelt.cc and WebKit's
    // Source/WTF/wtf/spi/darwin/SandboxSPI.h. Parameters are key/value pairs
    // terminated by a null pointer, not source text interpolated into SBPL.
    fn sandbox_init_with_parameters(
        profile: *const libc::c_char,
        flags: u64,
        parameters: *const *const libc::c_char,
        error: *mut *mut libc::c_char,
    ) -> i32;
    fn sandbox_check(pid: libc::pid_t, operation: *const libc::c_char, filter: i32, ...) -> i32;
}

/// A fixed policy on the calling process. This carries no resource authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionSeal {
    /// Trusted preparation may perform its final exec, but cannot create children.
    NoFork,
    /// Final payload may neither fork nor exec another image.
    NoForkOrExec,
}

impl ExecutionSeal {
    /// Install a fixed irreversible policy, then query the actual fork denial.
    /// Call in the trusted early role before payload work. No global exec-policy
    /// observation or installed resource receipt is returned: the no-exec action
    /// is this fixed accepted native profile.
    /// Existing policy, unsupported nesting or installation failure is an error;
    /// callers must never treat an attempted seal as a successful restriction.
    /// An error is not a rollback: never use it to fall back to ordinary work.
    pub fn install_current(self) -> io::Result<()> {
        let profile = match self {
            Self::NoFork => c"(version 1)(allow default)(deny process-fork)",
            Self::NoForkOrExec => {
                c"(version 1)(allow default)(deny process-fork)(deny process-exec)"
            }
        };
        install_profile(profile)?;
        if !fork_denied(std::process::id())? {
            return Err(io::Error::other("native execution seal observation unavailable"));
        }
        Ok(())
    }
}

pub(super) fn install_profile(profile: &std::ffi::CStr) -> io::Result<()> {
    let mut message = std::ptr::null_mut();
    // SAFETY: static valid profile; flags0 means inline profile. This call
    // restricts only the current process. Error storage is initialized null.
    let result = unsafe { sandbox_init(profile.as_ptr(), 0, &mut message) };
    finish_installation(result, message)
}

pub(super) fn install_image_profile(
    image: &std::ffi::CStr,
    descriptor: &std::ffi::CStr,
) -> io::Result<()> {
    let parameters = [
        c"IMAGE".as_ptr(),
        image.as_ptr(),
        c"DESCRIPTOR".as_ptr(),
        descriptor.as_ptr(),
        std::ptr::null(),
    ];
    let profile = c"(version 1)(deny default)(allow file-read* file-map-executable (literal (param \"IMAGE\")) (literal (param \"DESCRIPTOR\")))";
    let mut message = std::ptr::null_mut();
    // SAFETY: fixed profile, live native strings and a null-terminated pair list.
    // The path is passed as data, so quotes/backslashes cannot add policy rules.
    let result = unsafe {
        sandbox_init_with_parameters(profile.as_ptr(), 0, parameters.as_ptr(), &mut message)
    };
    finish_installation(result, message)
}

/// The proc-macro worker's policy. Reads are granted because a macro's inputs
/// are files the compiler could not enumerate for it (its dylib and runtime,
/// sources, manifests, data files); what the policy withholds is every way to
/// change the build or reach another process.
pub(super) fn install_macro_worker_profile(private_tmp: &std::ffi::CStr) -> io::Result<()> {
    let parameters = [c"TMP".as_ptr(), private_tmp.as_ptr(), std::ptr::null()];
    let profile = c"(version 1)(deny default)(allow file-read*)(allow file-map-executable)(allow file-write* (subpath (param \"TMP\")))(allow file-write-data (literal \"/dev/null\"))(allow sysctl-read)(allow signal (target self))";
    let mut message = std::ptr::null_mut();
    // SAFETY: fixed profile, one live native string and a null-terminated pair
    // list. The directory is passed as data, so it cannot add policy rules.
    let result = unsafe {
        sandbox_init_with_parameters(profile.as_ptr(), 0, parameters.as_ptr(), &mut message)
    };
    finish_installation(result, message)
}

fn finish_installation(result: i32, message: *mut libc::c_char) -> io::Result<()> {
    if !message.is_null() {
        // SAFETY: only the OS initializer supplied this error allocation;
        // free it once with its corresponding native allocator.
        unsafe { sandbox_free_error(message) };
    }
    if result != 0 {
        return Err(io::Error::other("native execution seal installation refused"));
    }
    Ok(())
}

/// Read-only fork denial. This does not establish a no-exec policy,
/// original-child custody, or a resource receipt. Validate a native lifetime
/// and image separately across an observation of another process.
pub fn fork_denied(pid: u32) -> io::Result<bool> {
    let pid = valid_pid(pid)?;
    // SAFETY: query-only call with static operation and SANDBOX_FILTER_NONE;
    // there are no variadic filter arguments or caller-supplied policy bytes.
    verdict(unsafe { sandbox_check(pid, c"process-fork".as_ptr(), 0) })
}

fn valid_pid(pid: u32) -> io::Result<i32> {
    i32::try_from(pid).ok().filter(|pid| *pid > 0).ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidInput, "invalid native process identity")
    })
}

fn verdict(result: i32) -> io::Result<bool> {
    match result {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(io::Error::other(format!(
            "native execution seal query unavailable (result {result}, errno {})",
            io::Error::last_os_error()
        ))),
    }
}
