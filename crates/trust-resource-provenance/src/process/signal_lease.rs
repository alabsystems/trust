//! The existing opt-in streaming signal epoch, shared by native child owners.
//! Handler replacement, final restoration and pending-cancellation semantics
//! stay identical for Cargo and compiletest. No PID or admission is created.
use std::io;

// Trust: only opt-in streaming operations take this process-wide signal lease.
// The handler is allocation/lock free; the observer performs cleanup while the
// leader remains unreaped. Existing API users retain their signal behavior.
#[cfg(any(target_os = "linux", target_os = "macos"))]
static STREAMING_SIGNAL_LEASE: std::sync::Mutex<StreamingSignalState> =
    std::sync::Mutex::new(StreamingSignalState { users: 0, prior: Vec::new() });

#[cfg(any(target_os = "linux", target_os = "macos"))]
struct StreamingSignalState {
    users: usize,
    prior: Vec<(libc::c_int, libc::sigaction)>,
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
static STREAMING_PENDING_SIGNALS: std::sync::atomic::AtomicU32 =
    std::sync::atomic::AtomicU32::new(0);
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub const OWNED_GROUP_SIGNALS: [libc::c_int; 4] =
    [libc::SIGINT, libc::SIGTERM, libc::SIGHUP, libc::SIGQUIT];

#[cfg(any(target_os = "linux", target_os = "macos"))]
extern "C" fn streaming_signal(signal: libc::c_int) {
    STREAMING_PENDING_SIGNALS.fetch_or(1 << signal, std::sync::atomic::Ordering::Relaxed);
}

pub fn pending_child_signal() -> u32 {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    return STREAMING_PENDING_SIGNALS.load(std::sync::atomic::Ordering::Acquire);
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    0
}

pub struct ChildSignalLease {
    restored: bool,
}

impl ChildSignalLease {
    /// Observe the canonical installed handler identity without invoking it.
    /// This pointer is diagnostic data and creates no signal or execution grant.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn handler_address() -> usize {
        streaming_signal as *const () as usize
    }

    pub fn install(enabled: bool) -> io::Result<Option<Self>> {
        if !enabled {
            return Ok(None);
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            let mut state =
                STREAMING_SIGNAL_LEASE.lock().unwrap_or_else(|error| error.into_inner());
            if state.users == 0 {
                STREAMING_PENDING_SIGNALS.store(0, std::sync::atomic::Ordering::Release);
                for signal in OWNED_GROUP_SIGNALS {
                    let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
                    action.sa_sigaction = streaming_signal as *const () as usize;
                    action.sa_flags = libc::SA_RESTART;
                    unsafe {
                        libc::sigemptyset(&mut action.sa_mask);
                    }
                    let mut prior: libc::sigaction = unsafe { std::mem::zeroed() };
                    if unsafe { libc::sigaction(signal, &action, &mut prior) } != 0 {
                        let error = io::Error::last_os_error();
                        for (installed, previous) in state.prior.drain(..).rev() {
                            unsafe {
                                libc::sigaction(installed, &previous, std::ptr::null_mut());
                            }
                        }
                        return Err(error);
                    }
                    state.prior.push((signal, prior));
                }
            } else {
                for signal in OWNED_GROUP_SIGNALS {
                    let mut current: libc::sigaction = unsafe { std::mem::zeroed() };
                    if unsafe { libc::sigaction(signal, std::ptr::null(), &mut current) } != 0 {
                        return Err(io::Error::last_os_error());
                    }
                    if current.sa_sigaction != streaming_signal as *const () as usize {
                        return Err(io::Error::other(
                            "streaming signal handler changed while leased",
                        ));
                    }
                }
            }
            state.users = state
                .users
                .checked_add(1)
                .ok_or_else(|| io::Error::other("too many streaming signal users"))?;
            Ok(Some(Self { restored: false }))
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        Err(io::Error::new(io::ErrorKind::Unsupported, "streaming signal cleanup is unsupported"))
    }

    pub fn restore(&mut self) -> io::Result<()> {
        if self.restored {
            return Ok(());
        }
        self.restored = true;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            let mut state =
                STREAMING_SIGNAL_LEASE.lock().unwrap_or_else(|error| error.into_inner());
            state.users = state.users.checked_sub(1).expect("owned streaming signal registration");
            let mut error = None;
            if state.users == 0 {
                for (signal, prior) in state.prior.drain(..).rev() {
                    let mut current: libc::sigaction = unsafe { std::mem::zeroed() };
                    if unsafe { libc::sigaction(signal, std::ptr::null(), &mut current) } != 0 {
                        error.get_or_insert_with(io::Error::last_os_error);
                    } else if current.sa_sigaction != streaming_signal as *const () as usize {
                        error.get_or_insert_with(|| {
                            io::Error::other("streaming signal handler changed while leased")
                        });
                    } else if unsafe { libc::sigaction(signal, &prior, std::ptr::null_mut()) } != 0
                    {
                        error.get_or_insert_with(io::Error::last_os_error);
                    }
                }
            }
            if let Some(error) = error {
                return Err(error);
            }
            let pending = pending_child_signal();
            if pending != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    format!("streaming process interrupted by signal mask {pending:#x}"),
                ));
            }
        }
        Ok(())
    }
}

impl Drop for ChildSignalLease {
    fn drop(&mut self) {
        let _ = self.restore();
    }
}
