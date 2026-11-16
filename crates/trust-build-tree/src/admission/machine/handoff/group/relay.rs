//! One scoped, process-wide interruption owner for a standalone launcher.
//! Refuses an application's existing custom signal handler. Configure only at
//! standalone-launcher startup, without concurrent external signal setup.

use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

use super::*;

static CLAIMED: AtomicBool = AtomicBool::new(false);
static PENDING: AtomicU8 = AtomicU8::new(0);

const SIGNALS: [(libc::c_int, u8); 3] = [(libc::SIGINT, 1), (libc::SIGTERM, 2), (libc::SIGHUP, 4)];

extern "C" fn receive(signal: libc::c_int) {
    let bit = match signal {
        libc::SIGINT => 1,
        libc::SIGTERM => 2,
        libc::SIGHUP => 4,
        _ => 0,
    };
    // Only lock-free native atomic work occurs in the signal handler. The
    // ordinary owning thread performs all child/group/kernel operations.
    PENDING.fetch_or(bit, Ordering::Relaxed);
}

fn handler() -> libc::sighandler_t {
    receive as *const () as libc::sighandler_t
}

pub(super) struct SignalRelay {
    previous: Vec<(libc::c_int, libc::sigaction)>,
}

fn action(signal: libc::c_int) -> io::Result<libc::sigaction> {
    let mut old = std::mem::MaybeUninit::<libc::sigaction>::zeroed();
    // SAFETY: a null new action observes the complete writable old action.
    if unsafe { libc::sigaction(signal, std::ptr::null(), old.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { old.assume_init() })
}

fn set(signal: libc::c_int, action: &libc::sigaction) -> io::Result<()> {
    // SAFETY: a previously observed or completely initialized action; no old
    // buffer is requested. Handler code has static process lifetime.
    if unsafe { libc::sigaction(signal, action, std::ptr::null_mut()) } == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

impl SignalRelay {
    pub(super) fn install() -> io::Result<Self> {
        CLAIMED.compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire).map_err(
            |_| io::Error::new(io::ErrorKind::WouldBlock, "native signal forwarding already owned"),
        )?;
        let originals = (|| -> io::Result<Vec<_>> {
            let mut originals = Vec::with_capacity(3);
            for (signal, _) in SIGNALS {
                let old = action(signal)?;
                if old.sa_sigaction != libc::SIG_DFL && old.sa_sigaction != libc::SIG_IGN {
                    return Err(invalid(
                        "native launcher cannot replace an existing application signal handler",
                    ));
                }
                originals.push((signal, old));
            }
            Ok(originals)
        })();
        let originals = match originals {
            Ok(originals) => originals,
            Err(error) => {
                CLAIMED.store(false, Ordering::Release);
                return Err(error);
            }
        };
        PENDING.store(0, Ordering::Release);
        let mut relay = Self { previous: Vec::with_capacity(3) };
        for (signal, old) in originals {
            // An ignored disposition is inherited across exec. Replacing it
            // with our caught handler would reset the child's disposition to
            // default and turn nohup/ignored-INT into an unexpected kill.
            if old.sa_sigaction == libc::SIG_IGN {
                continue;
            }
            // sigaction is integer fields and pointers; all-zero mask/storage
            // is initialized before the native sigemptyset call fills its mask.
            let mut new: libc::sigaction = unsafe { std::mem::zeroed() };
            new.sa_sigaction = handler();
            new.sa_flags = libc::SA_RESTART;
            if unsafe { libc::sigemptyset(&mut new.sa_mask) } != 0 {
                return Err(io::Error::last_os_error());
            }
            set(signal, &new)?;
            relay.previous.push((signal, old));
        }
        Ok(relay)
    }

    pub(super) fn take(&self) -> Vec<FixedCommandSignal> {
        let bits = PENDING.swap(0, Ordering::AcqRel);
        SIGNALS
            .into_iter()
            .filter_map(|(signal, bit)| {
                if bits & bit == 0 {
                    return None;
                }
                Some(match signal {
                    libc::SIGINT => FixedCommandSignal::Interrupt,
                    libc::SIGTERM => FixedCommandSignal::Terminate,
                    libc::SIGHUP => FixedCommandSignal::Hangup,
                    _ => unreachable!(),
                })
            })
            .collect()
    }
}

impl Drop for SignalRelay {
    fn drop(&mut self) {
        let mut restored = true;
        for (signal, previous) in self.previous.iter().rev() {
            match action(*signal) {
                Ok(current) if current.sa_sigaction == handler() => {
                    if set(*signal, previous).is_err() {
                        restored = false;
                    }
                }
                // A different application owner replaced ours. Do not overwrite
                // it; the next installation's preflight will refuse that handler.
                Ok(_) => {}
                Err(_) => restored = false,
            }
        }
        if restored {
            CLAIMED.store(false, Ordering::Release);
        } else {
            // The static callback remains valid; retain exclusivity rather
            // than pretending that an uncertain restore released its owner.
            let _ = writeln!(
                io::stderr().lock(),
                "native signal handler restoration unknown; forwarding ownership retained"
            );
        }
    }
}
