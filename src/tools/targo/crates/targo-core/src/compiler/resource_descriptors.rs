//! One maintained native descriptor admission implementation for Host and Root.

pub(super) use trust_resource_controller::descriptors::{DescriptorBudget, RootPermit};

#[cfg(test)]
use std::io;
#[cfg(test)]
fn limits() -> io::Result<libc::rlimit> {
    let mut limits = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    // SAFETY: getrlimit initializes this valid writable rlimit.
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limits) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(limits)
}

#[cfg(test)]
mod tests {
    use super::*;

    const MODE: &str = "TARGO_DESCRIPTOR_TEST_CHILD";

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the isolated child selects its actual inherited RLIMIT test mode before a Cargo context exists"
    )]
    fn host_descriptor_policy_in_child() {
        let Ok(mode) = std::env::var(MODE) else {
            return;
        };
        let original = limits().unwrap();
        let mut limited = libc::rlimit {
            rlim_cur: 256.min(original.rlim_max),
            rlim_max: original.rlim_max,
        };
        if mode == "hard" {
            limited.rlim_max = limited.rlim_cur;
        }
        // SAFETY: this test runs in its own short-lived process. It only
        // reduces limits inherited from its parent, never its parent's limits.
        assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limited) }, 0);
        DescriptorBudget::prepare(28).unwrap();
        let budget = DescriptorBudget::new(28, 5).unwrap();
        let maximum = if mode == "hard" { 4 } else { 28 };
        assert_eq!(budget.member_limit(), maximum);
        let mut permits: Vec<_> = (0..maximum)
            .map(|_| budget.try_root().unwrap().unwrap())
            .collect();
        assert!(budget.try_root().unwrap().is_none());
        drop(permits.pop());
        assert!(budget.try_root().unwrap().is_some());
        if mode == "hard" {
            assert_eq!(limits().unwrap().rlim_cur, limited.rlim_cur);
        } else {
            assert!(limits().unwrap().rlim_cur >= 1024);
        }
    }

    #[test]
    fn resource_budget_tracks_real_host_limits_and_returns_root_permits() {
        for mode in ["soft", "hard"] {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["host_descriptor_policy_in_child", "--nocapture"])
                .env(MODE, mode)
                .status()
                .unwrap();
            assert!(status.success(), "descriptor policy child {mode} failed");
        }
    }
}
