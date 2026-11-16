//! The library environment a census program is derived in (design §2.3:
//! "the library environment"; Critique C-1 change 2: a verdict must not
//! depend on the host that computed it).
//!
//! RL-INIT says the table at the root's entry is arbitrary. The limits that
//! bound it are NOT this machine's: `kern.maxfilesperproc` is a sysctl (this
//! Mac: 92 160, with `kern.maxfiles` 184 320 — raisable), and a descriptor
//! inherited from a parent with a higher limit keeps its number across exec
//! whatever the soft `RLIMIT_NOFILE` is. So:
//!
//! * the per-process maximum is the C `int` bound (`2^31 - 1`): a foreign
//!   descriptor may sit at any number below it, the soft limit
//!   notwithstanding (`trust_platform_derive::env::Limits::foreign_limit`);
//! * the soft limit at entry is explored at two values — launchd's default
//!   (256: a Dock-launched process) and the `int` maximum — and the hard
//!   limit is `RLIM_INFINITY`. A guard on the soft limit's value is exact
//!   at those two points only: premise [`P_RLIMIT_SOFT`], printed with
//!   every verdict.
//!
//! The host derives each (root, site) program once per environment of
//! [`library_envs`]; [`crate::verdict::site_verdict`] requires evidence for
//! every one of them before "not refuted".

use trust_platform::darwin;
use trust_platform_derive::env::{EnvSpec, Limits, Slot};

use crate::CensusPremise;

/// launchd's default soft `RLIMIT_NOFILE` (a Dock-launched process).
pub const LAUNCHD_SOFT_NOFILE: u64 = 256;

/// The largest descriptor number bound any host can configure: the C `int`
/// range (`kern.maxfilesperproc` is an `int`).
pub const INT_MAX_FILES: u64 = i32::MAX as u64;

/// The premise every verdict rests on: the soft limit's two explored values.
pub const P_RLIMIT_SOFT: &str = "P-RLIMIT-SOFT";

/// The limits of each library environment.
#[must_use]
pub fn library_limits() -> Vec<Limits> {
    [LAUNCHD_SOFT_NOFILE, INT_MAX_FILES]
        .into_iter()
        .map(|soft| Limits { soft, hard: darwin::RLIM_INFINITY, max_files_per_proc: INT_MAX_FILES })
        .collect()
}

/// Every library environment (index = `SiteEvidence::env`): descriptor
/// arguments on 3, 4 or a middle slot, one unflagged foreign descriptor at
/// every partition position below the `int` bound, no fd-bound premise.
#[must_use]
pub fn library_envs() -> Vec<EnvSpec> {
    library_limits()
        .into_iter()
        .map(|limits| EnvSpec {
            limits,
            param_slots: vec![Slot::Exact(3), Slot::Exact(4), Slot::Mid],
            foreign: true,
            foreign_at: Vec::new(),
            fd_bound_cap: None,
            // No RL-INIT namespace: the census emits no named open (an
            // `open` path is `PC-NONCONST-ARG` until producer increment B4).
            names: Vec::new(),
        })
        .collect()
}

/// The environment premise, as printed with a verdict.
#[must_use]
pub fn premise() -> CensusPremise {
    CensusPremise {
        code: P_RLIMIT_SOFT,
        text: format!(
            "the root starts with soft RLIMIT_NOFILE {LAUNCHD_SOFT_NOFILE} (launchd's default) or \
             {INT_MAX_FILES} (the int maximum), hard RLIM_INFINITY; a foreign descriptor may sit \
             at any number below {INT_MAX_FILES}, above the soft limit too; a guard on another \
             soft-limit value is not explored"
        ),
        at: vec!["<library environment>".to_string()],
    }
}
