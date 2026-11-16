//! Refuse native producing contexts before raw driver modes can execute code.

use crate::getopts::Matches;

pub(super) enum Phase {
    Options,
    Backend,
}

pub(super) fn refusal(matches: &Matches, phase: Phase) -> Option<&'static str> {
    let present = |name| matches.opt_defined(name) && matches.opt_present(name);
    // Trust: private Fixed routing never enters raw backend/pager execution.
    // Actual compiler admission remains exclusively the pinned native issuer.
    if present("resource-bootstrap-fixed-v1") {
        if ["resource-worker-v2", "resource-worker-v3", "resource-subgroups-v3"]
            .into_iter()
            .any(present)
        {
            return Some("private Bootstrap Fixed compiler excludes other worker protocols");
        }
        if present("explain") {
            return Some(
                "private Fixed compiler cannot execute the pre-interface explanation pager",
            );
        }
        if matches!(phase, Phase::Backend) {
            return Some(
                "private Fixed compiler cannot construct an unauthenticated early backend",
            );
        }
    }
    let worker = present("resource-worker-v3");
    let subgroups = present("resource-subgroups-v3");
    if worker != subgroups || (worker && present("resource-worker-v2")) {
        return Some("native v3 requires both custody markers and excludes v2");
    }
    if !worker {
        return None;
    }
    if present("explain") {
        return Some("native v3 producing work cannot execute the pre-interface explanation pager");
    }
    if matches!(phase, Phase::Backend) {
        return Some("native v3 producing work cannot construct an unauthenticated early backend");
    }
    None
}

#[cfg(test)]
#[path = "native_v3_early/tests.rs"]
mod tests;
