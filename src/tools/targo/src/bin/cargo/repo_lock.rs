//! Native source-tree administration; the shared manager owns every policy.
//! This route never resolves a frontend sidecar, project alias or compiler.

use std::ffi::OsString;

pub(super) fn requested(args: &[OsString]) -> bool {
    matches!(args, [trust, repo, lock, ..] if trust == "trust" && repo == "repo" && lock == "lock")
}

pub(super) fn run(args: &[OsString]) -> u8 {
    // The native caller authenticates its entry and original purpose before
    // selecting this route. The manager retains its exact existing parser,
    // namespace, owner/liveness, token and WITHHELD refusal semantics.
    trust_build_tree::trust_repo_lock::management::cli::run(&args[3..])
}

#[cfg(test)]
mod public_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_exact_native_manager_prefix_selects_administration() {
        let words = |values: &[&str]| values.iter().map(OsString::from).collect::<Vec<_>>();
        for tail in [
            vec![],
            vec!["--protocol"],
            vec!["acquire", "--kind", "build"],
        ] {
            let mut args = words(&["trust", "repo", "lock"]);
            args.extend(tail.into_iter().map(OsString::from));
            assert!(requested(&args));
        }
        for args in [
            vec!["trust", "repo"],
            vec!["trust", "repo", "locker"],
            vec!["alias", "trust", "repo", "lock"],
            vec!["--config", "trust", "repo", "lock"],
            vec!["--unverified", "run", "--", "trust", "repo", "lock"],
        ] {
            assert!(!requested(&words(&args)), "{args:?}");
        }
    }
}
