//! Trust: let a native, unverified frontend use the shared jobserver's room.
//!
//! This is a worker ceiling, not additional CPU capacity. rustc's thread pool
//! acquires the same jobserver tokens as other compilation units. Proof sessions
//! retain their separate, deliberately serial frontend policy.

use std::ffi::OsStr;

mod intent;
pub(crate) use intent::ResourceIntent;

pub(super) fn frontend_jobs<'a>(
    native_unverified: bool,
    jobs: u32,
    args: impl IntoIterator<Item = &'a OsStr>,
) -> Option<u32> {
    if !native_unverified || jobs <= 1 {
        return None;
    }
    let mut unstable = false;
    for arg in args {
        let Some(arg) = arg.to_str() else { return None };
        // Response files can contain explicit controls. Do not second-guess
        // them or compiler/proxy arguments we cannot inspect losslessly.
        if arg.starts_with('@')
            || arg == "--jobs"
            || arg.starts_with("--jobs=")
            || arg == "-j"
            || arg
                .strip_prefix("-j")
                .is_some_and(|value| !value.is_empty())
            || arg == "--jobs-frontend"
            || arg.starts_with("--jobs-frontend=")
            || arg == "-Zthreads"
            || arg.starts_with("-Zthreads=")
            || arg.starts_with("-Z=threads")
            || (unstable && arg.starts_with("threads="))
        {
            return None;
        }
        unstable = arg == "-Z";
    }
    // rustc's frontend thread count has an explicit 255-worker upper bound.
    Some(jobs.min(255))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget(native: bool, jobs: u32, args: &[&str]) -> Option<u32> {
        frontend_jobs(native, jobs, args.iter().map(OsStr::new))
    }

    #[test]
    fn shares_the_admitted_budget_without_changing_proof_or_serial_builds() {
        assert_eq!(budget(true, 21, &["--crate-name", "large"]), Some(21));
        assert_eq!(budget(true, 300, &[]), Some(255));
        assert_eq!(budget(false, 21, &[]), None);
        assert_eq!(budget(true, 1, &[]), None);
    }

    #[test]
    fn explicit_controls_and_opaque_arguments_win() {
        for args in [
            vec!["--jobs", "2"],
            vec!["--jobs=2"],
            vec!["-j", "2"],
            vec!["-j2"],
            vec!["--jobs-frontend", "2"],
            vec!["--jobs-frontend=2"],
            vec!["-Zthreads=2"],
            vec!["-Z=threads=2"],
            vec!["-Z", "threads=2"],
            vec!["@arguments"],
        ] {
            assert_eq!(budget(true, 21, &args), None, "{args:?}");
        }
        assert_eq!(budget(true, 21, &["-Z", "unstable-options"]), Some(21));
    }
}
