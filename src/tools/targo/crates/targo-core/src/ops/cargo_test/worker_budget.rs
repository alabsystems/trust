// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Trust: cooperative worker ceilings for admitted native libtest execution.
//!
//! These environment inputs are scheduling metadata, not authenticated resource
//! authority. A thread ceiling does not acquire jobserver permits or confine
//! arbitrary threads a test creates.

use std::ffi::OsStr;

use cargo_util::ProcessBuilder;

use crate::util::{CargoResult, GlobalContext};

#[derive(Clone, Copy)]
pub(super) struct WorkerBudget {
    ceiling: usize,
}

impl WorkerBudget {
    pub(super) fn native(gctx: &GlobalContext) -> CargoResult<Option<Self>> {
        if !crate::is_targo_invocation() || crate::trust_verified_targo() {
            return Ok(None);
        }
        Self::managed(gctx)
    }

    /// Read the current cooperative allocation. Prepared execution calls this
    /// only after its authenticated lane has been established; these inputs
    /// neither select that lane nor supply execution authority.
    pub(super) fn managed(gctx: &GlobalContext) -> CargoResult<Option<Self>> {
        Self::from_env(
            gctx.get_env_os("BUILD_SLOT_HELD"),
            gctx.get_env_os("CARGO_BUILD_JOBS"),
        )
    }

    fn from_env(held: Option<&OsStr>, jobs: Option<&OsStr>) -> CargoResult<Option<Self>> {
        let Some(held) = held else { return Ok(None) };
        anyhow::ensure!(
            held == "1",
            "managed test execution requires BUILD_SLOT_HELD=1"
        );
        let jobs = jobs
            .and_then(OsStr::to_str)
            .filter(|raw| !raw.is_empty() && raw.bytes().all(|byte| byte.is_ascii_digit()))
            .and_then(|raw| raw.parse::<usize>().ok())
            .filter(|&jobs| jobs != 0)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "BUILD_SLOT_HELD=1 requires positive ASCII-decimal CARGO_BUILD_JOBS"
                )
            })?;
        Ok(Some(Self { ceiling: jobs }))
    }

    pub(super) fn process_limit(self, requested: usize) -> usize {
        requested.min(self.ceiling)
    }

    /// Apply after the target/build-script environment has been assembled.
    /// Libtest CLI flags override this environment, so validate both forms too.
    pub(super) fn apply(self, command: &mut ProcessBuilder, args: &[&str]) -> CargoResult<()> {
        self.validate_args(args)?;
        let preference = command
            .get_env("RUST_TEST_THREADS")
            .map(|raw| count(raw.to_str(), "RUST_TEST_THREADS"))
            .transpose()?
            .unwrap_or(self.ceiling);
        command.env(
            "RUST_TEST_THREADS",
            preference.min(self.ceiling).to_string(),
        );
        Ok(())
    }

    /// Check an already-authorized command without rewriting it. The explicit
    /// environment bound was established before the plan was authenticated;
    /// execution cannot silently recapture ambient libtest defaults or repair
    /// a plan which exceeds the allocation that owns this phase.
    pub(super) fn validate_prepared(self, args: &[&str], threads: Option<&str>) -> CargoResult<()> {
        self.validate_args(args)?;
        let requested = count(threads, "prepared RUST_TEST_THREADS")?;
        anyhow::ensure!(
            requested <= self.ceiling,
            "prepared RUST_TEST_THREADS requests {requested} workers, exceeding the admitted ceiling {}",
            self.ceiling
        );
        Ok(())
    }

    fn validate_args(self, args: &[&str]) -> CargoResult<()> {
        visit_thread_requests(args, |value| {
            let requested = count(value, "--test-threads")?;
            anyhow::ensure!(
                requested <= self.ceiling,
                "--test-threads requests {requested} workers, exceeding the admitted ceiling {}",
                self.ceiling
            );
            Ok(())
        })
    }
}

/// Inspect real libtest worker options, preserving opaque option values and
/// the filter tail. Both scheduling owners use this same argument grammar.
pub(super) fn visit_thread_requests<'a>(
    args: &[&'a str],
    mut visit: impl FnMut(Option<&'a str>) -> CargoResult<()>,
) -> CargoResult<()> {
    let mut args = args.iter().copied();
    while let Some(arg) = args.next() {
        let value = if arg == "--" {
            break;
        } else if arg == "--test-threads" {
            Some(args.next())
        } else if let Some(value) = arg.strip_prefix("--test-threads=") {
            Some(Some(value))
        } else {
            // These standard libtest options consume a following value.
            // In particular, a skip filter is opaque even when it spells
            // `--test-threads=...`; it is not another worker request.
            if matches!(
                arg,
                "-Z" | "--logfile" | "--skip" | "--color" | "--format" | "--shuffle-seed"
            ) {
                args.next();
            }
            None
        };
        if let Some(value) = value {
            visit(value)?;
        }
    }
    Ok(())
}

fn count(raw: Option<&str>, name: &str) -> CargoResult<usize> {
    raw.and_then(|raw| raw.parse::<usize>().ok())
        .filter(|&count| count != 0)
        .ok_or_else(|| {
            anyhow::anyhow!("{name} must be a positive integer for managed test execution")
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_budget_distinguishes_real_worker_requests_from_opaque_filters() {
        for args in [vec!["--test-threads=1"], vec!["--test-threads", "1"]] {
            let error = super::super::validate_native_test_arguments(&args).unwrap_err();
            assert!(error.is::<super::super::NativeTestBudgetRefusal>());
        }
        for args in [
            vec!["--skip", "--test-threads=1"],
            vec!["--", "--test-threads=1"],
            vec!["--logfile", "--test-threads=1"],
            vec!["--test-threads-filter"],
        ] {
            assert!(
                super::super::validate_native_test_arguments(&args).is_ok(),
                "{args:?}"
            );
        }
    }

    #[test]
    fn prepared_command_requires_explicit_bounded_environment_and_arguments() {
        let budget = WorkerBudget::from_env(Some(OsStr::new("1")), Some(OsStr::new("2")))
            .unwrap()
            .unwrap();
        assert!(budget.validate_prepared(&[], Some("2")).is_ok());
        assert!(
            budget
                .validate_prepared(&["--test-threads=1"], Some("2"))
                .is_ok()
        );
        for threads in [None, Some(""), Some("0"), Some("invalid"), Some("3")] {
            assert!(
                budget.validate_prepared(&[], threads).is_err(),
                "{threads:?}"
            );
        }
        for args in [vec!["--test-threads=3"], vec!["--test-threads", "3"]] {
            assert!(budget.validate_prepared(&args, Some("1")).is_err());
        }
        assert!(
            budget
                .validate_prepared(&["--skip", "--test-threads=3"], Some("1"))
                .is_ok()
        );
        assert!(
            budget
                .validate_prepared(&["--", "--test-threads=3"], Some("1"))
                .is_ok()
        );
    }

    #[test]
    fn preparation_caps_effective_preference_before_authorization() {
        let budget = WorkerBudget::from_env(Some(OsStr::new("1")), Some(OsStr::new("2")))
            .unwrap()
            .unwrap();
        let mut command = ProcessBuilder::new("test-image");
        command.env("RUST_TEST_THREADS", "64");
        budget.apply(&mut command, &[]).unwrap();
        assert_eq!(
            command.get_env("RUST_TEST_THREADS").as_deref(),
            Some(OsStr::new("2"))
        );
        command.env("RUST_TEST_THREADS", "1");
        budget.apply(&mut command, &[]).unwrap();
        assert_eq!(
            command.get_env("RUST_TEST_THREADS").as_deref(),
            Some(OsStr::new("1"))
        );
    }
}
