//! The `clean` executable the binary cross-check gates measure.
//!
//! Five gates in `tests/` shell out to a `clean` binary:
//! `ay_blast_correspondence_gate`, `structured_multiplier_proof_gate`,
//! `i128_corner_bounds_proof_gate`, `codegen_equivalence_gate` and
//! `trust_soundness_ouroboros_gate`. What such a run measures is THE BINARY:
//! that a `clean` built from the pinned `first-party/clean` agrees with the
//! verdicts reached in process. The proofs' authority does not live there.
//! `clean-parser`, `clean-elab` and `clean-kernel` are dependencies of
//! `trust-certify`, so `lean_front_door_gate` kernel-checks both corpora in
//! process, at the pinned revision, and [`crate::clean_proof_obligations`] holds
//! the required theorem names and the multiply-cap coupling; nothing there is
//! discovered and nothing can skip.
//!
//! The binary is named, never discovered: [`require_clean_bin`] reads
//! `TRUST_CLEAN_BIN` and panics, with the build recipe, without it. The five
//! gates are `#[ignore]`d, and the `slow.clean-binary-proof-gates` row of
//! `tests/run_trust_comprehensive_harness.sh` builds `clean` from the submodule
//! at its pin, exports the variable, runs them with `--ignored`, and demands
//! `1 passed` from each.
//!
//! Until 2026-10-09 a search here (beside the test binary, then
//! `build/*/stage{2,3}/bin`, then `first-party/clean/target`) that found
//! nothing made all five gates return green with a NOTICE that libtest
//! captured, so a fresh clone or worktree passed them having run nothing. One
//! that found something measured whatever had built it: on the measured host a
//! nine-day-old stage2 `clean`, not the pinned source.

use std::ffi::OsString;
use std::path::PathBuf;

use crate::trust_rustc::is_executable_file;

/// The environment variable that names the `clean` executable to measure.
pub const TRUST_CLEAN_BIN: &str = "TRUST_CLEAN_BIN";

/// How to build `clean` from the pinned submodule, from the repository root.
/// The executable is `<target dir>/release/clean`; cargo's
/// `--message-format json` names it exactly.
pub const CLEAN_BUILD_RECIPE: &str = "targo --unverified build --manifest-path \
     first-party/clean/Cargo.toml -p clean --bin clean --release --locked";

/// The `clean` executable `TRUST_CLEAN_BIN` names. Panics, naming the build
/// recipe, when the variable is unset or empty or names no executable file.
#[must_use]
pub fn require_clean_bin() -> PathBuf {
    match clean_bin_from(std::env::var_os(TRUST_CLEAN_BIN)) {
        Ok(path) => {
            // Printed per test (libtest captures per test thread), so a failing
            // gate's output names the binary it measured.
            eprintln!("clean checker: {}", path.display());
            path
        }
        Err(why) => panic!("{why}"),
    }
}

/// [`require_clean_bin`] over an explicit `TRUST_CLEAN_BIN` value.
pub fn clean_bin_from(value: Option<OsString>) -> Result<PathBuf, String> {
    let Some(value) = value.filter(|value| !value.is_empty()) else {
        return Err(format!(
            "{TRUST_CLEAN_BIN} is unset. This gate cross-checks a `clean` executable built from \
             the pinned first-party/clean, and it never searches for one: build it from the \
             repository root with\n    {CLEAN_BUILD_RECIPE}\nand set {TRUST_CLEAN_BIN} to the \
             executable cargo reports (the slow.clean-binary-proof-gates harness row does both). \
             The proofs themselves are checked without a binary by lean_front_door_gate and \
             clean_proof_obligations."
        ));
    };
    let path = PathBuf::from(value);
    if is_executable_file(&path) {
        Ok(path)
    } else {
        Err(format!(
            "{TRUST_CLEAN_BIN}={} is not an executable file; build one with\n    \
             {CLEAN_BUILD_RECIPE}",
            path.display()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unset_or_empty_trust_clean_bin_is_an_error_naming_the_recipe() {
        for value in [None, Some(OsString::new())] {
            let why = clean_bin_from(value).expect_err("no binary must be an error");
            assert!(why.contains("TRUST_CLEAN_BIN is unset") && why.contains(CLEAN_BUILD_RECIPE));
        }
    }

    #[test]
    fn a_trust_clean_bin_naming_no_executable_is_an_error() {
        let dir = tempfile::tempdir().expect("tempdir");
        let missing = dir.path().join("no-such-clean");
        for value in [missing.as_os_str(), dir.path().as_os_str()] {
            let why = clean_bin_from(Some(value.to_owned())).expect_err("not an executable");
            assert!(why.contains("is not an executable file"), "{why}");
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let plain = dir.path().join("clean");
            std::fs::write(&plain, b"").expect("write stand-in");
            assert!(clean_bin_from(Some(plain.clone().into_os_string())).is_err());
            std::fs::set_permissions(&plain, std::fs::Permissions::from_mode(0o755))
                .expect("chmod");
            assert_eq!(clean_bin_from(Some(plain.clone().into_os_string())), Ok(plain));
        }
    }
}
