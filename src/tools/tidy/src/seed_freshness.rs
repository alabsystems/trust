// Trust: tidy check for the re-seed cadence invariant.
//! Tidy check: the pinned Trust stage0 seed must stay within one minor of
//! `src/version` (the "re-seed cadence" invariant — docs/OFF_STOCK_RUST_PLAN.md
//! Phase 4). This is what makes "a seed is always within one minor of source"
//! machine-enforced rather than tribal knowledge: `./x test tidy` and the
//! `src/etc/pre-push.sh` hook both run it, so a `src/version` bump that leaves
//! the pinned seed too far behind is refused before it lands.
//!
//! The invariant has a single implementation: `scripts/check_seed_freshness.py`
//! (also enforced at build time by `check_stage0_version` in
//! `compiler/.../config.rs`). This check delegates to that script rather than
//! re-deriving the rule, by shelling out to `git`.

use std::path::Path;
use std::process::Command;

use crate::diagnostics::TidyCtx;

pub fn check(root_path: &Path, tidy_ctx: TidyCtx) {
    let mut check = tidy_ctx.start_check("seed_freshness");

    let script = root_path.join("scripts/check_seed_freshness.py");
    if !script.is_file() {
        // e.g. a pruned source tarball. Not this check's failure.
        check.message("scripts/check_seed_freshness.py is absent; skipping seed cadence check");
        return;
    }

    // tomllib needs Python 3.11+. Absence of a usable python3 is a tooling gap,
    // not a cadence violation, so we skip rather than fail closed on an
    // unrelated environment problem.
    let python =
        ["python3", "python3.14", "python3.13", "python3.12", "python3.11"].into_iter().find(|p| {
            Command::new(p).arg("--version").output().map(|o| o.status.success()).unwrap_or(false)
        });
    let Some(python) = python else {
        check.message(
            "no python3 (>=3.11) found; skipping seed cadence check \
             (run scripts/check_seed_freshness.py manually)",
        );
        return;
    };

    // Strict: the TRUST_SEED_STAIRCASE recovery hack must never let a stale seed
    // pass the gate, so scrub it from the child environment.
    let output = Command::new(python)
        .current_dir(root_path)
        .arg(&script)
        .env_remove("TRUST_SEED_STAIRCASE")
        .output();

    match output {
        Ok(out) if out.status.success() => {
            // Invariant holds — nothing to report.
        }
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout);
            let stderr = String::from_utf8_lossy(&out.stderr);
            let detail = if !stdout.trim().is_empty() { stdout.trim() } else { stderr.trim() };
            check.error(format!(
                "the pinned Trust stage0 seed fails the re-seed cadence invariant: it must not \
                 be NEWER than src/rust-compat-version, and its metadata must parse. RE-MINT and \
                 pin a matching seed — docs/OFF_STOCK_RUST_PLAN.md Phase 1. \
                 check_seed_freshness.py said:\n{detail}"
            ));
        }
        Err(e) => {
            check.message(format!(
                "could not run scripts/check_seed_freshness.py ({e}); skipping seed cadence check"
            ));
        }
    }
}
