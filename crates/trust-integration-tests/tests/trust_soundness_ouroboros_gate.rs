//! The ouroboros gate, wired into the Trust build.
//!
//! `proofs/trust-soundness/*.lean` is the Trust-owned, machine-checked proof
//! corpus that Trust's discharge encoding is sound (`realPanics ⊆ models`), plus
//! the per-class soundness arms and the declaration-marker / UnsupportedMir
//! exhaustiveness bricks. This test kernel-checks every file by shelling out to
//! a `clean` binary built from the pinned `first-party/clean` submodule, so the
//! apex proofs are reproducible from a Trust checkout, not stranded in a
//! separate working clone. Every test run kernel-checks the corpus in process,
//! through `lean_front_door_gate`; this binary cross-check re-verifies it only
//! under `slow.clean-binary-proof-gates` (`--ignored`, with `TRUST_CLEAN_BIN`
//! set).
//!
//! This lane measures the BINARY, not the corpus: its subject is the `clean`
//! executable `TRUST_CLEAN_BIN` names. The corpus's authority is
//! `lean_front_door_gate`, which checks the same files through the kernel
//! crates linked into this test binary, unconditionally and at the pinned
//! `first-party/clean` source revision. Read a pass here as "a `clean` built
//! from the pin agrees", never as "the proofs were checked". It is `#[ignore]`d
//! and runs only under `slow.clean-binary-proof-gates`, which builds `clean`
//! from the submodule at its pin and names it in `TRUST_CLEAN_BIN`; selected
//! without it, it panics with the build recipe. (Until 2026-10-09 it searched
//! for a binary and passed with a NOTICE when it found none.)

use std::path::Path;
use std::process::Command;

use trust_integration_tests::clean_test_support::require_clean_bin;

/// Floor on the corpus size, so an emptied or clobbered proof directory fails
/// instead of vacuously passing. Kept BELOW the current count: a floor equal to
/// it only catches a total wipe and needs editing every time a proof lands.
const MIN_PROOF_FILES: usize = 30;

#[test]
#[ignore = "needs TRUST_CLEAN_BIN (slow.clean-binary-proof-gates)"]
fn trust_soundness_ouroboros_gate() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/trust-soundness");
    let dir = dir
        .canonicalize()
        .unwrap_or_else(|e| panic!("trust-soundness proof corpus {dir:?} not found: {e}"));

    let bin = require_clean_bin();

    let mut files = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("read proofs/trust-soundness") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            files.push(path);
        }
    }
    files.sort();

    assert!(
        files.len() >= MIN_PROOF_FILES,
        "expected the Trust-owned trust-soundness proof corpus (>= {MIN_PROOF_FILES} files), \
         found {} in {}",
        files.len(),
        dir.display()
    );

    let mut failures = Vec::new();
    for path in &files {
        let output = Command::new(&bin)
            .arg("check")
            .arg(path)
            .output()
            .unwrap_or_else(|e| panic!("failed to run clean checker on {path:?}: {e}"));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        // clean prints "  N passed, M failed"; success requires exit 0 and zero failures.
        let ok = output.status.success()
            && stdout.contains(" 0 failed")
            && !stdout.contains("error:")
            && !stderr.contains("panicked");
        if !ok {
            failures.push(format!(
                "OUROBOROS GATE BROKEN: {} no longer kernel-checks\n--- stdout ---\n{}\n--- stderr ---\n{}",
                path.display(),
                stdout.trim(),
                stderr.trim()
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} proofs failed:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n\n")
    );

    eprintln!(
        "OUROBOROS GATE GREEN: {} Trust-soundness proofs kernel-checked by clean ({})",
        files.len(),
        bin.display()
    );
}
