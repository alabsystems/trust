//! The ouroboros gate, wired into the Trust build.
//!
//! `proofs/trust-soundness/*.lean` is the Trust-owned, machine-checked proof
//! corpus that Trust's discharge encoding is sound (`realPanics ⊆ models`), plus
//! the per-class soundness arms and the declaration-marker / UnsupportedMir
//! exhaustiveness bricks. This test kernel-checks every file by shelling out to
//! the `clean` binary Trust builds from the pinned `first-party/clean` submodule
//! — so the apex proofs are reproducible from a Trust checkout and re-verified on
//! every test run, not stranded in a separate working clone.
//!
//! This lane measures the BINARY, not the corpus. Its subject is whichever
//! `clean` executable is discoverable, which may be absent or stale, so it
//! prints a notice and passes when none is found. That skip is not a hole in
//! the proof coverage: `lean_front_door_gate` checks the same corpus through
//! the kernel crates linked into this test binary, unconditionally and at the
//! pinned `first-party/clean` source revision. Read a pass here as "the
//! discovered checker agrees", never as "the proofs were checked".

use std::path::Path;
use std::process::Command;

use trust_integration_tests::clean_test_support::clean_checker_path;

/// Floor on the corpus size, so an emptied or clobbered proof directory fails
/// instead of vacuously passing. Kept BELOW the current count: a floor equal to
/// it only catches a total wipe and needs editing every time a proof lands.
const MIN_PROOF_FILES: usize = 30;

#[test]
fn trust_soundness_ouroboros_gate() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/trust-soundness");
    let dir = dir
        .canonicalize()
        .unwrap_or_else(|e| panic!("trust-soundness proof corpus {dir:?} not found: {e}"));

    let Some(bin) = clean_checker_path() else {
        eprintln!(
            "NOTICE: no `clean` checker discoverable — the binary cross-check over {} did not \
             run. The corpus itself is still gated by `lean_front_door_gate`, which checks it \
             with the linked kernel and cannot skip.",
            dir.display()
        );
        return;
    };
    eprintln!("clean checker: {}", bin.display());

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
