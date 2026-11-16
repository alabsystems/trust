//! The codegen-equivalence gate (G16): kernel-checked proven-output bedrock.
//!
//! `proofs/codegen-equivalence/*.lean` holds machine-checked proofs that the
//! VALUE SEMANTICS of the machine instructions trust-cg emits equal the IR
//! semantics they implement — proved symbolically (∀ inputs, by induction over
//! the word width) over a fixed-width `Word = List Bool` model, with the
//! machine-side and IR-side operations SEPARATELY defined and then proven equal
//! (not X=X by construction).
//!
//! This is the kernel-grade ([PROVED]) counterpart of the runtime proven-output
//! certificates in `trust-cg-bridge` (which are [VALIDATED] — discharged by the
//! `ay` SMT solver as an oracle): here the equivalence is re-checked by the
//! `clean` CIC kernel, so `ay` is not in the trusted base for the proofs that
//! land here. Like the ouroboros gate, it shells out to a `clean` binary built
//! from the pinned `first-party/clean` submodule, so the proofs are reproducible
//! from a Trust checkout. Every test run kernel-checks them in process, through
//! `lean_front_door_gate`; this binary cross-check re-verifies them only under
//! `slow.clean-binary-proof-gates` (`--ignored`, with `TRUST_CLEAN_BIN` set).
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
/// instead of vacuously passing.
const MIN_PROOF_FILES: usize = 2;

#[test]
#[ignore = "needs TRUST_CLEAN_BIN (slow.clean-binary-proof-gates)"]
fn codegen_equivalence_gate() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/codegen-equivalence");
    let dir = dir
        .canonicalize()
        .unwrap_or_else(|e| panic!("codegen-equivalence proof corpus {dir:?} not found: {e}"));

    let bin = require_clean_bin();

    let mut files = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("read proofs/codegen-equivalence") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            files.push(path);
        }
    }
    files.sort();

    assert!(
        files.len() >= MIN_PROOF_FILES,
        "expected the codegen-equivalence proof corpus (>= {MIN_PROOF_FILES} files), \
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
                "CODEGEN-EQUIVALENCE GATE BROKEN: {} no longer kernel-checks\n--- stdout ---\n{}\n--- stderr ---\n{}",
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
        "CODEGEN-EQUIVALENCE GATE GREEN: {} kernel-checked proven-output equivalence proofs ({})",
        files.len(),
        bin.display()
    );
}
