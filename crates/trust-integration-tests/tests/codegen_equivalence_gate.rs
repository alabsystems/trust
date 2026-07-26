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
//! land here. Like the ouroboros gate, it shells out to the `clean` binary Trust
//! builds from the pinned `first-party/clean` submodule, so the proofs are
//! reproducible from a Trust checkout and re-verified on every test run.
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
/// instead of vacuously passing.
const MIN_PROOF_FILES: usize = 2;

#[test]
fn codegen_equivalence_gate() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/codegen-equivalence");
    let dir = dir
        .canonicalize()
        .unwrap_or_else(|e| panic!("codegen-equivalence proof corpus {dir:?} not found: {e}"));

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
