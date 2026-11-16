// Test-only source preparation for the frozen oracle files.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//
// Everything this script writes is consumed only by `#[cfg(test)]` modules. Nothing here may
// fail the production build: a preparation that cannot be made is recorded as a REASON, and the
// test that needs it FAILS with that reason. A missing baseline is a red test, never a vacuous
// green one and never a broken compiler build.
//
// 1. `mir_differential_without_inner_docs.rs` — the CURRENT `src/mir_differential.rs` with its
//    leading `//!` block demoted to `//` so `include!` accepts it
//    (`mir_differential_tailcall_ratification_tests.rs`).
//
// 2. `<stem>_pinned.rs` + `<stem>_current.rs` + `<stem>_pin_meta.rs`, for every row of
//    `REFINEMENT_HARNESSES` — today `src/flip_registry.rs` (stem `flip_registry`),
//    `src/mir_differential.rs` (stem `mir_differential`), and `src/flip.rs` and
//    `src/instance_flip.rs` (stems `flip`, `instance_flip`, read as TEXT only, by the censuses
//    in `flip_refinement_tests.rs`). Each is the frozen file's PRODUCTION
//    SECTION twice: once from the blob `scripts/frozen-files.txt` PINS for that file, read out
//    of git (so the baseline a refinement harness compares against is exactly the ratified one,
//    and moves only when the owner moves the pin), and once from the working tree. The
//    harnesses (`flip_registry_refinement_tests.rs`, `mir_differential_refinement_tests.rs`)
//    compile both and compare them over a corpus — the "REFUSES MORE / NEITHER SAMPLES NOR
//    REFUSES DIFFERENTLY" claims the waiver rows for those files used to make only in prose.
//
//    The production section is everything before the file's inline `#[cfg(test)] mod <name> {`
//    (`mod tests` in flip_registry.rs, `mod session_state_tests` in mir_differential.rs). The
//    cut is by that exact marker, required to occur once, and the module's own closing brace
//    (found by brace matching that skips strings, chars and comments) must end the file —
//    anything after it would be dropped from both halves of the harness, so it is refused
//    (`src/frozen_section_cut.rs`, which carries the cut and its tests); the frozen tests
//    module is cut because a pinned blob's fixtures construct crate types
//    whose field lists have since moved (flip_registry's `CalleeRef`/`Lowered`,
//    mir_differential's `Terminator::Call`), and because a harness is about what the oracle
//    DECIDES, not what its own tests assert.
//
//    Each row's cfg (`trust_frozen_pin_<stem>`) is set only when BOTH instances were prepared.
//    When it is not set, `<stem>_pin_meta.rs` carries `PIN_UNAVAILABLE` with the reason and
//    that harness consists of one test that fails with it. One row failing never disarms the
//    other: each is prepared, and fails, on its own.

use std::path::{Path, PathBuf};
use std::process::Command;

const FROZEN_MANIFEST: &str = "../../scripts/frozen-files.txt";

/// One frozen file a refinement harness compiles twice (pinned and current).
struct RefinementHarness {
    /// Column 1 of its `scripts/frozen-files.txt` row.
    manifest_path: &'static str,
    /// The same file, relative to this crate.
    source: &'static str,
    /// The name of the file's one inline test module, which the cut removes.
    tests_module: &'static str,
    /// OUT_DIR stem, and the `trust_frozen_pin_<stem>` cfg.
    stem: &'static str,
}

const REFINEMENT_HARNESSES: [RefinementHarness; 4] = [
    RefinementHarness {
        manifest_path: "crates/trust-thir-lower/src/flip_registry.rs",
        source: "src/flip_registry.rs",
        tests_module: "tests",
        stem: "flip_registry",
    },
    RefinementHarness {
        manifest_path: "crates/trust-thir-lower/src/mir_differential.rs",
        source: "src/mir_differential.rs",
        tests_module: "session_state_tests",
        stem: "mir_differential",
    },
    // Trust (F2, 2026-09-29): `flip.rs`'s production section, for the CENSUS of its waived
    // movement (`flip_refinement_tests.rs`). Only the text is read; nothing compiles it twice.
    RefinementHarness {
        manifest_path: "crates/trust-thir-lower/src/flip.rs",
        source: "src/flip.rs",
        tests_module: "w3_regression_tests",
        stem: "flip",
    },
    // Trust (F2 rework, 2026-09-29): `instance_flip.rs`'s production section, read as TEXT for
    // the census of its waived movement (the instance lane's spread-argument refusal).
    RefinementHarness {
        manifest_path: "crates/trust-thir-lower/src/instance_flip.rs",
        source: "src/instance_flip.rs",
        tests_module: "tests",
        stem: "instance_flip",
    },
];

// `demote_inner_docs` and `production_section`: one text, compiled here and, as the library's
// `#[cfg(test)] mod frozen_section_cut`, under test — so the cut the tests exercise IS this one.
include!("src/frozen_section_cut.rs");

/// The blob `scripts/frozen-files.txt` pins for `path` — column 2 of the row whose column 1 is
/// exactly `path`. Comment and blank rows are skipped, exactly as the freeze gate skips them.
fn pinned_blob(manifest: &str, path: &str) -> Result<String, String> {
    for row in manifest.lines() {
        let row = row.trim();
        if row.is_empty() || row.starts_with('#') {
            continue;
        }
        let mut cols = row.split('|');
        if cols.next() != Some(path) {
            continue;
        }
        let Some(blob) = cols.next() else {
            return Err(format!("manifest row for {path} has no blob column"));
        };
        if blob.len() != 40 || !blob.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err(format!("manifest row for {path} pins a malformed blob `{blob}`"));
        }
        return Ok(blob.to_string());
    }
    Err(format!("no manifest row pins {path}"))
}

/// `git cat-file blob <sha>` from the crate directory, so git resolves the enclosing checkout.
fn git_blob(manifest_dir: &Path, sha: &str) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(manifest_dir)
        .args(["cat-file", "blob", sha])
        .output()
        .map_err(|e| format!("cannot run git: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "git cat-file blob {sha} failed ({}): {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout).map_err(|e| format!("blob {sha} is not UTF-8: {e}"))
}

/// Both instances of a frozen file's production section, or the first reason one could not be
/// prepared. Returns `(pinned_sha, pinned_production, current_production)`.
fn prepare(
    manifest_dir: &Path,
    harness: &RefinementHarness,
) -> Result<(String, String, String), String> {
    let manifest = std::fs::read_to_string(manifest_dir.join(FROZEN_MANIFEST))
        .map_err(|e| format!("cannot read {FROZEN_MANIFEST}: {e}"))?;
    let sha = pinned_blob(&manifest, harness.manifest_path)?;
    let pinned = git_blob(manifest_dir, &sha)?;
    let pinned = production_section(&pinned, harness.tests_module)
        .map_err(|e| format!("pinned blob {sha}: {e}"))?;
    let current = std::fs::read_to_string(manifest_dir.join(harness.source))
        .map_err(|e| format!("cannot read {}: {e}", harness.source))?;
    let current = production_section(&current, harness.tests_module)
        .map_err(|e| format!("{}: {e}", harness.source))?;
    Ok((sha, pinned, current))
}

fn main() {
    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let manifest_dir = PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );

    // (1) The frozen MIR differential, current source, inner docs demoted.
    const SOURCE: &str = "src/mir_differential.rs";
    println!("cargo:rerun-if-changed={SOURCE}");
    let source = std::fs::read_to_string(SOURCE).expect("read frozen MIR differential source");
    std::fs::write(
        out_dir.join("mir_differential_without_inner_docs.rs"),
        demote_inner_docs(&source),
    )
    .expect("write test-only MIR differential source");

    // (2) Every refinement harness's frozen file, pinned and current, production sections only.
    println!("cargo:rerun-if-changed={FROZEN_MANIFEST}");
    for harness in &REFINEMENT_HARNESSES {
        let stem = harness.stem;
        println!("cargo:rerun-if-changed={}", harness.source);
        println!("cargo:rustc-check-cfg=cfg(trust_frozen_pin_{stem})");
        let meta = match prepare(&manifest_dir, harness) {
            Ok((sha, pinned, current)) => {
                // Whether the pin IS the working tree: the two production sections the harness
                // compiles are byte-equal. A harness witnesses the waived movement only when
                // they differ, and demands the two sides AGREE when they do not (the ratified
                // state) — computed here from the very strings it compiles, so the flag cannot
                // drift from the baseline.
                let pin_is_current = pinned == current;
                std::fs::write(out_dir.join(format!("{stem}_pinned.rs")), pinned)
                    .expect("write pinned production section");
                std::fs::write(out_dir.join(format!("{stem}_current.rs")), current)
                    .expect("write current production section");
                println!("cargo:rustc-cfg=trust_frozen_pin_{stem}");
                format!(
                    "pub const PINNED_BLOB: &str = {sha:?};\npub const PIN_IS_CURRENT: bool = \
                     {pin_is_current};\n"
                )
            }
            Err(reason) => format!("pub const PIN_UNAVAILABLE: &str = {reason:?};\n"),
        };
        std::fs::write(out_dir.join(format!("{stem}_pin_meta.rs")), meta)
            .expect("write pin metadata");
    }
}
