//! R107-PRINT-GAP-PIN-1: a `println!` program keeps its `std-print-dispatch` gap
//! class, which pins that production's bridge entry forwards the compiler's
//! authenticated sysroot-member set to R107.
//!
//! R107 charges `src != 0` before a cast into `NonNull`/`NonZero` in every lowered
//! body except a bundled member the compiler authenticated as a foreign
//! `core`/`alloc`/`std` body. Production lowers through the compiler-context bridge
//! entry (`lower_to_trust_ir_functions_with_compiler_context`, selected by the
//! paired-condvar crate certificate), which takes that set from trust_verify's
//! `compiler_authenticated_sysroot_members`. If the entry dropped the set, R107 would
//! charge the std members every `format_args!` bundles
//! (`core::fmt::Arguments::from_str`, `core::fmt::rt::Argument::new_display`). Their
//! unlinked asserts fail `panic_freedom_fold_is_exclusive_for`, so the
//! whole-function panic-freedom row would lose its `std-print-dispatch` class and
//! the program would read as having an unclassified panic source
//! (docs/DECISION_QUEUE.md BMC-LANE-1, third hostile review). No unit test can mint
//! the certificate that selects that entry, and the only other pin, the e2e program
//! r09, runs in no land-gate leg.
//!
//! The class is read from the compiler's own wire (`-Ztrust-verify-output=json`,
//! the raw `TRUST_JSON:` lines), on `main`'s row that names the print backend. The
//! negative control is r28's shape: a user `assert!` folded under the same
//! aggregate must leave the row UNCLASSED, so this test cannot pass on a class
//! stamped on every print row.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path};

/// Set by compiletest's `--trust-vanilla` replay, which runs the stock rustc.
/// That build has no verifier and writes no wire, so there is nothing to assert.
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

const GAP_CLASS: &str = "\"gap_class\":\"std-print-dispatch\"";
const MAIN_ROW: &str = "\"function\":\"main::main\"";

/// The raw `TRUST_JSON:` transport lines a verifying build of `source` writes, and
/// its exit status.
fn wire(trustc: &PathBuf, label: &str, source: &str) -> (Vec<String>, Option<i32>) {
    let file = format!("{label}.rs");
    rfs::write(&file, source);
    let output = cmd(trustc)
        .args([
            "--edition=2021",
            "--crate-name=main",
            "-Ztrust-verify=on",
            "-Ztrust-verify-output=json",
            "-o",
            &format!("{label}-bin"),
            &file,
        ])
        .run_unchecked();
    let stderr = output.stderr_utf8();
    let lines: Vec<String> =
        stderr.lines().filter(|line| line.starts_with("TRUST_JSON:")).map(str::to_string).collect();
    assert!(!lines.is_empty(), "{label}: the verifying build must write its wire:\n{stderr}");
    (lines, output.status().code())
}

fn classed_rows(lines: &[String]) -> Vec<&String> {
    lines.iter().filter(|line| line.contains(MAIN_ROW) && line.contains(GAP_CLASS)).collect()
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    for (label, source) in [
        ("hello", "fn main() { println!(\"hello\"); }\n"),
        ("display", "fn main() { println!(\"{}\", 42); }\n"),
    ] {
        let (lines, status) = wire(&trustc, label, source);
        assert_eq!(status, Some(0), "{label}: the default policy reports the print gap");
        let classed = classed_rows(&lines);
        assert_eq!(
            classed.len(),
            1,
            "{label}: `main`'s print row must carry the `std-print-dispatch` class (R107 \
             must not charge the std members `format_args!` bundles):\n{}",
            lines.join("\n")
        );
        assert!(
            !classed[0].contains("\"outcome\":\"proved\""),
            "{label}: a gap row is never proved: {}",
            classed[0]
        );
    }

    // r28's shape: one user `assert!` folded under the print aggregate.
    let (lines, _) = wire(
        &trustc,
        "folded_assert",
        "fn main() { let n = std::env::args().count(); assert!(n > 7); println!(\"hello\"); }\n",
    );
    assert!(
        classed_rows(&lines).is_empty(),
        "a user `assert!` folded under the print row leaves it unclassed:\n{}",
        lines.join("\n")
    );
}
