// trust-integration-tests/tests/real_kernel_fn_trust_loop.rs
//
// TRUST -> CLEAN loop closure on REAL clean-kernel functions — the
// self-verification milestone in miniature. Trust proves a safety property of a
// LITERAL clean-kernel Rust function, and the property is re-checked by Clean's
// OWN kernel (`clean_kernel::TypeChecker::check_type(term, False)`, the de
// Bruijn criterion) with the SMT solver OUTSIDE the trusted base.
//
// Pipeline exercised — no hand-authored MIR; the real rustc fork extracts it:
//
//   literal kernel fn source
//     -> Trust rustc fork (MIR extraction via -Ztrust-dump=mir:<dir>)
//     -> trust_vcgen::generate_vcs        (safety VC: div/rem-by-zero)
//     -> trust_certify::certify_violation (ay refutes + clean kernel re-checks)
//     -> ProofEvidence::CleanCic          (kernel-checked term : False)
//
// The two functions are copied BYTE-IDENTICALLY from clean-kernel (only
// pub(crate) -> pub so the verify pass keeps them):
//
//   nat_gcd:          clean-kernel/src/env/native_reducers_bool_ext.rs:84
//                     Euclidean GCD; the `a % b` is guarded by `while b != 0`.
//   round_up_to_next: clean-kernel/src/tc/heartbeat_profiler/types.rs:178
//                     `value / step` is guarded by `if step == 0 { return }`.
//
// EXPECTED (verified with the Trust stage2 rustc + clean@f9f8024d):
//   * round_up_to_next's DivisionByZero VC(s) CLOSE — certify_violation returns
//     ProofEvidence::CleanCic (the clean kernel re-checked `term : False`).
//   * nat_gcd's RemainderByZero VC(s) FAIL CLOSED (None) — the loop's carried
//     modulo has no invariant, so the divisor's non-zeroness is not provable;
//     the pipeline refuses to certify and emits NO false Certified.
//
// Requires: a built Trust rustc fork (TRUST_RUSTC or build/*/stage{1,2}/bin/rustc).
// SKIPS (does not fail) when the fork is not present.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::ProofEvidence;
use trust_types::VerifiableFunction;

const KERNEL_FN_SOURCE: &str = r#"
/// Euclidean GCD for u64.  clean-kernel/src/env/native_reducers_bool_ext.rs:84
pub fn nat_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Round `value` up to the next strictly-greater multiple of `step`.
/// clean-kernel/src/tc/heartbeat_profiler/types.rs:178
pub fn round_up_to_next(value: u64, step: u64) -> u64 {
    if step == 0 {
        return value;
    }
    let next_boundary = (value / step).saturating_add(1).saturating_mul(step);
    next_boundary.max(step)
}
"#;

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <repo>/crates/trust-integration-tests
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repo-root grandparent")
        .to_path_buf()
}

fn find_trust_rustc() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("TRUST_RUSTC") {
        let p = PathBuf::from(p);
        if p.is_file() {
            return Some(p);
        }
    }
    let root = repo_root();
    [
        "build/aarch64-apple-darwin/stage2/bin/rustc",
        "build/aarch64-apple-darwin/stage1/bin/rustc",
        "build/x86_64-apple-darwin/stage2/bin/rustc",
        "build/x86_64-unknown-linux-gnu/stage2/bin/rustc",
        "build/host/stage1/bin/rustc",
    ]
    .iter()
    .map(|c| root.join(c))
    .find(|p| p.is_file())
}

fn extract_kernel_fn_mir(rustc: &Path) -> Vec<VerifiableFunction> {
    let tmp = tempfile::tempdir().expect("tempdir");
    let src = tmp.path().join("kernel_fns.rs");
    std::fs::write(&src, KERNEL_FN_SOURCE).expect("write source");
    let dump = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump).expect("mkdir dump");

    let output = Command::new(rustc)
        .env_remove("TRUST_DUMP_MIR")
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO")
        .arg("-Z")
        .arg(format!("trust-dump=mir:{}", dump.display()))
        .args(["-Z", "trust-verify-output=json"])
        .args(["--edition", "2021", "--crate-type", "lib"])
        .arg("-o")
        .arg(tmp.path().join("kernel_fns.rlib"))
        .arg(&src)
        .output()
        .expect("invoke trust rustc fork");
    assert!(
        output.status.success(),
        "fork compile failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut functions = Vec::new();
    for entry in std::fs::read_dir(&dump).expect("read dump").flatten() {
        let path = entry.path();
        if path.extension().is_some_and(|e| e == "json") {
            let json = std::fs::read_to_string(&path).expect("read fixture");
            functions.push(serde_json::from_str(&json).expect("parse VerifiableFunction"));
        }
    }
    functions
}

#[test]
fn real_kernel_fn_trust_clean_loop_closes() {
    let Some(rustc) = find_trust_rustc() else {
        eprintln!(
            "SKIPPING: no Trust rustc fork found. Build with `./x.py build --stage 2` \
             or set TRUST_RUSTC=/path/to/rustc"
        );
        return;
    };
    eprintln!("Trust rustc fork: {}", rustc.display());

    let functions = extract_kernel_fn_mir(&rustc);
    assert!(!functions.is_empty(), "fork extraction produced no VerifiableFunction fixtures");
    eprintln!("Extracted MIR for {} kernel functions", functions.len());

    let mut minted = 0usize; // Some(CleanCic): clean kernel re-checked term:False at MINT
    let mut fail_closed = 0usize; // None: unsupported/SAT — correctly NOT certified
    let mut total = 0usize;

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        eprintln!("\n== {} -> {} VC(s) ==", func.name, vcs.len());
        total += vcs.len();

        for vc in &vcs {
            eprint!("  [{:?}] ... ", vc.kind);
            // MINT: ay refutes the violation, then the REAL clean kernel
            // re-checks the reconstructed term inhabits False (+ serialized
            // round-trip). Some(..) => the loop CLOSED; SMT is outside the TCB.
            let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) =
                trust_certify::certify_violation(&vc.formula)
            else {
                eprintln!("NOT certified (unsupported / SAT) -> fail-closed, no false Certified");
                fail_closed += 1;
                continue;
            };
            assert!(!term.is_empty() && !context.is_empty(), "CleanCic term/context nonempty");
            minted += 1;
            eprint!("CLOSED (kernel-checked mint, term={}B)", term.len());

            // If this VC lands in the QF_LIA order-atom fragment, the consumer-side
            // offline re-checker reconstructs it and a tampered term is rejected.
            if trust_certify::recheck_cleancic(&term, &context, &lineage, &vc.formula) {
                let mut tampered = term.clone();
                tampered[0] ^= 0xff;
                assert!(
                    !trust_certify::recheck_cleancic(&tampered, &context, &lineage, &vc.formula),
                    "tampered term must fail the offline kernel re-check (fail-closed)"
                );
                eprint!(" + offline recheck OK + tamper REJECTED");
            }
            eprintln!();
        }
    }

    eprintln!("\n=== TRUST->CLEAN loop on LITERAL clean-kernel functions ===");
    eprintln!("  VCs total: {total}");
    eprintln!("  CLOSED (kernel-checked mint): {minted}   <- the milestone (SMT outside TCB)");
    eprintln!("  fail-closed (None, no false Certified): {fail_closed}");

    // The milestone: at least one VC from a LITERAL kernel function is
    // kernel-re-checked by the clean kernel (Certified with SMT outside the TCB).
    assert!(
        minted > 0,
        "loop did NOT close: 0 of {total} VCs kernel-checked at mint on literal kernel fns"
    );
}
