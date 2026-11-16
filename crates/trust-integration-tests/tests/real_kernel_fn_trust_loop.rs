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
// EXPECTED (measured 2026-09-17 with the Trust stage1 rustc):
//   * round_up_to_next's DivisionByZero VC CLOSES — certify_violation returns
//     ProofEvidence::CleanCic (the clean kernel re-checked `term : False`).
//   * nat_gcd's two RemainderByZero VCs (the assert row and the `Rem` statement
//     row) CLOSE too: both carry the loop guard `_6 == (_3 != 0)` at the divisor
//     version the remainder reads. Before the trust-vcgen fix the statement row
//     lost that guard to the later `b = ..` write and was falsely refuted.
//   * The strict default compile of this source SUCCEEDS (asserted below).
//
// Requires: a Trust rustc fork that CONTAINS the trust-vcgen fix the strict
// compile pins (LOOP_GUARD_FIX, d8c8b7d29a, 2026-09-17), resolved by
// trust_integration_tests::trust_rustc::require_trust_rustc(Some(LOOP_GUARD_FIX)).
// TRUST_RUSTC is measured as given, whatever its age; a TRUST_RUSTC that names no
// executable fails the test rather than falling back to a discovered one. A
// compiler found under build/*/stage{1,2}/bin/rustc is passed over when its
// `-vV` commit-hash and this checkout's history show it PREDATES the fix: it
// fails nat_gcd's row `:1` because of its age, not because of this tree.
// Measured 2026-09-29 on one host: the discovered stage2 (248a9f1dd,
// 2026-09-14) and the installed seal trustc (321aaeda7, forked from main at
// 4d972edcfd on 2026-09-13) both predate the fix and both fail "1
// obligation(s) were not proved". The stage1 beside them (b18797f54,
// 2026-09-28) contains it and proves 3 of 3. Before this check the search took
// stage2 first, so the test was red there against a two-week-old compiler. A
// compiler whose age cannot be established (no commit-hash, or a revision this
// clone lacks) is still measured, and its identity goes in the failure message.
//
// The loop test runs with the crate's other tests (TRUST_RUSTC-1, 2026-11-03:
// it was #[ignore]d and run only by the slow.real-mir-trust-clean-loops harness
// row, so a gate whose build/ held a compiler still never ran it). Where no fork
// qualifies it PANICS with how to build one; the land gate's crates-tests leg
// hands it this tree's stage 1 as TRUST_RUSTC. Until 2026-10-09 it said NOT RUN
// and passed without evidence instead, in every fresh clone and worktree, and
// whenever every fork found predated the fix.
// The resolver's own rules are pinned by the unit tests at the end of this
// file, which need no compiler and run everywhere.
//
// The vcgen half of the fix does not depend on this test:
// crates/trust-vcgen/tests/loop_guarded_rem_realmir.rs checks nat_gcd's checked-in
// MIR, and its unguarded mutant, on every run.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::process::Command;

use trust_integration_tests::trust_rustc::{
    Provenance, TrustRustc, commit_from_version_verbose, explicit_trust_rustc, find_repo_root,
    lent_output, provenance, provenance_from_exit, require_trust_rustc, select,
};
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

/// The trust-vcgen fix the strict compile pins: "a statement row lost its loop
/// guard to a write AFTER its own read". A fork built without it fails nat_gcd's
/// RemainderByZero row `:1`, by construction.
const LOOP_GUARD_FIX: &str = "d8c8b7d29ac25490ae44a106c642fe76ec91abc0";

fn extract_kernel_fn_mir(rustc: &TrustRustc) -> Vec<VerifiableFunction> {
    let tmp = tempfile::tempdir().expect("tempdir");
    let src = tmp.path().join("kernel_fns.rs");
    std::fs::write(&src, KERNEL_FN_SOURCE).expect("write source");
    let dump = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump).expect("mkdir dump");

    let output = lent_output(
        Command::new(&rustc.path)
            .env_remove("TRUST_DUMP_MIR")
            .env_remove("CARGO_TARGET_DIR")
            .env_remove("CARGO")
            .arg("-Z")
            .arg(format!("trust-dump=mir:{}", dump.display()))
            .args(["-Z", "trust-verify-output=json"])
            // STRICT default policy, on purpose. Both functions are safe, so the
            // fork compile must succeed without `-Ztrust-policy=advisory`: `nat_gcd`
            // (`a % b` under `while b != 0`) used to FAIL here on its RemainderByZero
            // row `:1`. The loop guard `_6 == (_3 != 0)` was dropped by a later
            // write in the loop body. That was a false refutation of valid Rust,
            // fixed in trust-vcgen (`v2_live_path_defs_at_point`,
            // `tests/loop_guarded_rem_realmir.rs`). A regression fails this
            // assertion instead of being hidden by the survey lane.
            // (`-Ztrust-verify=off` is refused for `-Ztrust-dump=mir:<dir>`,
            // which needs batteries-on verification.)
            .args(["--edition", "2021", "--crate-type", "lib"])
            .arg("-o")
            .arg(tmp.path().join("kernel_fns.rlib"))
            .arg(&src),
    )
    .expect("invoke trust rustc fork");
    assert!(
        output.status.success(),
        "fork compile failed with {}:\n{}",
        rustc.identity(),
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
    let rustc = require_trust_rustc(Some(LOOP_GUARD_FIX));

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

/// The fix's parent: the last revision whose fork fails nat_gcd's row `:1`.
const LOOP_GUARD_FIX_PARENT: &str = "e14109a23898be69b2443cfd6312c1b5922a8123";

/// A discovered fork whose revision contains the flag surface and stands in
/// `provenance` to LOOP_GUARD_FIX.
fn candidate(name: &str, provenance: Provenance) -> TrustRustc {
    TrustRustc {
        path: PathBuf::from(name),
        commit: Some(name.to_string()),
        surface: Provenance::Contains,
        min_fix: Some((LOOP_GUARD_FIX.to_string(), provenance)),
        behind_head: None,
    }
}

fn measured(selection: Result<TrustRustc, String>) -> String {
    match selection {
        Ok(rustc) => rustc.path.display().to_string(),
        Err(why) => panic!("expected a fork to be measured, got: {why}"),
    }
}

fn refused(selection: Result<TrustRustc, String>) -> String {
    match selection {
        Ok(rustc) => panic!("expected no fork to be measured, got: {}", rustc.identity()),
        Err(why) => why,
    }
}

// Regression (2026-09-29 review): a TRUST_RUSTC naming no file was dropped by a
// `.filter(is_file)`, so the test measured a discovered fork in its place, or
// said NOT RUN because "TRUST_RUSTC is unset" while it was set.
#[test]
fn a_trust_rustc_that_names_no_file_is_an_error_not_a_fallback() {
    assert_eq!(explicit_trust_rustc(None), Ok(None));
    assert_eq!(explicit_trust_rustc(Some("".into())), Ok(None));

    let dir = tempfile::tempdir().expect("tempdir");
    let missing = dir.path().join("no-such-rustc");
    let why = explicit_trust_rustc(Some(missing.clone().into_os_string()))
        .expect_err("a missing TRUST_RUSTC must be an error");
    assert!(why.contains("TRUST_RUSTC=") && why.contains("no-such-rustc"), "{why}");
    // A directory is not a compiler either.
    assert!(explicit_trust_rustc(Some(dir.path().as_os_str().to_owned())).is_err());
    // cargo runs this binary in the package directory, so a repo-relative value
    // misses, and the error says what it was resolved against.
    let why = explicit_trust_rustc(Some("build/host/stage1/bin/no-such-rustc".into()))
        .expect_err("a relative TRUST_RUSTC naming nothing must be an error");
    assert!(why.contains("relative path") && why.contains("absolute"), "{why}");

    let present = dir.path().join("rustc");
    std::fs::write(&present, b"").expect("write stand-in");
    // A file nobody can execute is not a compiler either (since 2026-10-09, when
    // this resolver became the one e2e_real_rustc.rs already used).
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert!(explicit_trust_rustc(Some(present.clone().into_os_string())).is_err());
        std::fs::set_permissions(&present, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    }
    assert_eq!(explicit_trust_rustc(Some(present.clone().into_os_string())), Ok(Some(present)));
}

// Regression (2026-09-29): the search took build/*/stage2 before stage1, and
// nothing asked how old either was. On the measured host stage2 predated the
// fix and stage1 contained it, so the test measured the stale one and was red.
#[test]
fn a_fork_that_predates_the_loop_guard_fix_is_never_the_one_discovered() {
    use Provenance::{Contains, Predates, Unknown};

    // The measured host: a stale stage2 ahead of a current stage1.
    assert_eq!(
        measured(select(None, vec![candidate("stage2", Predates), candidate("stage1", Contains)])),
        "stage1"
    );
    // Only stale forks: nothing is measured, and that is an ERROR (it was NOT
    // RUN and a pass until 2026-10-09) whose reason names each fork and the fix.
    let reason = refused(select(None, vec![candidate("stage2", Predates)]));
    assert!(reason.contains("stage2") && reason.contains(LOOP_GUARD_FIX), "{reason}");
    // No fork at all: an error saying how to build one.
    let reason = refused(select(None, Vec::new()));
    assert!(
        reason.contains("No executable Trust rustc found")
            && reason.contains("x.py build --stage 1"),
        "{reason}"
    );
    // An age that cannot be established is measured, not dropped.
    assert_eq!(
        measured(select(None, vec![candidate("stage2", Unknown("no hash".into()))])),
        "stage2"
    );
    // An explicit TRUST_RUSTC is measured whatever its age.
    assert_eq!(
        measured(select(
            Some(candidate("explicit", Predates)),
            vec![candidate("stage1", Contains)]
        )),
        "explicit"
    );
    // A fork older than the flag surface is passed over too, whatever it
    // says about the fix: it cannot parse the command line.
    let mut no_surface = candidate("stage1", Contains);
    no_surface.surface = Predates;
    assert_eq!(measured(select(None, vec![no_surface, candidate("stage2", Contains)])), "stage2");
}

#[test]
fn only_a_negative_ancestry_answer_marks_a_fork_as_stale() {
    assert_eq!(provenance_from_exit(Some(0), ""), Provenance::Contains);
    assert_eq!(provenance_from_exit(Some(1), ""), Provenance::Predates);
    for code in [Some(128), Some(2), None] {
        assert!(
            matches!(provenance_from_exit(code, "fatal"), Provenance::Unknown(_)),
            "exit {code:?} must not be read as an answer"
        );
    }

    // Against this checkout's own history. A clone without the fix commit (a
    // history-rewritten snapshot) answers Unknown for both, which is still
    // neither of the wrong answers asserted against here.
    let root = find_repo_root();
    let fix = provenance(&root, LOOP_GUARD_FIX, Some(LOOP_GUARD_FIX));
    let parent = provenance(&root, LOOP_GUARD_FIX, Some(LOOP_GUARD_FIX_PARENT));
    assert_ne!(fix, Provenance::Predates, "a revision contains itself");
    assert_ne!(parent, Provenance::Contains, "the fix's parent cannot contain it");
    let knows_fix = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["cat-file", "-e", &format!("{LOOP_GUARD_FIX}^{{commit}}")])
        .status()
        .is_ok_and(|s| s.success());
    if knows_fix {
        assert_eq!(fix, Provenance::Contains);
        assert_eq!(parent, Provenance::Predates);
    }
    assert!(matches!(provenance(&root, LOOP_GUARD_FIX, None), Provenance::Unknown(_)));
}

#[test]
fn the_fork_commit_is_read_from_rustc_vv_and_unknown_is_no_commit() {
    // The measured stage2's `-vV`, verbatim but for the LLVM line.
    let stage2 = "rustc 1.99.0-dev (248a9f1dd 2026-09-14)\nbinary: rustc\n\
                  commit-hash: 248a9f1ddb4f63811fd71e5ea953c6b98ba3b04d\n\
                  commit-date: 2026-09-14\nhost: aarch64-apple-darwin\n\
                  release: 1.99.0-dev\ntrust: 0.1.0\n";
    assert_eq!(
        commit_from_version_verbose(stage2).as_deref(),
        Some("248a9f1ddb4f63811fd71e5ea953c6b98ba3b04d")
    );
    assert_eq!(commit_from_version_verbose("rustc 1.99.0-dev\ncommit-hash: unknown\n"), None);
    assert_eq!(commit_from_version_verbose("rustc 1.99.0-dev\ncommit-date: 2026-09-17\n"), None);
}
