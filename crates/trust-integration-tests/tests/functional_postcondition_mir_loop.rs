// trust-integration-tests/tests/functional_postcondition_mir_loop.rs
//
// TRUST -> CLEAN loop closure on a FUNCTIONAL-correctness postcondition of a
// LITERAL clean-kernel Rust function — the rung ABOVE the safety-VC leaf
// (`real_kernel_fn_trust_loop.rs`, which grounded a div-by-zero SAFETY VC) and
// ABOVE the MODEL-LEVEL checker-core lanes (`trust_certify::checker_core*`,
// which kernel-recheck lemmas over the 6-ctor `KExpr` abstraction, NOT literal
// Rust). Here the property is a FUNCTIONAL postcondition — a first-order integer
// BOUND relating the result to an input, `result >= step`, beyond mere safety —
// and it is proved about the LITERAL Rust function's real MIR, discharged by a
// real clean-kernel-checked proof term.
//
// Pipeline exercised — no hand-authored MIR; the real rustc fork extracts it:
//
//   literal kernel fn source + #[core::contracts::ensures(|r| *r >= step)]
//     -> Trust rustc fork (MIR + contract extraction via -Ztrust-dump=mir:<dir>)
//     -> trust_vcgen::generate_vcs         (a VcKind::Postcondition FUNCTIONAL VC:
//                                           the negated postcondition + body defs,
//                                           with the return-slot version unification
//                                           now INTERNALIZED in vcgen — see NOTE)
//     -> trust_certify::certify_violation  (ay refutes + clean kernel re-checks)
//     -> ProofEvidence::CleanCic           (kernel-checked `term : False`)
//     -> trust_certify::recheck_cleancic   (independent offline kernel re-check)
//
// The function body is copied BYTE-IDENTICALLY from clean-kernel (only
// `pub(crate) -> pub` so the verify pass keeps it; the `#[ensures]` is the
// SPECIFICATION of the property proved, not a change to the code):
//
//   round_up_to_next: clean-kernel/src/tc/heartbeat_profiler/types.rs:178
//                     `next_boundary.max(step)` guarantees `result >= step` on
//                     the step != 0 path (the `.max` spec yields `__ret >= step`).
//
// POSITIVE: round_up_to_next's `result >= step` Postcondition VC on the step != 0
//   path CLOSES — certify_violation returns a CleanCic (the clean kernel re-checked
//   `term : False`), and the serialized payload re-checks offline + rejects a
//   tampered term. The clean CIC kernel is the ONLY trusted component; SMT (ay) is
//   OUTSIDE the TCB.
//
// NEGATIVE CONTROL (no masquerade): round_up_gt states the FALSE postcondition
//   `result > step` — false because `round_up_to_next(0, 5) == 5 == step`. Under
//   the IDENTICAL pipeline + name unification, EVERY one of its Postcondition VCs
//   FAILS CLOSED (certify_violation = None). The discrimination between `>= step`
//   (proved) and `> step` (refused) exactly tracks the real `.max(step)`
//   semantics, witnessing that the discharge is genuine, not vacuous.
//
// NOTE — the return-slot version unification (formerly a test-side stand-in) is
//   now INTERNALIZED in vcgen. vcgen's pipeline-v2 postcondition lane versions the
//   negated postcondition's `_0` at the Return point, where `_0` carries the MERGED
//   reaching-set token of all return predecessors (`_0#s1_0_s6_0`), while the body's
//   return-value pin carries the SINGLE establish-point token of THIS predecessor
//   (`_0#s6_0 = __ret#s5_t`) and the `.max` spec yields `__ret#s5_t >= step`. The two
//   `_0` names denote the same final return value on this per-predecessor VC but did
//   not unify, so the negated postcondition stayed havoc'd and the VC was vacuously
//   SAT (correctly fails closed as-emitted). `trust_vcgen`'s
//   `unify_return_slot_versions` (generate.rs) now unifies every statement-version of
//   the return slot to the pin's version WITHIN the single Return-block VC, so this
//   test consumes the STANDARD pipeline output directly — no stand-in. Soundness is
//   witnessed by the NEGATIVE CONTROL: the SAME internalized unification leaves the
//   FALSE `> step` postcondition unrefuted (`result == step` stays satisfiable).
//
// Requires: a built Trust rustc fork (TRUST_RUSTC or build/*/stage{1,2}/bin/rustc).
// SKIPS (does not fail) when the fork is not present.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::ProofEvidence;
use trust_types::{Formula, VcKind, VerifiableFunction};

/// Byte-identical `round_up_to_next` body + BOTH the true (`>= step`) and false
/// (`> step`) functional postconditions. The `move` closures capture the
/// parameter by value (the contracts feature requires `'static` captures).
const KERNEL_FN_SOURCE: &str = r#"
#![feature(contracts)]
#![allow(dead_code, internal_features)]

/// clean-kernel/src/tc/heartbeat_profiler/types.rs:178 — byte-identical body.
/// FUNCTIONAL postcondition (TRUE): the result is at least `step`.
#[core::contracts::ensures(move |r: &u64| *r >= step)]
pub fn round_up_to_next(value: u64, step: u64) -> u64 {
    if step == 0 {
        return value;
    }
    let next_boundary = (value / step).saturating_add(1).saturating_mul(step);
    next_boundary.max(step)
}

/// NEGATIVE CONTROL: identical body, FALSE postcondition `result > step`
/// (round_up_to_next(0, 5) == 5 == step, so strict `>` fails).
#[core::contracts::ensures(move |r: &u64| *r > step)]
pub fn round_up_gt(value: u64, step: u64) -> u64 {
    if step == 0 {
        return value;
    }
    let next_boundary = (value / step).saturating_add(1).saturating_mul(step);
    next_boundary.max(step)
}
"#;

fn repo_root() -> PathBuf {
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
        .args(["-Z", "trust-verify-level=1"])
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

fn find<'a>(funcs: &'a [VerifiableFunction], name: &str) -> &'a VerifiableFunction {
    funcs.iter().find(|f| f.name == name).unwrap_or_else(|| panic!("missing extracted fn `{name}`"))
}

#[test]
fn functional_postcondition_trust_clean_loop_closes() {
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

    // ---- POSITIVE: round_up_to_next `result >= step` --------------------------
    let pos = find(&functions, "round_up_to_next");
    assert_eq!(
        pos.postconditions,
        vec![Formula::Ge(
            Box::new(Formula::var("_0", trust_types::Sort::Int)),
            Box::new(Formula::var("step", trust_types::Sort::Int)),
        )],
        "the functional bound `result >= step` must be extracted from the literal fn's #[ensures]"
    );

    let mut minted = 0usize;
    for vc in trust_vcgen::generate_vcs(pos) {
        if !matches!(vc.kind, VcKind::Postcondition) {
            continue;
        }
        // STANDARD pipeline output — the return-slot version unification is now
        // internalized in vcgen's postcondition lane (`unify_return_slot_versions`),
        // so no test-side stand-in is applied. The VC is consumed verbatim.
        let Some(ProofEvidence::CleanCic { term, context, lineage, .. }) =
            trust_certify::certify_violation(&vc.formula)
        else {
            continue; // e.g. the step==0 early-return path additionally needs u64-range
        };
        assert!(!term.is_empty() && !context.is_empty(), "CleanCic payload nonempty");
        minted += 1;

        // Consumer-side de Bruijn re-check: rebuild the kernel + hypothesis context
        // from the obligation's own violation atoms and re-run check_type(_, False).
        assert!(
            trust_certify::recheck_cleancic(&term, &context, &lineage, &vc.formula),
            "minted functional CleanCic must re-check offline via the clean kernel"
        );
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !trust_certify::recheck_cleancic(&tampered, &context, &lineage, &vc.formula),
            "tampered functional term must fail the offline kernel re-check (fail-closed)"
        );
    }
    assert!(
        minted > 0,
        "the FUNCTIONAL postcondition `result >= step` did NOT kernel-close on any path \
         of the literal round_up_to_next MIR"
    );
    eprintln!(
        "POSITIVE: round_up_to_next `result >= step` — {minted} Postcondition VC(s) \
               kernel-checked to CleanCic (+ offline recheck + tamper rejected)."
    );

    // ---- NEGATIVE CONTROL: round_up_gt `result > step` (FALSE) ----------------
    let neg = find(&functions, "round_up_gt");
    let mut neg_postcondition_vcs = 0usize;
    for vc in trust_vcgen::generate_vcs(neg) {
        if !matches!(vc.kind, VcKind::Postcondition) {
            continue;
        }
        neg_postcondition_vcs += 1;
        // STANDARD pipeline output (no stand-in): the SAME internalized vcgen
        // return-slot unification runs here — it must NOT make this FALSE bound
        // provable (`result == step` stays satisfiable), the no-masquerade witness.
        assert!(
            trust_certify::certify_violation(&vc.formula).is_none(),
            "FALSE postcondition `result > step` must FAIL CLOSED under the standard \
             pipeline with internalized return-slot unification (result CAN equal step): \
             no false Certified"
        );
    }
    assert!(neg_postcondition_vcs > 0, "negative control produced no Postcondition VCs to gate");
    eprintln!(
        "NEGATIVE: round_up_gt `result > step` — all {neg_postcondition_vcs} \
               Postcondition VC(s) failed closed (no masquerade)."
    );
}
