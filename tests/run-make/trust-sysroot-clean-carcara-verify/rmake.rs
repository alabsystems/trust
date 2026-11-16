//! The sysroot `clean` is a CAPABLE independent Alethe checker.
//!
//! Regression pin for bootstrap's `clean` ToolBuild
//! (`ensure_default_verifier_tool_bins`, tool.rs) enabling `carcara-verify`.
//! Without that feature `clean` answers EVERY Alethe certificate with
//! "carcara-verify feature required for tier 1 verification", whatever the
//! proof says — measured 2026-09-14/15 on trust-stage1-r2/bin/clean and on the
//! aterm trust pack 8590/8595 `bin/clean` — and trust-cg's certificate lane
//! (which capability-probes its checker with exactly this control pair) treats
//! such a sysroot as having NO checker.
//!
//! The recipe runs the sysroot binary on the same control certificate
//! trust-cg uses (`CHECKER_PROBE_SMT2` / `CHECKER_PROBE_ALETHE`,
//! obligation_cert_store.rs) and requires the `Proof status: fully verified`
//! contract trust-cg keys on; then it runs a one-premise MUTANT of the proof and
//! requires a rejection, so a checker that says yes to everything cannot pass.
//! Finally it pins the sysroot layout trust-cg-verify's fallback discovery
//! recognises (`trust_sysroot_clean_checker_candidate_for`): the checker sits in
//! `<sysroot>/bin` beside `trustc`, with `<sysroot>/lib/rustlib` present.
//!
//! A missing `clean` is a FAILURE, not a skip: batteries-on bootstrap installs
//! it whenever its source is present and `[build] tools` does not deselect it.
//!
//! It also pins Clean's Carcara soundness fixes 36-40 (Clean `b0a2d570a`,
//! `third-party/carcara/DOWNSTREAM.md`): four SATISFIABLE scripts that a Carcara
//! misreading SMT-LIB refuted (unhygienic `define-fun` capture, a second
//! `check-sat`, an ignored `pop`, `define-fun-rec` read as an axiom) must NOT be
//! reported fully verified, while the hygienic `define-fun` control must be. The
//! scripts are copies of Clean's `carcara_verify/soundness/` fixtures of the
//! same names. A `first-party/clean` move that drops the fixes turns this red
//! (docs/first-party-pin-ledger.md, 2026-10-07 (q)).

//@ ignore-cross-compile

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const CARCARA_FEATURE_MARKER: &str = "carcara-verify feature required";
const FULLY_VERIFIED: &str = "Proof status: fully verified";

const CONTROL_CERT: &str = r#"{"type": "alethe_certificate", "version": "1.0", "problem": "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n", "proof": "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t1 t0))\n"}"#;
const MUTANT_CERT: &str = r#"{"type": "alethe_certificate", "version": "1.0", "problem": "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n", "proof": "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t0))\n"}"#;

/// `(name, problem, proof)`: satisfiable scripts whose refutation a pre-fix-36-40
/// Carcara accepted. None may be reported fully verified.
const SATISFIABLE_MISREAD: [(&str, &str, &str); 4] = [
    (
        "pr_u1_define_fun_capture",
        "(set-logic ALL)\n(declare-fun x () Int)\n(define-fun k () Int x)\n(define-fun h ((x Int)) Int k)\n(assert (= (h 5) x))\n(assert (not (= x 5)))\n(check-sat)\n",
        "(assume a0 (= (h 5) x))\n(assume a1 (not (= x 5)))\n(step t1 (cl (= x 5)) :rule symm :premises (a0))\n(step t2 (cl) :rule resolution :premises (a1 t1))\n",
    ),
    (
        "pr_u14_two_check_sats",
        "(set-logic ALL)\n(declare-fun p () Bool)\n(assert p)\n(check-sat)\n(assert (not p))\n(check-sat)\n",
        "(assume a0 p)\n(assume a1 (not p))\n(step t1 (cl) :rule resolution :premises (a0 a1))\n",
    ),
    (
        "pr_u17_pop",
        "(set-logic ALL)\n(declare-fun p () Bool)\n(push 1)\n(assert (not p))\n(pop 1)\n(assert p)\n(check-sat)\n",
        "(assume a0 p)\n(assume a1 (not p))\n(step t1 (cl) :rule resolution :premises (a0 a1))\n",
    ),
    (
        "pr_u31_recursive_definition_inconsistent",
        "(set-logic UFLIA)\n(define-fun-rec f ((x Int)) Int (+ (f x) 1))\n(check-sat)\n",
        "(assume a0 (forall ((x Int)) (= (f x) (+ (f x) 1))))\n(step t1 (cl (or (not (forall ((x Int)) (= (f x) (+ (f x) 1)))) (= (f 0) (+ (f 0) 1)))) :rule forall_inst :args (0))\n(step t2 (cl (not (forall ((x Int)) (= (f x) (+ (f x) 1)))) (= (f 0) (+ (f 0) 1))) :rule or :premises (t1))\n(step t3 (cl (= (f 0) (+ (f 0) 1))) :rule resolution :premises (t2 a0))\n(step t4 (cl (not (= (f 0) (+ (f 0) 1)))) :rule la_generic :args (1))\n(step t5 (cl) :rule resolution :premises (t3 t4))\n",
    ),
];

/// The control: hygienic expansion makes `(h 5)` equal `x`, so this is UNSAT.
const OK_PR_HYGIENIC_DEFINE_FUN: (&str, &str, &str) = (
    "ok_pr_hygienic_define_fun",
    "(set-logic ALL)\n(declare-fun x () Int)\n(define-fun k () Int x)\n(define-fun h ((x Int)) Int k)\n(assert (not (= (h 5) x)))\n(check-sat)\n",
    "(assume a0 (not (= (h 5) x)))\n(step t1 (cl (= x x)) :rule refl)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
);

/// An `alethe_certificate` JSON document; the fixtures carry no `"` or `\`,
/// but escape them anyway so a future fixture cannot corrupt the document.
fn alethe_certificate(problem: &str, proof: &str) -> String {
    fn json_string(text: &str) -> String {
        let mut out = String::with_capacity(text.len() + 2);
        out.push('"');
        for ch in text.chars() {
            match ch {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                c => out.push(c),
            }
        }
        out.push('"');
        out
    }
    format!(
        r#"{{"type": "alethe_certificate", "version": "1.0", "problem": {}, "proof": {}}}"#,
        json_string(problem),
        json_string(proof)
    )
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream replay compiler ships no Trust verifier backends.
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let bin = rustc.parent().expect("rustc lives in <sysroot>/bin").to_path_buf();
    let clean = bin.join(bin_name("clean"));
    assert!(
        clean.is_file(),
        "batteries-on sysroot must ship its Alethe checker at {}",
        clean.display()
    );

    rfs::write("control.json", CONTROL_CERT);
    let control = cmd(&clean)
        .arg("cert")
        .arg("verify-external")
        .arg("control.json")
        .arg("--verbose")
        .run_unchecked();
    let (stdout, stderr) = (control.stdout_utf8(), control.stderr_utf8());
    assert!(
        !stdout.contains(CARCARA_FEATURE_MARKER) && !stderr.contains(CARCARA_FEATURE_MARKER),
        "sysroot clean was built without carcara-verify:\n{stdout}\n{stderr}"
    );
    assert!(
        control.status().success(),
        "sysroot clean refused the known-good control proof ({}):\n{stdout}\n{stderr}",
        control.status()
    );
    assert!(
        stdout.contains(FULLY_VERIFIED),
        "control proof must be reported fully verified:\n{stdout}\n{stderr}"
    );

    rfs::write("mutant.json", MUTANT_CERT);
    let mutant = cmd(&clean)
        .arg("cert")
        .arg("verify-external")
        .arg("mutant.json")
        .arg("--verbose")
        .run_unchecked();
    let (stdout, stderr) = (mutant.stdout_utf8(), mutant.stderr_utf8());
    assert!(
        !mutant.status().success() && !stdout.contains(FULLY_VERIFIED),
        "sysroot clean accepted a resolution step with one premise:\n{stdout}\n{stderr}"
    );
    assert!(
        !stdout.contains(CARCARA_FEATURE_MARKER) && !stderr.contains(CARCARA_FEATURE_MARKER),
        "the mutant must be rejected by Carcara, not by a missing feature:\n{stdout}\n{stderr}"
    );

    // Carcara fixes 36-40: no satisfiable script may be certified.
    for (name, problem, proof) in SATISFIABLE_MISREAD {
        let file = format!("{name}.json");
        rfs::write(&file, alethe_certificate(problem, proof));
        let run = cmd(&clean)
            .arg("cert")
            .arg("verify-external")
            .arg(&file)
            .arg("--verbose")
            .run_unchecked();
        let (stdout, stderr) = (run.stdout_utf8(), run.stderr_utf8());
        assert!(
            !stdout.contains(FULLY_VERIFIED),
            "sysroot clean certified a refutation of the SATISFIABLE script {name}; its \
             Carcara lacks Clean's fixes 36-40 (b0a2d570a):\n{stdout}\n{stderr}"
        );
        assert!(
            !stdout.contains(CARCARA_FEATURE_MARKER) && !stderr.contains(CARCARA_FEATURE_MARKER),
            "{name} must be refused by Carcara, not by a missing feature:\n{stdout}\n{stderr}"
        );
    }

    // The control keeps the loop above from passing on a checker that refuses
    // every script with definitions in it.
    let (name, problem, proof) = OK_PR_HYGIENIC_DEFINE_FUN;
    let file = format!("{name}.json");
    rfs::write(&file, alethe_certificate(problem, proof));
    let control = cmd(&clean)
        .arg("cert")
        .arg("verify-external")
        .arg(&file)
        .arg("--verbose")
        .run_unchecked();
    let (stdout, stderr) = (control.stdout_utf8(), control.stderr_utf8());
    assert!(
        control.status().success() && stdout.contains(FULLY_VERIFIED),
        "sysroot clean must fully verify the hygienic define-fun control {name} ({}):\n\
         {stdout}\n{stderr}",
        control.status()
    );

    assert_eq!(bin.file_name().and_then(|name| name.to_str()), Some("bin"));
    assert!(
        bin.join(bin_name("trustc")).is_file(),
        "trust-cg's sysroot fallback requires trustc beside clean in {}",
        bin.display()
    );
    assert!(
        bin.parent().expect("sysroot").join("lib/rustlib").is_dir(),
        "trust-cg's sysroot fallback requires <sysroot>/lib/rustlib"
    );
}
