// The `clean-axioms` CLI end to end: a context that declares a kernel-owned
// name is REFUSED (exit 2, no CLEAN verdict on stdout), never silently CLEAN.
//
// Before 2026-09-28 each `ax2_*` fixture below read `clean axioms: CLEAN` and
// passed `--require-axioms 3` (measured by the clean-sorry reviewer): the
// harness classified a foundation by NAME, so `propext : False` counted as
// the kernel's propext.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/clean-axioms")
        .join(format!("{name}.json"))
}

fn run(name: &str, extra: &[&str]) -> (Option<i32>, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_clean-axioms"))
        .args(extra)
        .arg(fixture(name))
        .output()
        .expect("clean-axioms runs");
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn counterfeit_contexts_are_refused_not_clean() {
    for name in [
        "ax2_propext_false",
        "ax2_quotsound_alias",
        "ax_propext_false",
        "ax_quotsound_alias",
        "choice_definition",
        "sorryax_definition",
        "trustedAy_axiom",
    ] {
        for extra in [&[][..], &["--require-axioms", "3"][..], &["--json"][..]] {
            let (code, stdout, stderr) = run(name, extra);
            assert_eq!(code, Some(2), "{name} {extra:?}: stdout={stdout} stderr={stderr}");
            assert!(!stdout.contains("CLEAN"), "{name} {extra:?}: {stdout}");
            assert!(!stdout.contains("\"clean\":true"), "{name} {extra:?}: {stdout}");
            assert!(stderr.contains("context REFUSED"), "{name} {extra:?}: {stderr}");
            assert!(stderr.contains("reserved kernel name"), "{name} {extra:?}: {stderr}");
        }
    }
}

#[test]
fn the_kernels_own_foundations_pass_the_gate_undeclared() {
    let (code, stdout, stderr) = run("kernel_foundations_undeclared", &["--require-axioms", "3"]);
    assert_eq!(code, Some(0), "stdout={stdout} stderr={stderr}");
    assert!(stdout.contains("clean axioms: CLEAN"), "{stdout}");
    let (code, stdout, _) = run("kernel_foundations_undeclared", &["--json"]);
    assert_eq!(code, Some(0));
    assert_eq!(
        stdout.trim(),
        r#"{"clean":true,"foundational":["Classical.choice","Quot.sound","propext"],"residual":[],"unresolved":[]}"#
    );
}

#[test]
fn residual_and_dangling_marker_fail_the_gate() {
    // Not kernel-owned: builds, and the two axioms are residual.
    let (code, stdout, _) = run("ax_proofirrel", &["--json"]);
    assert_eq!(code, Some(0), "report mode succeeds regardless of cleanliness");
    assert_eq!(
        stdout.trim(),
        r#"{"clean":false,"foundational":[],"residual":["False","proofIrrel"],"unresolved":[]}"#
    );
    let (code, _, _) = run("ax_proofirrel", &["--require-axioms", "3"]);
    assert_eq!(code, Some(1));
    // An undeclared trust marker is not the kernel's to vouch for.
    let (code, stdout, _) = run("sorryax_undeclared", &["--require-axioms", "3"]);
    assert_eq!(code, Some(1), "{stdout}");
    assert!(stdout.contains("NOT CLEAN") && stdout.contains("sorryAx"), "{stdout}");
}

/// A context DEFINITION is kernel-checked against the entries before it
/// (2026-09-29): an ill-typed `mySorry : False := Sort 0`, a self-reference, a
/// cycle and a top-universe value each REFUSE the context. Before, the first
/// two printed `clean axioms: CLEAN ✓` (measured by the cb/track-b reviewer).
#[test]
fn unchecked_definitions_are_refused_not_clean() {
    for name in
        ["def_ill_typed_mysorry", "def_self_reference", "def_cycle", "def_universe_overflow"]
    {
        for extra in [&[][..], &["--require-axioms", "3"][..], &["--json"][..]] {
            let (code, stdout, stderr) = run(name, extra);
            assert_eq!(code, Some(2), "{name} {extra:?}: stdout={stdout} stderr={stderr}");
            assert!(!stdout.contains("CLEAN"), "{name} {extra:?}: {stdout}");
            assert!(!stdout.contains("\"clean\":true"), "{name} {extra:?}: {stdout}");
            assert!(stderr.contains("context REFUSED"), "{name} {extra:?}: {stderr}");
        }
    }
    let (code, stdout, stderr) = run("def_clean_chain", &["--require-axioms", "3"]);
    assert_eq!(code, Some(0), "control: stdout={stdout} stderr={stderr}");
    assert!(stdout.contains("clean axioms: CLEAN"), "{stdout}");
}

/// de Bruijn (2026-09-29): the kernel returned a bound variable's type without
/// lifting it past the binders after it, so `(λP:Sort 2. λx:P. λQ:Prop. x) Type
/// Prop` typed as `∀Q:Prop, Q`. The cb/track-b round-2 reviewer's
/// `shift_false.json` and `shift_false_inline.json` (copied verbatim as
/// `debruijn_shift_false*`) printed `clean axioms: CLEAN ✓` and passed
/// `--require-axioms 3`; the polymorphic identity at its true type
/// (`poly_id.json`) was refused. Both directions are pinned here.
#[test]
fn de_bruijn_attacks_are_refused_and_true_types_are_clean() {
    for name in [
        "debruijn_shift_false",
        "debruijn_shift_false_inline",
        "debruijn_shift_false_deep",
        "debruijn_dep_confuse",
        "debruijn_open_axiom",
    ] {
        for extra in [&[][..], &["--require-axioms", "3"][..], &["--json"][..]] {
            let (code, stdout, stderr) = run(name, extra);
            assert_eq!(code, Some(2), "{name} {extra:?}: stdout={stdout} stderr={stderr}");
            assert!(!stdout.contains("CLEAN"), "{name} {extra:?}: {stdout}");
            assert!(!stdout.contains("\"clean\":true"), "{name} {extra:?}: {stdout}");
            assert!(stderr.contains("context REFUSED"), "{name} {extra:?}: {stderr}");
        }
    }
    for name in ["debruijn_poly_id", "debruijn_k_true_type", "debruijn_compose", "debruijn_dep_hyp"]
    {
        let (code, stdout, stderr) = run(name, &["--require-axioms", "3"]);
        assert_eq!(code, Some(0), "{name}: stdout={stdout} stderr={stderr}");
        assert!(stdout.contains("clean axioms: CLEAN"), "{name}: {stdout}");
    }
}
