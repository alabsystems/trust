// Regression (drop-in, 2026-07-06): the common ring-buffer idiom `s[i % s.len()]`
// (guarded non-empty) was fail-closed to `unsupported` — `build_modulo_bound_facts`
// emits the sufficient LINEAR bound `(len==0) ∨ (i%len < len)`, but the VC ALSO
// carried the nonlinear `%` DEFINITION (`dest == i mod len`), which ay's linear-arith
// lane rejects. Fix: drop the unsigned, NON-CONSTANT-divisor `%` scalar def (DROP-ONLY
// sound — removing a hypothesis can only weaken a PROVE, never false-PROVE; the linear
// bound compensates). Validated end-to-end: safe modulo-index PROVES; `s[i%100]`,
// unguarded `s[i%len]` (remzero), and variable-`k` `s[i%k]` all still REFUTE.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn bounds_dbg(name: &str) -> String {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap();
    let f: VerifiableFunction = serde_json::from_str(&json).unwrap();
    generate_vcs(&f)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .map(|vc| format!("{:?}", vc.formula))
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn safe_modulo_index_drops_nonlinear_def_keeping_linear_bound() {
    // The variable-divisor `%` def is DROPPED, so no `Rem`/`Mod` term chokes the
    // linear solver; the linear bound `dest < len` remains to discharge the index.
    let dbg = bounds_dbg("mod_safe");
    assert!(
        !dbg.contains("Rem(") && !dbg.contains("Mod("),
        "the nonlinear `%` def must be dropped from the safe modulo-index VC (else the \
         linear solver fail-closes to unsupported): {dbg}"
    );
}

#[test]
fn variable_modulus_index_drops_def_and_stays_refutable() {
    // SOUNDNESS: `if k!=0 { s[i % k] }` — the variable `%` def is DROPPED (no `Rem`
    // term to choke the solver), and the linear bound is `dest < k`, which does NOT
    // imply `dest < len` for an unconstrained `k`, so the obligation `dest >= len`
    // stays satisfiable (refutable). DROP-ONLY never manufactures a false-PROVE
    // (validated end-to-end: this refutes `[slice]`).
    let dbg = bounds_dbg("mod_var");
    assert!(
        !dbg.is_empty() && !dbg.contains("Rem("),
        "variable-modulus index: `%` def dropped (no Rem term) yet a refutable bounds          obligation remains: {dbg}"
    );
}
