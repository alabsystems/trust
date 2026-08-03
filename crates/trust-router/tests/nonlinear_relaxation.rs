// The ay bridge must PROVE an obligation whose proof needs only the LINEAR
// core of a `mod`-bearing formula. Historically ay returned `unknown` on the
// QF_NIA query and the proof was recovered by the sound nonlinear-abstraction
// retry (see incremental_ay::abstract_nonlinear); the pinned ay now decides
// the query `unsat` directly. Either path must yield `Proved`.
//
// Models the `s[n % s.len()]` bounds VC under a non-empty guard:
//   fact:      (slen == 0) ∨ (k < slen)      [the unsigned modulo bound]
//   def:       k == n mod slen               [the poisoning nonlinear term]
//   path:      slen > 0                       [from the !is_empty / remzero assert]
//   violation: k >= slen
// UNSAT (the fact + path + violation are contradictory) even before the `mod`
// is abstracted away. Sound: the relaxation has a superset of models, so its
// UNSAT implies the original's UNSAT.
//
// Skips gracefully if the `ay` solver is not co-located (env-dependent).
use trust_router::IncrementalAYSession;
use trust_types::*;

fn locate_ay() -> Option<String> {
    if let Ok(p) = std::env::var("TRUST_AY_BIN") {
        if std::path::Path::new(&p).exists() {
            return Some(p);
        }
    }
    // Walk up from the crate dir to a repo root holding build/host/stage2/bin/ay.
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let cand = dir.join("build/host/stage2/bin/ay");
        if cand.exists() {
            return Some(cand.to_string_lossy().into_owned());
        }
        if !dir.pop() {
            return None;
        }
    }
}

#[test]
fn nonlinear_relaxation_proves_symbolic_modulo_bound() {
    let Some(ay) = locate_ay() else {
        eprintln!("ay solver not found (set TRUST_AY_BIN); skipping");
        return;
    };
    let k = || Formula::Var("k".into(), Sort::Int);
    let slen = || Formula::Var("slen".into(), Sort::Int);
    let n = || Formula::Var("n".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Or(vec![
            Formula::Eq(Box::new(slen()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(k()), Box::new(slen())),
        ]),
        Formula::Eq(Box::new(k()), Box::new(Formula::Rem(Box::new(n()), Box::new(slen())))),
        Formula::Gt(Box::new(slen()), Box::new(Formula::Int(0))),
        Formula::Ge(Box::new(k()), Box::new(slen())),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "modtest".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    let result = IncrementalAYSession::with_solver_path(ay).verify_vc(&vc);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "symbolic-modulo bound must PROVE (directly or via nonlinear relaxation), got {result:?}"
    );

    // Soundness guard: the RELAXATION must never be the prover of an obligation
    // whose relaxed formula is SAT. Dropping the bounding fact leaves
    // `k == n mod slen, slen > 0, k >= slen`; its relaxation (`k` free) is
    // satisfiable, so a `Proved` attributed to `ay-nonlinear-relaxation` here
    // would mean the relaxation lane fabricated an UNSAT. The ORIGINAL formula
    // is still UNSAT under exact `mod` semantics (`|n mod slen| < slen`), so a
    // DIRECT proof from the solver itself is sound and acceptable — the pinned
    // ay now decides it without the relaxation.
    let unsat_should_not = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "modtest_unsafe".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Eq(Box::new(k()), Box::new(Formula::Rem(Box::new(n()), Box::new(slen())))),
            Formula::Gt(Box::new(slen()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(k()), Box::new(slen())),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    let r2 =
        IncrementalAYSession::with_solver_path(locate_ay().unwrap()).verify_vc(&unsat_should_not);
    assert!(
        !(matches!(r2, VerificationResult::Proved { .. })
            && r2.solver_name() == "ay-nonlinear-relaxation"),
        "the SAT relaxation must never publish the proof of the unbounded modulo obligation, \
         got {r2:?}"
    );
}
