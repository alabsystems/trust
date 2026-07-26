// Real-MIR reproduction of the assert_mut_setter_identity falsification fixture.
// The base assert-refutation lane must PROVE `assert!(a == v)` after
// `set(&mut a, v)` — i.e. `generate_full_assert_refutation_vcs` must emit a
// GROUNDED formula (every free var an input parameter) for the panic block, so ay
// decides it UNSAT (no input reaches the panic). Before the setter-summary token
// fix the emitted formula had `_7#s1_0` (the post-call copy `_7 = Copy(a)`) free
// and un-pinned, so it was NOT grounded and the obligation demoted to
// runtime-checked, failing `-full`.
//
// The fixtures are the REAL MIR extracted with `-Ztrust-dump=mir:<dir>` from the
// fixture's `f` and its callee `set`.
use trust_types::*;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

#[test]
fn setter_identity_assert_is_grounded_on_real_mir() {
    let f = load(include_str!("fixtures/setter_identity_f_mir.json"));
    let set = load(include_str!("fixtures/setter_identity_set_mir.json"));

    // Populate the derived-setter registry exactly as the compiler's
    // `trust_init_backing_certificates` does over the whole-crate extraction.
    let summaries = trust_vcgen::compute_trivial_setter_summaries(std::slice::from_ref(&set));
    assert!(
        !summaries.is_empty(),
        "the trivial-setter recognizer must admit `set`; got {summaries:?}"
    );
    let context = trust_vcgen::VcgenContext::for_function(f.def_path.clone())
        .with_callee_summaries(
            trust_vcgen::CalleeSummaryContext::default().with_setter_summaries(summaries),
        );
    let vcs = trust_vcgen::generate_full_assert_refutation_vcs_with_context(&f, &context);
    assert_eq!(vcs.len(), 1, "one assert/panic block => one refutation VC; got {}", vcs.len());
    let vc = &vcs[0];

    // The refutation formula must be UNSAT (a proof: no input reaches the panic).
    // Concretely, it must carry BOTH derived-setter facts sharing a single bridge
    // variable, so the panic premise `Eq_NOT(copy, v)` is contradicted:
    //   (i)  the setter post-call fact      Eq(<bridge>, v)
    //   (ii) the copy-chain link            Eq(<copied-temp>, <bridge>)
    //   (iii) the panic premise             Not(Eq(<copied-temp>, v))
    // (i)+(ii) force <copied-temp> == v, contradicting (iii) ⇒ UNSAT. This test
    // guards the TOKEN alignment: (i) and (ii) must name the SAME bridge var, else
    // they are disjoint and inert (the pre-fix behavior left the copy free).
    let eqs: Vec<(String, String)> = collect_var_eqs(&vc.formula);
    // The setter fact: some bridge var equals the parameter `v`.
    let bridge: Vec<&str> = eqs
        .iter()
        .filter(|(a, b)| a == "v" || b == "v")
        .map(|(a, b)| if a == "v" { b.as_str() } else { a.as_str() })
        .filter(|nm| *nm != "v")
        .collect();
    assert!(
        !bridge.is_empty(),
        "a derived-setter fact `<bridge> == v` must be present; formula: {:?}",
        vc.formula
    );
    // Every bridge is transitively connected to the panic-premise's copied temp:
    // there is an `Eq(copied, bridge)` copy-chain link. Assert at least one bridge
    // is itself the subject of a further Eq (the copy link) — i.e. the chain has
    // depth ≥ 2 and closes, not a dangling `bridge == v` with nothing reaching it.
    let connected = bridge.iter().any(|br| {
        eqs.iter().any(|(a, b)| (a == br || b == br) && a != "v" && b != "v")
    });
    assert!(
        connected,
        "the setter bridge var must also be tied to the copied temp (copy-chain \
         link) so the panic premise is contradicted; bridges={bridge:?}, eqs={eqs:?}\n\
         formula: {:?}",
        vc.formula
    );
}

/// Collect every `Eq(Var(a), Var(b))` pair (either operand order) appearing
/// anywhere in `f`, for equality-chain inspection.
fn collect_var_eqs(f: &Formula) -> Vec<(String, String)> {
    fn walk(f: &Formula, out: &mut Vec<(String, String)>) {
        match f {
            Formula::Eq(a, b) => {
                if let (Formula::Var(na, _), Formula::Var(nb, _)) = (a.as_ref(), b.as_ref()) {
                    out.push((na.clone(), nb.clone()));
                }
                walk(a, out);
                walk(b, out);
            }
            Formula::And(xs) | Formula::Or(xs) => {
                for x in xs {
                    walk(x, out);
                }
            }
            Formula::Not(x) => walk(x, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(f, &mut out);
    out
}
