//! E6 admission expansion I1′ — `==`/`!=` over `bool`, end to end through the
//! E9 island-defeq discharge, on the REAL extracted MIR of the differential
//! harness (`fixtures/e6_differential/shapes.{unopt,opt}.json`).
//!
//! The kernel re-types every mint, but it cannot see a wrong READING of the
//! body (design note 2026-09-28 §5 rule 5). So this is a BODY × MODEL matrix:
//! five bool bodies (`==`, `!=`, `<`, `<=`, `>`) against four island models
//! (`a == b`, `a != b`, and the true meanings of `a < b` and `a <= b`), at both
//! opt levels, and exactly the two diagonal pairs may discharge:
//!
//! * `a == b` against `a == b`, and `a != b` against `a != b` — I1′;
//! * NOTHING for the orderings — not even against their own correct models
//!   (`!a && b`, `!a || b`): I1′ mints no ordering image at all, and above all
//!   never the `==` image review H1 found the plan would have minted for them.
//!
//! Runs with no compiler build:
//! `targo --unverified test --manifest-path crates/Cargo.toml -p trust-certify --test e6_bool_cmp_discharge`

use trust_certify::clean_island::{
    CitationVerdict, CleanIslandSession, admit_certified_island_definition,
    kernel_prove_ensures_by_defeq,
};
use trust_spec_elab::FacetTable;
use trust_types::VerifiableFunction;

const UNOPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.unopt.json");
const OPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.opt.json");

const MODELS: &str = "
def m_eq (a b : Bool) : Bool := a == b
def m_ne (a b : Bool) : Bool := a != b
def m_lt (a b : Bool) : Bool := !a && b
def m_le (a b : Bool) : Bool := !a || b
";

fn body(json: &str, name: &str) -> VerifiableFunction {
    let root: serde_json::Value = serde_json::from_str(json).expect("fixture parses");
    serde_json::from_value(root["functions"][format!("e6_shapes::{name}")].clone())
        .unwrap_or_else(|e| panic!("`{name}` does not deserialize: {e}"))
}

/// Whether the clause `result == <model>(a, b)` discharges on `func`.
fn discharges(func: &VerifiableFunction, model: &str) -> bool {
    let seed =
        FacetTable::from_structural_facets([(func.def_path.clone(), true, true, true, true)]);
    let mut session = CleanIslandSession::new();
    let minted = session.admit_program_functions(std::slice::from_ref(func), &seed);
    let outcome = session.check(MODELS);
    assert!(!outcome.is_rejected(), "the models must kernel-check: {:?}", outcome.errors);
    let mut table = seed.clone();
    for (path, admission) in &minted {
        table.admit(path.clone(), admission.clone());
    }
    let env = session.environment().expect("session environment").clone();
    admit_certified_island_definition(&env, model, &mut table).expect("the model is admissible");
    let verdict = kernel_prove_ensures_by_defeq(
        &env,
        &format!("result == {model}(a, b)"),
        &[("a", "bool"), ("b", "bool")],
        &func.def_path,
        &table,
    );
    matches!(verdict, CitationVerdict::KernelStatementMatchCertified)
}

#[test]
fn only_the_equalities_discharge_and_only_against_their_own_model() {
    let bodies = ["bb_eq", "bb_ne", "bb_lt", "bb_le", "bb_gt"];
    let models = ["m_eq", "m_ne", "m_lt", "m_le"];
    let mut wrong = Vec::new();
    for (tag, json) in [("unopt", UNOPT_JSON), ("opt", OPT_JSON)] {
        for b in bodies {
            let func = body(json, b);
            for m in models {
                let expected = matches!((b, m), ("bb_eq", "m_eq") | ("bb_ne", "m_ne"));
                let got = discharges(&func, m);
                if got != expected {
                    wrong.push(format!(
                        "[{tag}] body {b} vs model {m}: discharged={got}, expected {expected}"
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "bool comparison discharge matrix:\n{}", wrong.join("\n"));
}

/// The wrong-BINARY gate keeps to the frozen shapes (review H3): a generated
/// carrier whose body only the E6-only lanes read is refused as outside the
/// checked fragment — even `a == b` against its own model — until the new
/// shapes are measured against that gate. A frozen bool control still passes,
/// so the refusal is the lane's, not the harness's.
#[test]
fn the_carrier_faithfulness_gate_refuses_the_new_bool_shapes() {
    use trust_certify::clean_island::{
        CarrierFaithfulnessRejection, check_generated_carrier_faithfulness,
    };
    for (tag, json) in [("unopt", UNOPT_JSON), ("opt", OPT_JSON)] {
        for (b, m) in [("bb_eq", "m_eq"), ("bb_ne", "m_ne")] {
            let func = body(json, b);
            let mut session = CleanIslandSession::new();
            assert!(!session.check(MODELS).is_rejected());
            let mut env = session.environment().expect("env").clone();
            let mut table = FacetTable::from_structural_facets([(
                func.def_path.clone(),
                true,
                true,
                true,
                true,
            )]);
            let verdict = check_generated_carrier_faithfulness(&mut env, m, &func, &mut table);
            assert!(
                matches!(
                    verdict,
                    Err(CarrierFaithfulnessRejection::CarrierOutsideCheckedFragment { .. })
                ),
                "[{tag}] {b} vs {m}: {verdict:?}"
            );
        }
    }
    // Control: a FROZEN bool shape (a projection) against its own model
    // passes the same gate, so the refusals above are the lanes', not the
    // harness's. (The gate spells only u32/u64/i32/i64/bool parameters.)
    let func = body(UNOPT_JSON, "p_bool");
    let mut session = CleanIslandSession::new();
    assert!(!session.check("def m_id (a : Bool) : Bool := a").is_rejected());
    let mut env = session.environment().expect("env").clone();
    let mut table =
        FacetTable::from_structural_facets([(func.def_path.clone(), true, true, true, true)]);
    let verdict = check_generated_carrier_faithfulness(&mut env, "m_id", &func, &mut table);
    assert!(verdict.is_ok(), "the frozen-shape control must pass: {verdict:?}");
}
