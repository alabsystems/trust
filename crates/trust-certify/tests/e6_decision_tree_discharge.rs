//! E6 admission expansion I4′ — value decision trees (`if`/`else`, `match`
//! with literal arms, `matches!`), end to end through the E9 island-defeq
//! discharge, on the REAL extracted MIR of the differential harness
//! (`fixtures/e6_differential/shapes.{unopt,opt}.json`).
//!
//! As for I3′ (`e6_bool_tree_discharge.rs`), the kernel re-types every mint
//! but cannot see a wrong READING of the body (design note 2026-09-28 §5 rule
//! 5), so each body is judged against its correct island model AND against
//! the models a misreading would produce: arms swapped, a threshold moved by
//! one, a wrong `otherwise` value, a missing arm, `<` for `<=` — and exactly
//! the correct ones may discharge.
//!
//! The island spelling of a Rust `match` on an integer is an `if x = v then
//! … else …` chain (the design note's image: nested `ite` over `Eq x v`).
//! Clean's own `match` on a `UInt8` literal elaborates through `x == v`
//! (`BEq`), whose proposition is not the image's, so it does NOT discharge —
//! pinned here as a negative (`*_clean_match`) so a change in either spelling
//! is seen.
//!
//! Runs with no compiler build:
//! `targo --unverified test --manifest-path crates/Cargo.toml -p trust-certify --test e6_decision_tree_discharge`

use trust_certify::clean_island::{
    CitationVerdict, CleanIslandSession, admit_certified_island_definition,
    kernel_prove_ensures_by_defeq,
};
use trust_spec_elab::FacetTable;
use trust_types::VerifiableFunction;

const UNOPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.unopt.json");
const OPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.opt.json");

const MODELS: &str = "
def m_if_bool (c a b : Bool) : Bool := if c then a else b
def m_if_bool_swapped (c a b : Bool) : Bool := if c then b else a
def m_if_bool_connectives (c a b : Bool) : Bool := (c && a) || (!c && b)
def m_if_u8 (c : Bool) (a b : UInt8) : UInt8 := if c then a else b
def m_if_u8_swapped (c : Bool) (a b : UInt8) : UInt8 := if c then b else a
def m_if_const (c : Bool) : UInt8 := if c then 1 else 0
def m_if_const_swapped (c : Bool) : UInt8 := if c then 0 else 1
def m_match_bool (b : Bool) : UInt8 := if b then 3 else 9
def m_match_bool_swapped (b : Bool) : UInt8 := if b then 9 else 3
def m_sel_const (a : UInt8) : UInt8 := if a < 10 then 0 else 255
def m_sel_const_threshold (a : UInt8) : UInt8 := if a < 11 then 0 else 255
def m_sel_const_otherwise (a : UInt8) : UInt8 := if a < 10 then 0 else 254
def m_chain (a : UInt8) : UInt8 := if a < 10 then 1 else if a < 100 then 2 else 3
def m_chain_le (a : UInt8) : UInt8 := if a < 10 then 1 else if a <= 100 then 2 else 3
def m_match_u8 (x : UInt8) : UInt8 := if x = 0 then 10 else if x = 1 then 20 else if x = 7 then 30 else 0
def m_match_u8_value (x : UInt8) : UInt8 := if x = 0 then 10 else if x = 1 then 21 else if x = 7 then 30 else 0
def m_match_u8_missing (x : UInt8) : UInt8 := if x = 0 then 10 else if x = 7 then 30 else 0
def m_match_u8_clean_match (x : UInt8) : UInt8 := match x with | 0 => 10 | 1 => 20 | 7 => 30 | _ => 0
def m_matches (x : UInt8) : Bool := x == 1 || x == 2 || x == 7
def m_matches_missing (x : UInt8) : Bool := x == 1 || x == 2
def m_zero_or_max (x : UInt8) : Bool := x == 0 || x == 255
def m_max (a b : UInt8) : UInt8 := if b < a then a else b
def m_max_gt (a b : UInt8) : UInt8 := if a > b then a else b
def m_max_arms_swapped (a b : UInt8) : UInt8 := if b < a then b else a
def m_min_ge (a b : UInt8) : UInt8 := if b <= a then b else a
def m_min_gt (a b : UInt8) : UInt8 := if b < a then b else a
def m_ne_sel (a b : UInt8) : UInt8 := if a = b then 0 else a
def m_ne_sel_swapped (a b : UInt8) : UInt8 := if a = b then a else 0
def m_if_cmp_bool (a : UInt8) (b : Bool) : Bool := if a = 0 then b else !b
def m_if_cmp_bool_swapped (a : UInt8) (b : Bool) : Bool := if a = 0 then !b else b
def m_param_arms (x a : UInt8) : UInt8 := if x = 0 then a else if x = 1 then 7 else x
def m_param_arms_wrong (x a : UInt8) : UInt8 := if x = 0 then x else if x = 1 then 7 else a
def m_nested (a b : Bool) : UInt8 := if a then (if b then 1 else 2) else 3
def m_nested_swapped (a b : Bool) : UInt8 := if a then (if b then 2 else 1) else 3
";

/// `(body, (param, type) list, the models it is judged against, the ones
/// that must discharge)`.
type Row = (
    &'static str,
    &'static [(&'static str, &'static str)],
    &'static [&'static str],
    &'static [&'static str],
);

const ROWS: &[Row] = &[
    (
        "d_if_bool",
        &[("c", "bool"), ("a", "bool"), ("b", "bool")],
        &["m_if_bool", "m_if_bool_swapped", "m_if_bool_connectives"],
        &["m_if_bool"],
    ),
    (
        "d_if_u8",
        &[("c", "bool"), ("a", "u8"), ("b", "u8")],
        &["m_if_u8", "m_if_u8_swapped"],
        &["m_if_u8"],
    ),
    // All-`bool` parameters with an integer result. These were a CLAUSE-LANE
    // limit: the clause elaborator typed `result == m(c)` at the parameters'
    // `Bool` carrier and refused the goal as ill-typed, so nothing discharged,
    // correct model or not. Since E9-RESULT-CARRIER-1 (efb8ede416, TG15) the
    // relation takes the carrier `result` and the model return, so exactly the
    // correct model discharges and the arms-swapped one does not (measured on
    // origin/main e88d030c4a, both fixtures; the rows had stayed `&[]`, red).
    ("d_if_const", &[("c", "bool")], &["m_if_const", "m_if_const_swapped"], &["m_if_const"]),
    (
        "d_match_bool",
        &[("b", "bool")],
        &["m_match_bool", "m_match_bool_swapped"],
        &["m_match_bool"],
    ),
    (
        "d_sel_const",
        &[("a", "u8")],
        &["m_sel_const", "m_sel_const_threshold", "m_sel_const_otherwise"],
        &["m_sel_const"],
    ),
    ("d_chain", &[("a", "u8")], &["m_chain", "m_chain_le"], &["m_chain"]),
    (
        "d_match_u8",
        &[("x", "u8")],
        &["m_match_u8", "m_match_u8_value", "m_match_u8_missing", "m_match_u8_clean_match"],
        &["m_match_u8"],
    ),
    ("d_matches", &[("x", "u8")], &["m_matches", "m_matches_missing"], &["m_matches"]),
    ("d_match_u8_bool", &[("x", "u8")], &["m_zero_or_max", "m_matches"], &["m_zero_or_max"]),
    (
        "d_max",
        &[("a", "u8"), ("b", "u8")],
        &["m_max", "m_max_gt", "m_max_arms_swapped"],
        &["m_max", "m_max_gt"],
    ),
    ("d_ge_sel", &[("a", "u8"), ("b", "u8")], &["m_min_ge", "m_min_gt"], &["m_min_ge"]),
    ("d_ne_sel", &[("a", "u8"), ("b", "u8")], &["m_ne_sel", "m_ne_sel_swapped"], &["m_ne_sel"]),
    (
        "d_if_cmp_bool",
        &[("a", "u8"), ("b", "bool")],
        &["m_if_cmp_bool", "m_if_cmp_bool_swapped"],
        &["m_if_cmp_bool"],
    ),
    (
        "d_match_param_arms",
        &[("x", "u8"), ("a", "u8")],
        &["m_param_arms", "m_param_arms_wrong"],
        &["m_param_arms"],
    ),
    // The same shape (all-`bool` parameters, a `u8` result), nested.
    (
        "d_if_nested",
        &[("a", "bool"), ("b", "bool")],
        &["m_nested", "m_nested_swapped"],
        &["m_nested"],
    ),
];

fn body(json: &str, name: &str) -> VerifiableFunction {
    let root: serde_json::Value = serde_json::from_str(json).expect("fixture parses");
    serde_json::from_value(root["functions"][format!("e6_shapes::{name}")].clone())
        .unwrap_or_else(|e| panic!("`{name}` does not deserialize: {e}"))
}

fn discharged(func: &VerifiableFunction, params: &[(&str, &str)], models: &[&str]) -> Vec<String> {
    let seed =
        FacetTable::from_structural_facets([(func.def_path.clone(), true, true, true, true)]);
    let mut session = CleanIslandSession::new();
    let minted = session.admit_program_functions(std::slice::from_ref(func), &seed);
    assert_eq!(minted.len(), 1, "`{}` must mint (it is an I4′ shape)", func.def_path);
    let outcome = session.check(MODELS);
    assert!(!outcome.is_rejected(), "the models must kernel-check: {:?}", outcome.errors);
    let env = session.environment().expect("session environment").clone();
    let args = params.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", ");
    let mut out = Vec::new();
    for model in models {
        let mut table = seed.clone();
        for (path, admission) in &minted {
            table.admit(path.clone(), admission.clone());
        }
        admit_certified_island_definition(&env, model, &mut table).expect("model is admissible");
        let verdict = kernel_prove_ensures_by_defeq(
            &env,
            &format!("result == {model}({args})"),
            params,
            &func.def_path,
            &table,
        );
        if matches!(verdict, CitationVerdict::KernelStatementMatchCertified) {
            out.push((*model).to_owned());
        }
    }
    out
}

#[test]
fn every_decision_tree_discharges_against_exactly_its_own_models() {
    let mut wrong = Vec::new();
    let mut pairs = 0usize;
    for (tag, json) in [("unopt", UNOPT_JSON), ("opt", OPT_JSON)] {
        for (name, params, models, expected) in ROWS {
            let func = body(json, name);
            let got = discharged(&func, params, models);
            pairs += models.len();
            let want: Vec<String> = expected.iter().map(|m| (*m).to_owned()).collect();
            if got != want {
                wrong
                    .push(format!("[{tag}] {name}: discharged {got:?}, expected exactly {want:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "decision tree discharge matrix:\n{}", wrong.join("\n"));
    assert!(pairs >= 70, "only {pairs} body/model pairs were judged");
}
