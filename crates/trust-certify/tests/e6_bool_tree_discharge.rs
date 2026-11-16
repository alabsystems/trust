//! E6 admission expansion I3′ — `bool` connective trees, end to end through
//! the E9 island-defeq discharge, on the REAL extracted MIR of the
//! differential harness (`fixtures/e6_differential/shapes.{unopt,opt}.json`).
//!
//! The kernel re-types every mint, but it cannot see a wrong READING of the
//! body (design note 2026-09-28 §5 rule 5). So this is a BODY × MODEL matrix:
//! every I3′ body against every island model of its signature, at both opt
//! levels, and exactly the designated pairs may discharge. The models include
//! the wrong ones a misreading would produce — `&&` and `||` swapped, a
//! negation moved, a comparison leaf's operands swapped, a De Morgan dual of
//! a correct model — so a reader or producer that confused any of them would
//! discharge a pair this test forbids.
//!
//! Runs with no compiler build:
//! `targo --unverified test --manifest-path crates/Cargo.toml -p trust-certify --test e6_bool_tree_discharge`

use trust_certify::clean_island::{
    CitationVerdict, CleanIslandSession, admit_certified_island_definition,
    kernel_prove_ensures_by_defeq,
};
use trust_spec_elab::FacetTable;
use trust_types::VerifiableFunction;

const UNOPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.unopt.json");
const OPT_JSON: &str = include_str!("fixtures/e6_differential/shapes.opt.json");

/// Every island model, in the natural spelling an author converting the Rust
/// body would write (`&&`/`||`/`!`, `xor`, `==`/`!=`, and `decide (x < y)`
/// for an unsigned comparison, as the frozen comparison mint's discharges use).
const MODELS: &str = "
def m_and (a b : Bool) : Bool := a && b
def m_or (a b : Bool) : Bool := a || b
def m_xor (a b : Bool) : Bool := xor a b
def m_not_and (a b : Bool) : Bool := !(a && b)
def m_demorgan (a b : Bool) : Bool := !a || !b
def m_not_or (a b : Bool) : Bool := !a || b
def m_and_not (a b : Bool) : Bool := a && !b
def m_let (a b : Bool) : Bool := (a && b) || a
def m_not (a : Bool) : Bool := !a
def m_or3 (a b c : Bool) : Bool := a || b || c
def m_and3 (a b c : Bool) : Bool := a && b && c
def m_gate (w c e : Bool) : Bool := w && (c || !e)
def m_gate_neg_moved (w c e : Bool) : Bool := w && (!c || e)
def m_gate_swapped (w c e : Bool) : Bool := w || (c && !e)
def m_nested (a b c : Bool) : Bool := !(a || (b && !c))
def m_mix (a b c : Bool) : Bool := (a && b) || (!a && c)
def m_eq_tree (a b c : Bool) : Bool := (a == b) || c
def m_ne_tree (a b c : Bool) : Bool := a != b && c
def m_xor_eq (a b c : Bool) : Bool := xor a b == c
def m_cmp3 (a b : UInt8) : Bool := decide (a < 10) || decide (a = b) || decide (200 < b)
def m_cmp3_leaf_swapped (a b : UInt8) : Bool := decide (a < 10) || decide (b = a) || decide (200 < b)
def m_cmp3_and (a b : UInt8) : Bool := decide (a < 10) && decide (a = b) || decide (200 < b)
def m_ne_u8 (a b : UInt8) : Bool := a != b
def m_eq_u8 (a b : UInt8) : Bool := a == b
def m_not_cmp (a b : UInt8) : Bool := !(decide (a < b))
def m_ge (a b : UInt8) : Bool := decide (b <= a)
def m_mixed (a b : UInt8) (c : Bool) : Bool := decide (a < b) && !c
def m_mixed_or (a b : UInt8) (c : Bool) : Bool := decide (a < b) || !c
def m_eq_of_cmps (a b : UInt8) (c : Bool) : Bool := decide (a < b) == c
def m_cmp6 (x : UInt8) : Bool := x == 1 || x == 3 || x == 5 || x == 7 || x == 9 || x == 11
def m_cmp6_missing (x : UInt8) : Bool := x == 1 || x == 3 || x == 5 || x == 7 || x == 9
def m_ne_lit (x : UInt8) : Bool := x != 127 && decide (32 <= x)
def m_ne_lit_neg (x : UInt8) : Bool := x == 127 && decide (32 <= x)
";

/// The models of each signature, as `(name, parameter list)`: every body of
/// that signature is tried against every model in its group.
const GROUPS: &[(&[&str], &[&str])] = &[
    (
        &["a", "b"],
        &["m_and", "m_or", "m_xor", "m_not_and", "m_demorgan", "m_not_or", "m_and_not", "m_let"],
    ),
    (&["a"], &["m_not"]),
    (
        &["a", "b", "c"],
        &[
            "m_or3",
            "m_and3",
            "m_gate",
            "m_gate_neg_moved",
            "m_gate_swapped",
            "m_nested",
            "m_mix",
            "m_eq_tree",
            "m_ne_tree",
            "m_xor_eq",
        ],
    ),
    (
        &["a", "b"],
        &["m_cmp3", "m_cmp3_leaf_swapped", "m_cmp3_and", "m_ne_u8", "m_eq_u8", "m_not_cmp", "m_ge"],
    ),
    (&["a", "b", "c"], &["m_mixed", "m_mixed_or", "m_eq_of_cmps"]),
    (&["x"], &["m_cmp6", "m_cmp6_missing", "m_ne_lit", "m_ne_lit_neg"]),
];

/// `(body, its parameter types, the ONE group index, the models it must
/// discharge against — every other model of the group must not)`.
const BODIES: &[(&str, &[&str], usize, &[&str])] = &[
    ("t_and", &["bool", "bool"], 0, &["m_and"]),
    ("t_or", &["bool", "bool"], 0, &["m_or"]),
    ("t_bor", &["bool", "bool"], 0, &["m_or"]),
    ("ay_xor_accumulate_parity", &["bool", "bool"], 0, &["m_xor"]),
    ("t_not_and", &["bool", "bool"], 0, &["m_not_and"]),
    ("t_not_or", &["bool", "bool"], 0, &["m_not_or"]),
    ("t_and_not", &["bool", "bool"], 0, &["m_and_not"]),
    ("t_let", &["bool", "bool"], 0, &["m_let"]),
    ("t_not", &["bool"], 1, &["m_not"]),
    ("t_or3", &["bool", "bool", "bool"], 2, &["m_or3"]),
    ("t_and3", &["bool", "bool", "bool"], 2, &["m_and3"]),
    // `self_ind & init_valid & entry_ind` is LEFT-nested in MIR and re-nested
    // to the right, so it meets the natural `a && b && c` model.
    ("ay_lemma_admitted_inductive", &["bool", "bool", "bool"], 2, &["m_and3"]),
    ("ay_gate_keeps_sat", &["bool", "bool", "bool"], 2, &["m_gate"]),
    ("t_nested", &["bool", "bool", "bool"], 2, &["m_nested"]),
    ("t_and_or_mix", &["bool", "bool", "bool"], 2, &["m_mix"]),
    ("t_eq_tree", &["bool", "bool", "bool"], 2, &["m_eq_tree"]),
    ("t_ne_tree", &["bool", "bool", "bool"], 2, &["m_ne_tree"]),
    ("t_xor_eq", &["bool", "bool", "bool"], 2, &["m_xor_eq"]),
    ("t_cmp3", &["u8", "u8"], 3, &["m_cmp3"]),
    ("c_ne", &["u8", "u8"], 3, &["m_ne_u8"]),
    ("t_not_cmp", &["u8", "u8"], 3, &["m_not_cmp"]),
    ("t_mixed", &["u8", "u8", "bool"], 4, &["m_mixed"]),
    ("bb_eq_of_cmps", &["u8", "u8", "bool"], 4, &["m_eq_of_cmps"]),
    ("t_cmp6", &["u8"], 5, &["m_cmp6"]),
    ("t_ne_lit", &["u8"], 5, &["m_ne_lit"]),
];

fn body(json: &str, name: &str) -> VerifiableFunction {
    let root: serde_json::Value = serde_json::from_str(json).expect("fixture parses");
    serde_json::from_value(root["functions"][format!("e6_shapes::{name}")].clone())
        .unwrap_or_else(|e| panic!("`{name}` does not deserialize: {e}"))
}

/// Which models of `models` the clause `result == <model>(<params>)`
/// discharges on `func`, in one session.
fn discharged(func: &VerifiableFunction, params: &[(&str, &str)], models: &[&str]) -> Vec<String> {
    let seed =
        FacetTable::from_structural_facets([(func.def_path.clone(), true, true, true, true)]);
    let mut session = CleanIslandSession::new();
    let minted = session.admit_program_functions(std::slice::from_ref(func), &seed);
    assert_eq!(minted.len(), 1, "`{}` must mint (it is an I3′ shape)", func.def_path);
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
fn every_tree_discharges_against_exactly_its_own_models() {
    let mut wrong = Vec::new();
    let mut pairs = 0usize;
    for (tag, json) in [("unopt", UNOPT_JSON), ("opt", OPT_JSON)] {
        for (name, tys, group, expected) in BODIES {
            let (names, models) = GROUPS[*group];
            assert_eq!(names.len(), tys.len(), "{name}: group {group} has another arity");
            let params: Vec<(&str, &str)> =
                names.iter().copied().zip(tys.iter().copied()).collect();
            let func = body(json, name);
            let got = discharged(&func, &params, models);
            pairs += models.len();
            let want: Vec<String> = expected.iter().map(|m| (*m).to_owned()).collect();
            if got != want {
                wrong
                    .push(format!("[{tag}] {name}: discharged {got:?}, expected exactly {want:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "bool tree discharge matrix:\n{}", wrong.join("\n"));
    assert!(pairs >= 300, "only {pairs} body/model pairs were judged");
}

/// The wrong-BINARY gate keeps to the frozen shapes (review H3): a generated
/// carrier whose body only the E6-only TREE reader reads is refused as
/// outside the checked fragment — even against its own model — until the new
/// shapes are measured against that gate.
#[test]
fn the_carrier_faithfulness_gate_refuses_the_tree_shapes() {
    use trust_certify::clean_island::{
        CarrierFaithfulnessRejection, check_generated_carrier_faithfulness,
    };
    for (tag, json) in [("unopt", UNOPT_JSON), ("opt", OPT_JSON)] {
        // `bool` shapes only: the gate spells u32/u64/i32/i64/bool parameters
        // and refuses a `UInt8` model earlier, as an unrepresentable type.
        for (b, m) in [("t_and", "m_and"), ("t_or3", "m_or3"), ("ay_gate_keeps_sat", "m_gate")] {
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
}
