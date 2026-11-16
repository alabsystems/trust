//! REAL-ARTIFACT guard for KNOWN_HAZARDS R-c: a write to a FIELD of a by-value
//! parameter must fail-close an `ensures` that names that field, as a whole-parameter
//! rebind already does.
//!
//! Each fixture `tests/data/byvalue_param_field_write/<fn>.json` is the compiler's own
//! extracted verification input for one function of `source.rs` beside it (compiled as
//! `byvalue_param_field_write.rs`), captured with the stage 1 of `782780ea0d` (2026-10-03):
//!
//! ```text
//! rustc byvalue_param_field_write.rs --edition 2021 -Ztrust-verify=on --crate-type lib \
//!       -Ztrust-policy=certify -Ztrust-dump=mir:<dir>
//! ```
//!
//! They live in a SUBDIRECTORY on purpose: `tests/data/*.json` is the corpus other rows
//! measure over (`entry_sentinel_tie_guards`, `version_ssa_parity_tests`), and a pin
//! for one hazard should not move their populations.
//!
//! A parameter name in an `ensures` denotes its ENTRY value (E2/D2,
//! docs/design/2026-07-09-two-language-spec-surface.md §3). That stage 1 PROVED `z`
//! (`s.a = 0; 1` under `ensures s.a == 0`) and certified it: its postcondition VC read the
//! clause's `s.0` at the store's version, `s.0#s0_0 == 0 ∧ ¬(s.0#s0_0 == 0)`.
//!
//! What this pins, on the real MIR:
//!
//!  * `trust_vcgen::rebound_parameter_places` — the export the compiler's typed-CHC
//!    attestation (`typed_chc_rebound_parameters`) calls — names parameter 1 for every
//!    by-value write shape, and nothing for `ok` (no write) or `mref` (a store through a
//!    `&mut` parameter: the PD-15 exit read, out of scope);
//!  * `generate_vcs` emits the fail-closed placeholder for each written-field clause: a
//!    Postcondition VC with NO version token in it, so the clause's names are the free
//!    entry values and the VC is satisfiable. Before the fix, every one of these carried
//!    the store's version (`s.0#…`) and read PROVED;
//!  * `ok` keeps the ordinary path: a VC that pins the return value, not the bare
//!    placeholder;
//!  * `unrel` (writes `s.b`; the clause names `s.a`, true under E2) gets the placeholder
//!    too. The predicate's channel walk names only `s.1`, but it is unioned with the
//!    `local_defs` seam's non-SSA test (`7f118dfc1f`), which names a written parameter
//!    WHOLE. That is a capability cost, DECISION_QUEUE R-c, pinned here so that
//!    narrowing it is a visible change.

use trust_types::{Formula, VcKind, VerifiableFunction};

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}byvalue_param_field_write/{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The parameter locals the shared predicate reports, in the shape the compiler's
/// `typed_chc_rebound_parameters` collects them.
fn rebound(func: &VerifiableFunction) -> trust_types::fx::FxHashSet<usize> {
    trust_vcgen::rebound_parameter_places(func).into_iter().map(|rebind| rebind.parameter).collect()
}

fn postcondition_formulas(func: &VerifiableFunction) -> Vec<Formula> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|vc| vc.formula)
        .collect()
}

fn free_names(formula: &Formula) -> Vec<String> {
    formula.free_variables().iter().map(|v| v.as_str().to_string()).collect()
}

/// A Postcondition VC that reads no versioned name: every name in it is a free entry
/// value, which is the fail-closed `Not(post)` placeholder's shape.
fn is_placeholder(formula: &Formula) -> bool {
    matches!(formula, Formula::Not(_)) && free_names(formula).iter().all(|name| !name.contains('#'))
}

const WRITTEN_FIELD_SHAPES: [&str; 7] = ["z", "two", "tup", "callw", "viaref", "neg", "k"];

#[test]
fn every_by_value_field_write_rebinds_parameter_one() {
    for name in WRITTEN_FIELD_SHAPES.into_iter().chain(["unrel"]) {
        let func = load(name);
        assert_eq!(
            rebound(&func).into_iter().collect::<Vec<_>>(),
            vec![1],
            "`{name}` writes a place of its by-value parameter `_1`; the predicate must say so"
        );
    }
}

#[test]
fn no_write_and_mut_ref_pointee_store_rebind_nothing() {
    for name in ["ok", "mref"] {
        let func = load(name);
        assert!(
            trust_vcgen::rebound_parameter_places(&func).is_empty(),
            "`{name}` must not be reported rebound: {:?}",
            trust_vcgen::rebound_parameter_places(&func)
        );
    }
}

#[test]
fn a_clause_over_a_written_parameter_gets_the_fail_closed_placeholder() {
    for name in WRITTEN_FIELD_SHAPES.into_iter().chain(["unrel"]) {
        let func = load(name);
        let posts = postcondition_formulas(&func);
        assert!(!posts.is_empty(), "`{name}` must emit a Postcondition VC");
        for formula in &posts {
            assert!(
                is_placeholder(formula),
                "`{name}`: a clause over a parameter the body writes must be fail-closed to \
                 a bare `Not(post)` over entry names, got {formula:?}"
            );
        }
    }
}

#[test]
fn an_unwritten_parameter_keeps_the_ordinary_postcondition_vc() {
    for name in ["ok"] {
        let func = load(name);
        let posts = postcondition_formulas(&func);
        assert!(!posts.is_empty(), "`{name}` must emit a Postcondition VC");
        assert!(
            posts.iter().all(|formula| !is_placeholder(formula)),
            "`{name}`: a clause over an unwritten parameter keeps the ordinary VC, got {posts:?}"
        );
    }
}
