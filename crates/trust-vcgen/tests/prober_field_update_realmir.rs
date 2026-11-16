//! Captured compiler MIR for Prober::ensure_num_vars (source beside the fixture).
//! Its early guard reads self.num_vars before the store. Equating both values
//! made every later allocation violation UNSAT, even for a reachable oversized
//! resize. Check concrete executions of the generated violation formulas.

use trust_types::{Formula, VcKind, VerifiableFunction};

fn obligations() -> Vec<trust_types::VerificationCondition> {
    let f: VerifiableFunction =
        serde_json::from_str(include_str!("data/prober_field_update.json")).unwrap();
    let vcs = trust_vcgen::generate_vcs(&f);
    assert_eq!(vcs.len(), 3, "all three resize obligations must survive");
    assert!(vcs.iter().all(|vc| matches!(vc.kind, VcKind::UnboundedAllocation { .. })));
    vcs
}

// Execute the captured path with an initially empty Prober. Each resize is
// reached: old num_vars and all lengths are zero, and the requested size is n.
// Numeric field names and temporaries are fixed by the checked-in MIR artifact.
fn instantiate(formula: &Formula, n: i128) -> Formula {
    formula.clone().map(&mut |node| {
        let Formula::Var(name, _) = &node else { return node };
        let base = name.split('#').next().unwrap();
        match base {
            "num_vars" => Formula::Int(n),
            "num_lits" => Formula::Int(2 * n),
            // `self*.0#e` is the ENTRY value (the vac stale-read seal's spelling,
            // 2026-09-30), i.e. the initially empty Prober's 0 — only a version token
            // names the stored `n`.
            "self*.0" if name.contains('#') && !name.ends_with("#e") => Formula::Int(n),
            "self*.0" | "self*.1" | "self*.2" | "self*.3" | "_4" | "_7" | "_12" | "_17" | "_8*"
            | "_13*" | "_18*" => Formula::Int(0),
            "_3" => Formula::Bool(false),
            "_6" | "_11" | "_16" => Formula::Bool(true),
            _ => panic!("unmodeled fixture variable: {name}"),
        }
    })
}

#[test]
fn reachable_oversized_resizes_have_concrete_counterexamples() {
    for vc in obligations() {
        let instance = instantiate(&vc.formula, 1 << 28);
        assert!(instance.free_variables().is_empty());
        assert!(
            trust_router::violation_is_forced(&instance),
            "line {} lost a reachable allocation violation: {:?}",
            vc.location.line_start,
            vc.formula,
        );
    }
}

#[test]
fn small_resizes_do_not_violate_the_budget() {
    for vc in obligations() {
        for n in 1..=16 {
            let instance = instantiate(&vc.formula, n);
            assert!(instance.free_variables().is_empty());
            assert!(trust_router::violation_is_forced(&Formula::Not(Box::new(instance))));
        }
    }
}

#[test]
fn symbolic_saturating_counts_are_not_guaranteed_over_budget() {
    for vc in obligations() {
        assert!(!trust_router::alloc_over_ceiling_forced(&vc.formula), "{:?}", vc.formula);
    }
}
