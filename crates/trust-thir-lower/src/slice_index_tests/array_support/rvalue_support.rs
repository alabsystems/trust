//! Value temporaries and actual local places deliberately have different read order.

use super::*;

const ARRAYS: [&str; 4] =
    ["cast_reference_value", "reference_place", "block_array_value", "cast_array_value"];

fn module() -> Module {
    super::super::module("TRUST_INDEX_RVALUE_IR")
}

fn check_subject(module: &Module) {
    let mut cases = 0;
    for name in ARRAYS.into_iter().chain(["cast_slice_value"]) {
        let f = function(module, name);
        let rows: Vec<_> =
            module.proof_obligations.iter().filter(|r| r.function == Some(f.id)).collect();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].status, ProofStatus::Pending);
        assert_eq!(
            f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .filter(|n| matches!(n.inst, Inst::Assert { .. }))
                .count(),
            1
        );
    }
    for name in ARRAYS {
        for index in [0, 1, 2, 3, 4, u64::MAX] {
            let expected = if index >= 4 {
                Outcome::Panic
            } else {
                Outcome::Returned(if name == "reference_place" { B } else { A }[index as usize])
            };
            assert_eq!(run(module, name, index), expected, "{name}: index={index}");
            cases += 1;
        }
    }
    assert_eq!(cases, 24);
    let slice_cases = super::super::support::observe_rvalue_slice_cases(module);
    assert_eq!(slice_cases.len(), 8);
    for observation in slice_cases {
        assert!(observation.agrees(), "slice temporary changed: {observation:?}");
    }
}

#[test]
#[ignore = "requires a freshly emitted compiler-bound index value-temporary module"]
fn actual_index_bases_distinguish_places_from_value_temporaries() {
    check_subject(&module());
}

#[test]
#[ignore = "requires the fixed subject; changed IR is diagnostic only"]
fn actual_index_value_temporary_controls_detect_recaptured_bases() {
    let module = module();
    check_subject(&module);
    for name in ARRAYS {
        let mut changed = module.clone();
        let f = changed.functions.iter_mut().find(|f| f.name == name).unwrap();
        let wrong_position = usize::from(name != "reference_place");
        let wrong = f.blocks.iter().find(|b| b.id == f.entry).unwrap().params[wrong_position].0;
        let mut edits = 0;
        for n in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::ExtractElement { array, .. } = &mut n.inst {
                assert_ne!(*array, wrong);
                *array = wrong;
                edits += 1;
            }
        }
        assert_eq!(edits, 1);
        assert_eq!(
            run(&changed, name, 0),
            Outcome::Returned(if wrong_position == 0 { A[0] } else { B[0] })
        );
    }
    super::super::support::check_rvalue_slice_mutants(&module);
}
