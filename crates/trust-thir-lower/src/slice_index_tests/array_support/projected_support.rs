//! Both the referent and a direct reference variable are read after index effects.

use super::*;

const PROJECTED: [&str; 2] = ["reseat_deref_pointee", "change_pointer_not_pointee"];

fn module() -> Module {
    super::super::module("TRUST_ARRAY_PROJECTED_IR")
}

fn check_subject(module: &Module) {
    let mut cases = 0;
    for name in PROJECTED {
        let f = function(module, name);
        assert_eq!(
            f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .filter(|n| matches!(n.inst, Inst::Assert { .. }))
                .count(),
            1
        );
        let obligations: Vec<_> =
            module.proof_obligations.iter().filter(|r| r.function == Some(f.id)).collect();
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].status, ProofStatus::Pending);
        for index in [0, 1, 2, 3, 4, u64::MAX] {
            let expected =
                if index >= 4 { Outcome::Panic } else { Outcome::Returned(B[index as usize]) };
            assert_eq!(run(module, name, index), expected, "{name}: index={index}");
            cases += 1;
        }
    }
    assert_eq!(cases, 12);
    // Deliberately retained in the corresponding actual producer census, not
    // silently counted as executed here. A later lowering increment may add them.
    eprintln!(
        "unexecuted siblings: reseat_tuple_field, call_base_runs_once; make_array has an external callee"
    );
}

#[test]
#[ignore = "requires freshly emitted, compiler-bound array-reference-place module"]
fn actual_array_reference_places_preserve_pointee_and_reference_reassignment() {
    check_subject(&module());
}

#[test]
#[ignore = "requires the fixed subject; mutated IR is diagnostic only"]
fn actual_array_reference_place_controls_detect_old_pointer_or_pointee() {
    let module = module();
    check_subject(&module);
    for name in PROJECTED {
        let mut stale = module.clone();
        let f = stale.functions.iter_mut().find(|f| f.name == name).unwrap();
        let original = f.blocks.iter().find(|b| b.id == f.entry).unwrap().params[0].0;
        let mut changed = 0;
        for node in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::ExtractElement { array, .. } = &mut node.inst {
                assert_ne!(*array, original);
                *array = original;
                changed += 1;
            }
        }
        assert_eq!(changed, 1);
        assert_eq!(run(&stale, name, 0), Outcome::Returned(A[0]));
    }
}
