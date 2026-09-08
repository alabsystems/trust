// Trust: the checked-sub/add RESULT facts must not survive a store through a
// MUTABLE BORROW of the result local.
//
// `MIR_BORROW_REASSIGNED` is the compiler's OWN extracted verification input,
// captured verbatim with
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> probe.rs
//
// against
//
//   pub fn last_via_borrow(v: &[u8], b: usize) -> u8 {
//       if v.is_empty() { return 0; }
//       let mut idx = v.len() - 1;
//       let p = &mut idx;
//       *p = b;
//       v[idx]
//   }
//
// It is embedded INLINE rather than dropped in `tests/fixtures/` on purpose: a
// corpus-derived obligation count is ratcheted elsewhere and this lane must not
// perturb it.
//
// WHAT IS BEING PINNED. `build_checked_sub_result_facts` emits the global fact
// `(lhs < rhs) OR (idx == lhs - rhs)` for a whole-local copy of a
// `CheckedBinaryOp(Sub, ..)` result. Its definition scan counts only whole-local
// `Assign` places and `Call` dests, so the store `*p = b` — whose place local is
// `p`, not `idx` — was invisible to it; `idx` scored one definition and kept the
// fact. Conjoined and version-renamed onto the block terminal, the fact pins the
// MUTATED `idx` to `v.len() - 1` and deletes the out-of-bounds counterexample.
//
// Adding `local_mut_escapes` to that scan is what these rows gate: revert it and
// `borrow_reassigned_index_still_refutes` goes green->red.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

const MIR_BORROW_REASSIGNED: &str = r#"{"name":"last_via_borrow","def_path":"probe_borrow2::last_via_borrow","span":{"file":"probe_borrow2.rs","line_start":2,"col_start":0,"line_end":10,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Slice":{"elem":{"Int":{"width":8,"signed":false}}}}}},"name":"v"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"b"},{"index":3,"ty":"Bool","name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":"idx"},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":6,"ty":{"Tuple":[{"Int":{"width":64,"signed":false}},"Bool"]},"name":null},{"index":7,"ty":{"Ref":{"mutable":true,"inner":{"Int":{"width":64,"signed":false}}}},"name":"p"},{"index":8,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":9,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":10,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"core::slice::<impl [u8]>::is_empty","args":[{"Copy":{"local":1,"projections":[]}}],"dest":{"local":3,"projections":[]},"target":1,"span":{"file":"probe_borrow2.rs","line_start":3,"col_start":7,"line_end":3,"col_end":19},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":1,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Move":{"local":3,"projections":[]}},"targets":[[0,3]],"otherwise":2,"exhaustive_enum_unreachable":false,"span":{"file":"probe_borrow2.rs","line_start":3,"col_start":7,"line_end":3,"col_end":19}}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"probe_borrow2.rs","line_start":4,"col_start":15,"line_end":4,"col_end":16}}}],"terminator":{"Goto":6}},{"id":3,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"UnaryOp":["PtrMetadata",{"Copy":{"local":1,"projections":[]}}]},"span":{"file":"probe_borrow2.rs","line_start":6,"col_start":18,"line_end":6,"col_end":25}}},{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"CheckedBinaryOp":["Sub",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[1,64]}}]},"span":{"file":"probe_borrow2.rs","line_start":6,"col_start":18,"line_end":6,"col_end":29}}}],"terminator":{"Assert":{"cond":{"Move":{"local":6,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Sub"},"target":4,"span":{"file":"probe_borrow2.rs","line_start":6,"col_start":18,"line_end":6,"col_end":29},"unwind":"Continue"}}},{"id":4,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Use":{"Move":{"local":6,"projections":[{"Field":0}]}}},"span":{"file":"probe_borrow2.rs","line_start":6,"col_start":18,"line_end":6,"col_end":29}}},{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Ref":{"mutable":true,"place":{"local":4,"projections":[]}}},"span":{"file":"probe_borrow2.rs","line_start":7,"col_start":12,"line_end":7,"col_end":20}}},{"Assign":{"place":{"local":7,"projections":["Deref"]},"rvalue":{"Use":{"Copy":{"local":2,"projections":[]}}},"span":{"file":"probe_borrow2.rs","line_start":8,"col_start":4,"line_end":8,"col_end":10}}},{"Assign":{"place":{"local":8,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[]}}},"span":{"file":"probe_borrow2.rs","line_start":9,"col_start":6,"line_end":9,"col_end":9}}},{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"UnaryOp":["PtrMetadata",{"Copy":{"local":1,"projections":[]}}]},"span":{"file":"probe_borrow2.rs","line_start":9,"col_start":4,"line_end":9,"col_end":10}}},{"Assign":{"place":{"local":10,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":8,"projections":[]}},{"Copy":{"local":9,"projections":[]}}]},"span":{"file":"probe_borrow2.rs","line_start":9,"col_start":4,"line_end":9,"col_end":10}}}],"terminator":{"Assert":{"cond":{"Move":{"local":10,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":5,"span":{"file":"probe_borrow2.rs","line_start":9,"col_start":4,"line_end":9,"col_end":10},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":["Deref",{"Index":8}]}}},"span":{"file":"probe_borrow2.rs","line_start":9,"col_start":4,"line_end":9,"col_end":10}}}],"terminator":{"Goto":6}},{"id":6,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["b","Int"]},{"Int":0}]},{"Le":[{"Var":["b","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

/// One verdict per VC, from the REAL in-process ay backend, on a big stack (VC
/// generation and the solver search both overflow libtest's default stack).
fn verdicts(mir: &str) -> Vec<(VcKind, VerificationResult)> {
    let func: VerifiableFunction =
        serde_json::from_str(mir).expect("the captured MIR fixture must deserialize");
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = trust_router::Router::deterministic_in_process_ay(30_000);
            router.verify_all(&vcs).into_iter().map(|(vc, r)| (vc.kind, r)).collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

/// `*p = b` reseats `idx` to an arbitrary `usize`, so `v[idx]` is out of bounds
/// for every `b >= v.len()` — the fixture indexes a one-element slice at `b == 1`.
///
/// Killed by reverting `local_mut_escapes` out of the `stable` closure in
/// `build_checked_sub_result_facts`: the stale `idx == v.len() - 1` returns and
/// this row goes `Proved`.
#[test]
fn borrow_reassigned_index_still_refutes() {
    let rows = verdicts(MIR_BORROW_REASSIGNED);
    let bounds: Vec<_> =
        rows.iter().filter(|(k, _)| matches!(k, VcKind::SliceBoundsCheck)).collect();
    assert!(!bounds.is_empty(), "the bounds obligation must be generated at all");
    for (_, verdict) in bounds {
        assert!(
            !is_proved(verdict),
            "`let p = &mut idx; *p = b; v[idx]` is out of bounds at b >= v.len(); got {verdict:?}"
        );
    }
}

/// The over-correction guard: the `!v.is_empty()` guard is what makes
/// `v.len() - 1` underflow-free, and that proof comes from the guard, NOT from
/// the result fact — so it must SURVIVE the kill. Killed by any mutant that
/// drops the guard's path condition or the subtraction's operand ranges.
#[test]
fn the_guarded_length_subtraction_still_proves() {
    let rows = verdicts(MIR_BORROW_REASSIGNED);
    let subs: Vec<_> = rows
        .iter()
        .filter(|(k, _)| {
            matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Sub, .. })
        })
        .collect();
    assert!(!subs.is_empty(), "the subtraction obligation must be generated at all");
    for (_, verdict) in subs {
        assert!(
            is_proved(verdict),
            "`!v.is_empty()` makes `v.len() - 1` underflow-free; got {verdict:?}"
        );
    }
}
