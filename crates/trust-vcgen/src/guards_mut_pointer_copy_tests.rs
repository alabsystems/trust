//! Trust (2026-10-07, VEC-LEN-PARAM-COPY-1): the `Vec` length-stability oracle
//! (`local_mut_borrows_may_resize`, behind `coll_base_len_stable` and
//! `panic_calls::collection_abstract_len_with_base`) sees a `&mut Vec` POINTER handed
//! to a callee by copy or move, not only a `&mut (*v)` reborrow of it.
//!
//! Real MIR passes a `&mut Vec` parameter straight to `Vec::truncate` as `copy _1`
//! (no reborrow). The oracle looked only at `Rvalue::Ref { mutable: true }` /
//! `AddressOf` OF the base, so for
//! `fn(v: &mut Vec<u8>) { let n = v.len(); for i in 0..n { v.truncate(i); v[i] = 1 } }`
//! it answered "stable" and the `_k == v` length tie was emitted; only the
//! path-definition kill of the `&mut` parameter kept the index refuted.
//!
//! The fixtures are the real MIR of `tests/fixtures/vec_len_loop_head/` (sources in
//! `tests/vec_len_loop_head_realmir.rs`), dumped by the stage 1 of `7be75e9a80`.

use super::*;

const TRUNCATES: &str = include_str!("../tests/fixtures/vec_len_loop_head/truncates.json");
const POPS: &str = include_str!("../tests/fixtures/vec_len_loop_head/pops.json");
const ESCAPES: &str = include_str!("../tests/fixtures/vec_len_loop_head/escapes.json");
const REASSIGNS: &str = include_str!("../tests/fixtures/vec_len_loop_head/reassigns.json");
const POP_AFTER_INDEX: &str =
    include_str!("../tests/fixtures/vec_len_loop_head/pop_after_index.json");
const PUSH_THEN_RW: &str = include_str!("../tests/fixtures/vec_len_loop_head/push_then_rw.json");
const RW_THEN_TRUNCATE: &str =
    include_str!("../tests/fixtures/vec_len_loop_head/rw_then_truncate.json");
const OPAQUE_THEN_RW: &str =
    include_str!("../tests/fixtures/vec_len_loop_head/opaque_then_rw.json");
const RW_VEC: &str = include_str!("../tests/fixtures/vec_len_loop_head/rw_vec.json");
const RW_VEC_OFF_BY_ONE: &str =
    include_str!("../tests/fixtures/vec_len_loop_head/rw_vec_off_by_one.json");
const RO_SLICE: &str = include_str!("../tests/fixtures/vec_len_loop_head/ro_slice.json");

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// `_1` is the `&mut Vec<u8>` parameter `v` in every `&mut Vec` fixture.
fn param_is_mut_vec(func: &VerifiableFunction) -> bool {
    matches!(&func.body.locals[1].ty, Ty::Ref { mutable: true, inner } if matches!(inner.as_ref(), Ty::Seq { .. }))
}

/// Every call whose arg 0 is the whole local `local`, by copy or move.
fn calls_taking_whole(func: &VerifiableFunction, local: usize) -> Vec<String> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: callee, args, .. }
                if matches!(args.first(), Some(Operand::Copy(p) | Operand::Move(p))
                    if p.local == local && p.projections.is_empty()) =>
            {
                Some(callee.clone())
            }
            _ => None,
        })
        .collect()
}

/// No `&mut`/`&raw` of the parameter anywhere: the resize reaches the callee ONLY as
/// the pointer itself. This is what made the old oracle blind (vacuity guard).
fn no_mut_borrow_of(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().all(|b| {
        b.stmts.iter().all(|s| {
            !matches!(s, Statement::Assign {
                rvalue: Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place), ..
            } if place.local == local)
        })
    })
}

#[test]
fn a_mut_vec_parameter_copied_into_a_resizer_may_resize() {
    for (name, mir, resizer) in [
        ("truncates", TRUNCATES, "alloc::vec::Vec::<u8>::truncate"),
        ("pops", POPS, "alloc::vec::Vec::<u8>::pop"),
        ("pop_after_index", POP_AFTER_INDEX, "alloc::vec::Vec::<u8>::pop"),
        ("push_then_rw", PUSH_THEN_RW, "alloc::vec::Vec::<u8>::push"),
        ("rw_then_truncate", RW_THEN_TRUNCATE, "alloc::vec::Vec::<u8>::truncate"),
    ] {
        let func = parse(mir);
        assert!(param_is_mut_vec(&func), "{name}: vacuity guard, `_1: &mut Vec<u8>`");
        assert!(no_mut_borrow_of(&func, 1), "{name}: vacuity guard, no `&mut (*_1)` reborrow");
        assert!(
            calls_taking_whole(&func, 1).iter().any(|c| c == resizer),
            "{name}: vacuity guard, `{resizer}` receives `_1` whole: {:?}",
            calls_taking_whole(&func, 1)
        );
        assert!(local_mut_borrows_may_resize(&func, 1), "{name}: `{resizer}(copy _1)` resizes");
    }
}

#[test]
fn a_mut_vec_parameter_given_to_an_unknown_callee_or_written_through_may_resize() {
    // `escapes`/`opaque_then_rw`: `opaque(copy _1)`, a user function. `reassigns`:
    // `drop((*_1)); (*_1) = move _11` — `*v = Vec::new()`.
    for (name, mir) in
        [("escapes", ESCAPES), ("opaque_then_rw", OPAQUE_THEN_RW), ("reassigns", REASSIGNS)]
    {
        let func = parse(mir);
        assert!(param_is_mut_vec(&func), "{name}: vacuity guard");
        assert!(no_mut_borrow_of(&func, 1), "{name}: vacuity guard, no `&mut (*_1)` reborrow");
        assert!(local_mut_borrows_may_resize(&func, 1), "{name}");
    }
}

#[test]
fn a_mut_vec_parameter_used_only_by_std_index_and_len_stays_stable() {
    // The negative control: `rw_vec` hands `copy _1` to std's own
    // `<Vec<u8> as IndexMut<usize>>::index_mut` and reads `len` through `&(*_1)`.
    // Neither changes the length; the fix must keep this base stable.
    for (name, mir) in [("rw_vec", RW_VEC), ("rw_vec_off_by_one", RW_VEC_OFF_BY_ONE)] {
        let func = parse(mir);
        assert!(param_is_mut_vec(&func), "{name}: vacuity guard");
        let whole = calls_taking_whole(&func, 1);
        assert!(
            !whole.is_empty()
                && whole
                    .iter()
                    .all(|c| c
                        .starts_with("<alloc::vec::Vec<u8> as core::ops::index::IndexMut<usize>>")),
            "{name}: vacuity guard, `_1` reaches std's `IndexMut` whole: {whole:?}"
        );
        assert!(!local_mut_borrows_may_resize(&func, 1), "{name}: only length-benign uses");
    }
    // A shared slice parameter is never a mutable pointer: unchanged.
    let func = parse(RO_SLICE);
    assert!(!local_mut_borrows_may_resize(&func, 1), "ro_slice");
}

#[test]
fn std_index_mut_re_pointed_at_a_user_function_may_resize() {
    // The benign set is std's own: the same `rw_vec` with its `index_mut` callee
    // renamed to a user function (crate identity included) is a resize.
    let mut func = parse(RW_VEC);
    let mut touched = 0;
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: callee, callee_key, .. } = &mut b.terminator
            && callee.ends_with("::index_mut")
        {
            *callee = "veclen3::my_index_mut".to_string();
            if let Some(key) = callee_key {
                key.krate_is_real_sysroot = false;
                key.krate_name = "veclen3".to_string();
            }
            touched += 1;
        }
    }
    assert_eq!(touched, 1, "vacuity guard: one `index_mut`");
    assert!(local_mut_borrows_may_resize(&func, 1));
}

#[test]
fn a_copy_of_the_pointer_into_another_local_is_followed() {
    // `_n = copy _1; truncate(move _n)`: the alias closure reaches `_n`, and `_n`'s
    // own whole-local use by `truncate` is a resize. Built from `truncates` by
    // routing its `truncate` receiver through a fresh `&mut Vec` local.
    let mut func = parse(TRUNCATES);
    let fresh = func.body.locals.len();
    let mut decl = func.body.locals[1].clone();
    decl.index = fresh;
    decl.name = None;
    func.body.locals.push(decl);
    let mut touched = 0;
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: callee, args, .. } = &mut b.terminator
            && callee == "alloc::vec::Vec::<u8>::truncate"
        {
            args[0] = Operand::Move(Place::local(fresh));
            b.stmts.push(Statement::Assign {
                place: Place::local(fresh),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            });
            touched += 1;
        }
    }
    assert_eq!(touched, 1, "vacuity guard: one `truncate`");
    assert!(local_mut_borrows_may_resize_one(&func, fresh), "the alias itself resizes");
    assert!(!local_mut_borrows_may_resize_one(&func, 1), "`_1` alone only copies");
    assert!(local_mut_borrows_may_resize(&func, 1), "the closure of `_1` resizes");
}

#[test]
fn a_pointer_stored_into_an_aggregate_or_cast_may_resize() {
    // An escape of the pointer itself, not through a call: the `rw_vec` base with one
    // extra statement each. Every other mention is counted against the base.
    for rvalue in [
        Rvalue::Aggregate(trust_types::AggregateKind::Tuple, vec![Operand::Copy(Place::local(1))]),
        Rvalue::Cast(
            Operand::Copy(Place::local(1)),
            Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
        ),
    ] {
        let mut func = parse(RW_VEC);
        let fresh = func.body.locals.len();
        let mut decl = func.body.locals[1].clone();
        decl.index = fresh;
        decl.name = None;
        func.body.locals.push(decl);
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(fresh),
            rvalue: rvalue.clone(),
            span: SourceSpan::default(),
        });
        assert!(local_mut_borrows_may_resize(&func, 1), "{rvalue:?}");
    }
}
