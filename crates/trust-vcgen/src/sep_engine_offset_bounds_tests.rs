// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache 2.0

//! Check the offset obligation itself, independently of later memory accesses.
//! Model regressions do not establish compiler proof authority.

use super::*;
use crate::abstract_interp::discharge::try_eval_boolean;
use crate::abstract_interp::{AbstractDomain, Interval, IntervalDomain};

fn offset_rows(function: &VerifiableFunction) -> Vec<VerificationCondition> {
    check_sep_unsafe(function)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message }
            if message.contains("[unsafe:sep:offset]"))
        })
        .collect()
}

#[test]
fn concrete_pointer_offset_uses_slice_extent_and_allows_one_past() {
    // Real extracted MIR: fn(s: &[u8], i: usize) -> *const u8 {
    //     unsafe { s.as_ptr().add(i) }
    // }
    let function: VerifiableFunction =
        serde_json::from_str(include_str!("../tests/fixtures/sep_add_past_end_mir.json")).unwrap();
    let rows = offset_rows(&function);
    assert_eq!(rows.len(), 1, "the unsafe offset must retain its own obligation");
    let mut mismatches = Vec::new();
    for len in [0, 1, 8, 64] {
        for count in [0, 1, len, len + 1] {
            let mut values = IntervalDomain::top();
            values.set("s__slice_len".into(), Interval::constant(len));
            values.set("i".into(), Interval::constant(count));
            let actual = try_eval_boolean(&rows[0].formula, &values);
            if actual != Some(count > len) {
                mismatches.push((len, count, actual));
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "incorrect pointer offset bounds: {mismatches:?}; {:?}",
        rows[0].formula
    );
}

fn raw(pointee: Ty) -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(pointee) }
}

fn constant(n: i128) -> Operand {
    Operand::Constant(trust_types::ConstValue::Int(n))
}

fn array_engine(pointee: Ty) -> SepEngine {
    let mut engine = SepEngine::new("offset_range_model").with_local_tys(vec![
        Ty::Unit,
        Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
        raw(pointee.clone()),
        raw(pointee.clone()),
        Ty::usize(),
        raw(pointee),
    ]);
    engine.interpret_address_of(&Place::local(2), &Place::local(1), false, &SourceSpan::default());
    engine.vcs.clear();
    engine
}

fn call(engine: &mut SepEngine, method: &str, args: &[Operand], dest: usize) {
    let key = super::tests::fixture_key(method).expect("authenticated fixture operation");
    engine.interpret_call(
        method,
        args,
        &Place::local(dest),
        &SourceSpan::default(),
        false,
        Some(&key),
    );
}

fn offset(engine: &mut SepEngine, src: usize, count: i128, dest: usize, wrapping: bool) {
    call(
        engine,
        if wrapping {
            "core::ptr::const_ptr::wrapping_offset"
        } else {
            "core::ptr::const_ptr::offset"
        },
        &[Operand::Copy(Place::local(src)), constant(count)],
        dest,
    );
}

fn last_offset(engine: &SepEngine) -> &Formula {
    &engine
        .vcs
        .iter()
        .rev()
        .find(|vc| {
            matches!(&vc.kind,
        VcKind::Assertion { message } if message.contains("[unsafe:sep:offset]"))
        })
        .expect("an unsafe offset retains its bounds row")
        .formula
}

fn assert_offset(engine: &SepEngine, expected: Option<bool>) {
    let formula = last_offset(engine);
    assert_eq!(try_eval_boolean(formula, &IntervalDomain::top()), expected, "{formula:?}");
}

#[test]
fn concrete_offsets_scale_element_width_and_include_both_endpoints() {
    for (pointee, width) in [(Ty::u8(), 1), (Ty::Int { width: 32, signed: false }, 4)] {
        for count in [-65, -1, 0, 1, 15, 16, 17, 63, 64, 65] {
            let mut engine = array_engine(pointee.clone());
            offset(&mut engine, 2, count, 3, false);
            assert_offset(&engine, Some(count < 0 || count * width > 64));
        }
    }
}

#[test]
fn nonwrapping_offset_checks_source_even_when_destination_returns_inside() {
    for (start, count, invalid) in [
        (-1, 1, true),
        (65, -1, true),
        (-1, 0, false),
        (65, 0, false),
        (64, -64, false),
        (0, 64, false),
        (63, 1, false),
        (64, 1, true),
        (32, -33, true),
        (32, -32, false),
    ] {
        let mut engine = array_engine(Ty::u8());
        offset(&mut engine, 2, start, 3, true);
        assert!(engine.vcs.is_empty(), "safe wrapping construction emits no offset row");
        offset(&mut engine, 3, count, 3, false);
        assert_offset(&engine, Some(invalid));
    }
}

#[test]
fn offset_reassignment_preserves_the_old_plain_copy_alias() {
    let mut engine = array_engine(Ty::u8());
    offset(&mut engine, 2, 64, 3, true);
    engine.interpret_assign(
        &Place::local(5),
        &Rvalue::Use(Operand::Copy(Place::local(3))),
        &SourceSpan::default(),
    );
    offset(&mut engine, 3, -64, 3, false);
    assert_offset(&engine, Some(false));
    offset(&mut engine, 5, 1, 0, false);
    assert_offset(&engine, Some(true));
}

#[test]
fn zero_sized_offsets_and_unknown_stride_zero_need_no_allocation_bounds() {
    for count in [i128::from(i64::MIN), -1, 0, 1, i128::from(i64::MAX)] {
        let mut engine = array_engine(Ty::Unit);
        // Deliberately untracked source: zero-byte movement needs no allocation.
        engine.local_to_ptr.remove(&2);
        offset(&mut engine, 2, count, 3, false);
        assert_offset(&engine, Some(false));
    }
    // An unsized pointee has no modeled byte stride.
    let mut engine = array_engine(Ty::Slice { elem: Box::new(Ty::u8()) });
    offset(&mut engine, 2, 1, 3, false);
    assert_offset(&engine, None);
    offset(&mut engine, 2, 0, 3, false);
    assert_offset(&engine, Some(false));
}

#[test]
fn unknown_provenance_retains_a_nonzero_offset_obligation() {
    let mut engine = array_engine(Ty::u8());
    engine.local_to_ptr.remove(&2);
    offset(&mut engine, 2, 1, 3, false);
    assert_offset(&engine, None);
    offset(&mut engine, 2, 0, 3, false);
    assert_offset(&engine, Some(false));
}

#[test]
fn one_past_offset_does_not_authorize_a_nonempty_read() {
    let mut engine = array_engine(Ty::u8());
    offset(&mut engine, 2, 64, 3, false);
    assert_offset(&engine, Some(false));
    call(&mut engine, "core::ptr::read", &[Operand::Copy(Place::local(3))], 0);
    let bounds: Vec<_> = engine
        .vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::CopyBoundsViolation { .. }))
        .collect();
    assert_eq!(bounds.len(), 1);
    assert_eq!(try_eval_boolean(&bounds[0].formula, &IntervalDomain::top()), Some(true));
}

#[test]
fn loaded_pointer_value_does_not_inherit_its_slice_container_bounds() {
    // Typed model variation of the real extracted fixture, not a newly extracted
    // compiler artifact: &[ *const u8 ], then load (*s)[i] and offset that value.
    let mut function: VerifiableFunction =
        serde_json::from_str(include_str!("../tests/fixtures/sep_add_past_end_mir.json")).unwrap();
    function.body.locals[1].ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(raw(Ty::u8())) }) };
    function.body.locals[3].ty = raw(raw(Ty::u8()));
    function.body.locals.push(trust_types::LocalDecl {
        index: 4,
        ty: raw(Ty::u8()),
        name: Some("loaded".into()),
    });
    let block = &mut function.body.blocks[1];
    block.stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 1,
            projections: vec![Projection::Deref, Projection::Index(2)],
        })),
        span: SourceSpan::default(),
    });
    let Terminator::Call { args, .. } = &mut block.terminator else { panic!("offset call") };
    args[0] = Operand::Copy(Place::local(4));
    args[1] = constant(1);
    let rows = offset_rows(&function);
    assert_eq!(rows.len(), 1);
    let mut values = IntervalDomain::top();
    values.set("s__slice_len".into(), Interval::constant(64));
    values.set("i".into(), Interval::constant(0));
    assert_eq!(
        try_eval_boolean(&rows[0].formula, &values),
        None,
        "a container may store a null or dangling pointer: {:?}",
        rows[0].formula
    );
}

#[test]
fn projected_call_source_and_count_cannot_reuse_parent_local_bounds() {
    let mut engine = array_engine(Ty::u8());
    call(
        &mut engine,
        "core::ptr::const_ptr::offset",
        &[Operand::Copy(Place { local: 2, projections: vec![Projection::Deref] }), constant(1)],
        3,
    );
    assert_offset(&engine, None);
    call(
        &mut engine,
        "core::ptr::const_ptr::offset",
        &[Operand::Copy(Place::local(2)), Operand::Copy(Place::field(4, 0))],
        3,
    );
    let mut values = IntervalDomain::top();
    values.set("_4".into(), Interval::constant(0));
    assert_eq!(try_eval_boolean(last_offset(&engine), &values), None);
}

#[test]
fn binary_subtract_preserves_the_direction_and_projected_count_is_opaque() {
    let mut engine = array_engine(Ty::u8());
    engine.interpret_assign(
        &Place::local(3),
        &Rvalue::BinaryOp(trust_types::BinOp::Sub, Operand::Copy(Place::local(2)), constant(1)),
        &SourceSpan::default(),
    );
    assert_offset(&engine, Some(true));
    engine.interpret_assign(
        &Place::local(3),
        &Rvalue::BinaryOp(
            trust_types::BinOp::Sub,
            Operand::Copy(Place::local(2)),
            Operand::Copy(Place::field(4, 0)),
        ),
        &SourceSpan::default(),
    );
    let mut values = IntervalDomain::top();
    values.set("_4".into(), Interval::constant(0));
    assert_eq!(try_eval_boolean(last_offset(&engine), &values), None);
}

#[test]
fn nonzero_offset_of_freed_allocation_is_invalid_but_zero_remains_valid() {
    for path_scoped in [false, true] {
        for count in [0, 1, 64] {
            let mut engine = array_engine(Ty::u8());
            let name = engine.local_to_ptr[&2].clone();
            let prov = engine.heap.pointer(&name).unwrap().provenance;
            if path_scoped {
                engine.heap.set_path_freed(vec![prov]);
            } else {
                engine.heap.free(prov);
            }
            offset(&mut engine, 2, count, 3, false);
            assert_offset(&engine, Some(count != 0));
            if path_scoped {
                engine.heap.set_path_freed(vec![]);
                offset(&mut engine, 2, count, 3, false);
                assert_offset(&engine, Some(false));
            }
        }
    }
}

#[test]
fn pointer_loaded_from_known_storage_keeps_its_own_unknown_provenance() {
    let mut engine = array_engine(Ty::u8());
    // Model a reference to pointer storage within the known 64-byte region.
    // The stored pointer may be null, independently of that region's validity.
    engine.local_tys[5] =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(raw(Ty::u8())) }) };
    engine.local_to_ptr.insert(5, engine.local_to_ptr[&2].clone());
    engine.interpret_assign(
        &Place::local(3),
        &Rvalue::Use(Operand::Copy(Place {
            local: 5,
            projections: vec![Projection::Deref, Projection::Index(4)],
        })),
        &SourceSpan::default(),
    );
    assert!(!engine.local_to_ptr.contains_key(&3));
    offset(&mut engine, 3, 1, 3, false);
    assert_offset(&engine, None);
}

#[test]
fn backing_field_offset_keeps_source_lower_bound_and_certified_assumption() {
    for certified in [false, true] {
        for (start, count, invalid) in
            [(-1, 1, true), (65, -1, true), (0, 64, false), (64, 1, true), (-1, 0, false)]
        {
            let mut engine = array_engine(Ty::u8())
                .with_field_backing(vec![(0, 1)])
                .with_backing_certified(certified);
            engine.field_loads.insert(2, (7, 0));
            engine.field_load_var.insert((7, 1), Formula::Int(64));
            // Each offset result is a one-value local, so it carries the tag on.
            engine.backing_single_value_locals.extend([3, 5]);
            let (size, _) = engine.backing_alloc_size(7, 0, 1);
            let Formula::Var(size_name, _) = size else {
                panic!("backing extent must remain opaque")
            };
            offset(&mut engine, 2, start, 3, true);
            offset(&mut engine, 3, count, 5, false);
            let formula = last_offset(&engine);
            let mut values = IntervalDomain::top();
            values.set(size_name, Interval::constant(64));
            assert_eq!(try_eval_boolean(formula, &values), Some(invalid), "{formula:?}");
            assert_eq!(
                matches!(formula, Formula::And(parts) if parts.iter().any(|x| matches!(x, Formula::Ge(_, _)))),
                certified
            );
        }
    }
}

#[test]
fn offset_call_replaces_a_stale_destination_backing_tag() {
    let mut engine =
        array_engine(Ty::u8()).with_field_backing(vec![(0, 1)]).with_backing_certified(true);
    engine.field_loads.insert(3, (7, 0));
    engine.field_load_var.insert((7, 1), Formula::Int(128));
    offset(&mut engine, 2, 0, 3, false);
    assert!(!engine.field_loads.contains_key(&3), "the old destination is not the call result");
    offset(&mut engine, 3, 65, 3, false);
    assert_offset(&engine, Some(true));
}

#[test]
fn padded_tuple_pointee_never_uses_the_sum_of_its_field_sizes_as_stride() {
    let tuple = Ty::Tuple(vec![Ty::u8(), Ty::Int { width: 64, signed: false }]);
    for pointee in [tuple.clone(), Ty::Array { elem: Box::new(tuple), len: 2 }] {
        let mut engine = array_engine(pointee);
        // A nine-byte field sum would falsely allow seven elements in 64
        // bytes. Padding requires a layout fact that this model does not carry.
        offset(&mut engine, 2, 7, 3, false);
        assert_offset(&engine, None);
        offset(&mut engine, 2, 0, 3, false);
        assert_offset(&engine, Some(false));
    }
    let mut engine = array_engine(Ty::Tuple(vec![Ty::Unit, Ty::Tuple(vec![])]));
    offset(&mut engine, 2, 100, 3, false);
    assert_offset(&engine, Some(false));
}

fn offset_with_free_cfg(free_target: usize, conditional_before: bool) -> VerifiableFunction {
    // CFG model based on the real offset fixture. The added keyed deallocator
    // models its lifetime effect only; this is not newly extracted MIR.
    let mut function: VerifiableFunction =
        serde_json::from_str(include_str!("../tests/fixtures/sep_add_past_end_mir.json")).unwrap();
    let mut free = function.body.blocks[1].terminator.clone();
    let Terminator::Call { func, callee_key, args, dest, target, .. } = &mut free else {
        unreachable!()
    };
    *func = "alloc::alloc::dealloc".into();
    *callee_key = super::tests::fixture_key(func);
    assert!(callee_key.is_some());
    *args = vec![Operand::Copy(Place::local(3)), constant(0)];
    *dest = Place::local(4);
    *target = Some(BlockId(free_target));
    function.body.locals.push(trust_types::LocalDecl { index: 4, ty: Ty::Unit, name: None });
    function.body.blocks.push(trust_types::BasicBlock {
        id: BlockId(3),
        stmts: vec![],
        terminator: free,
    });
    if conditional_before {
        let Terminator::Call { target, .. } = &mut function.body.blocks[0].terminator else {
            unreachable!()
        };
        *target = Some(BlockId(4));
        function.body.blocks.push(trust_types::BasicBlock {
            id: BlockId(4),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        });
    } else {
        function.body.blocks[2].terminator = Terminator::Goto(BlockId(3));
    }
    function
}

#[test]
fn conditional_or_loop_deallocation_cannot_be_hidden_by_exact_bounds() {
    for function in [offset_with_free_cfg(1, true), offset_with_free_cfg(1, false)] {
        let after = blocks_after_global_dealloc(&function.body.blocks);
        assert!(after.contains(&1), "offset can be reached after free, independent of block order");
        assert!(!after.contains(&0));
        let rows = offset_rows(&function);
        assert_eq!(rows.len(), 1);
        let mut values = IntervalDomain::top();
        values.set("s__slice_len".into(), Interval::constant(64));
        values.set("i".into(), Interval::constant(1));
        assert_eq!(
            try_eval_boolean(&rows[0].formula, &values),
            None,
            "bounds must not erase the unresolved lifetime: {:?}",
            rows[0].formula
        );
        values.set("i".into(), Interval::constant(0));
        assert_eq!(try_eval_boolean(&rows[0].formula, &values), Some(false));
    }
}

#[test]
fn future_or_exclusive_deallocation_does_not_taint_an_earlier_offset() {
    for mut function in [offset_with_free_cfg(2, true), offset_with_free_cfg(4, false)] {
        if function.body.blocks.len() == 4 {
            function.body.blocks.push(trust_types::BasicBlock {
                id: BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            });
        }
        assert!(!blocks_after_global_dealloc(&function.body.blocks).contains(&1));
        let rows = offset_rows(&function);
        assert_eq!(rows.len(), 1);
        let mut values = IntervalDomain::top();
        values.set("s__slice_len".into(), Interval::constant(64));
        values.set("i".into(), Interval::constant(1));
        assert_eq!(
            try_eval_boolean(&rows[0].formula, &values),
            Some(false),
            "{:?}",
            rows[0].formula
        );
    }
}

/// KNOWN_HAZARDS "the 2026-09-25 offset repair proves a LOOP-CARRIED pointer's offset
/// row from its first-iteration offset": `p = p.add(1)` inside a loop. The forward walk
/// sees `p`'s first definition only, so its accumulated offset (0) bounded every
/// iteration's `add(1)` and the row proved. A loop-carried source takes no walk offset.
#[test]
fn loop_carried_source_takes_no_first_iteration_offset() {
    // Control: a straight-line `add(1)` from the array base proves.
    let mut engine = array_engine(Ty::u8());
    offset(&mut engine, 2, 1, 3, false);
    assert_offset(&engine, Some(false));

    // The same operation whose source is redefined around a back edge must not prove.
    let mut engine = array_engine(Ty::u8());
    engine.loop_carried_locals.insert(2);
    offset(&mut engine, 2, 1, 3, false);
    assert_offset(&engine, None);

    // Through a single-definition copy temporary that aliases the loop-carried local.
    let mut engine = array_engine(Ty::u8());
    engine.loop_carried_locals.insert(2);
    let name = engine.local_to_ptr[&2].clone();
    engine.local_to_ptr.insert(5, name);
    offset(&mut engine, 5, 1, 3, false);
    assert_offset(&engine, None);
}

fn assign_use(dest: usize, src: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(src))),
        span: SourceSpan::default(),
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> trust_types::BasicBlock {
    trust_types::BasicBlock { id: BlockId(id), stmts, terminator }
}

fn body(arg_count: usize, blocks: Vec<trust_types::BasicBlock>) -> trust_types::VerifiableBody {
    trust_types::VerifiableBody {
        locals: (0..5)
            .map(|index| trust_types::LocalDecl { index, ty: raw(Ty::u8()), name: None })
            .collect(),
        blocks,
        arg_count,
        return_ty: Ty::Unit,
        datatype_defs: Default::default(),
    }
}

#[test]
fn loop_carried_locals_need_a_back_edge_and_more_than_one_value() {
    // `_2` is written in both blocks; `_4` once; `_1` (a parameter when `arg_count` is
    // 1) once in the body, on top of its ENTRY definition.
    let blocks = |back: bool| {
        vec![
            block(0, vec![assign_use(2, 3)], Terminator::Goto(BlockId(1))),
            block(
                1,
                vec![assign_use(2, 3), assign_use(4, 3), assign_use(1, 3)],
                if back { Terminator::Goto(BlockId(0)) } else { Terminator::Return },
            ),
        ]
    };
    let carried =
        SepEngine::new("f").with_loop_carried_locals(&body(0, blocks(true))).loop_carried_locals;
    assert!(carried.contains(&2), "redefined across a back edge: {carried:?}");
    assert!(!carried.contains(&4), "defined once: {carried:?}");
    assert!(!carried.contains(&1), "a non-parameter defined once: {carried:?}");

    // A PARAMETER reassigned once in the loop holds two values (entry + body). The
    // first cut tallied body definitions only and missed it.
    let carried =
        SepEngine::new("f").with_loop_carried_locals(&body(1, blocks(true))).loop_carried_locals;
    assert!(carried.contains(&1), "a reassigned parameter: {carried:?}");

    let straight =
        SepEngine::new("f").with_loop_carried_locals(&body(1, blocks(false))).loop_carried_locals;
    assert!(straight.is_empty(), "no back edge, no loop-carried local: {straight:?}");
}

/// KNOWN_HAZARDS "a sub-object reference or `&raw` at offset 0 lets walk-derived size
/// rows PROVE an out-of-bounds access". `array_engine` holds `_1: [u8; 64]`; `_4` is the
/// index. A pointer to `_1[_4]` is NOT at offset 0, so `add(60)` from it must not be
/// bounded as if it were.
#[test]
fn subobject_borrow_takes_no_base_offset() {
    let element = Place { local: 1, projections: vec![Projection::Index(4)] };

    // Control: `&raw const _1` (the whole array) is at offset 0; `add(60)` proves.
    let mut engine = array_engine(Ty::u8());
    offset(&mut engine, 2, 60, 3, false);
    assert_offset(&engine, Some(false));

    // `&raw const _1[_4]`, then `add(60)`.
    let mut engine = array_engine(Ty::u8());
    engine.interpret_address_of(&Place::local(5), &element, false, &SourceSpan::default());
    offset(&mut engine, 5, 60, 3, false);
    assert_offset(&engine, None);
}

#[test]
fn subobject_reference_through_tracked_base_takes_no_base_offset() {
    // `&(*_2)[_4]` through the TRACKED base pointer (the hazard's `&(*s)[6]`), then
    // `add(60)`. It inherits `_2`'s concrete provenance, so before the fix the walk
    // read its offset as 0.
    let through_base =
        Place { local: 2, projections: vec![Projection::Deref, Projection::Index(4)] };
    let mut engine = array_engine(Ty::u8());
    engine.interpret_ref(&Place::local(5), &through_base, false);
    offset(&mut engine, 5, 60, 3, false);
    assert_offset(&engine, None);
}

/// A reborrow `&raw const (*p)` is wherever `p` points: after `p = base.add(60)` it is at
/// offset 60, so a further `add(10)` (byte 70 of 64) must be refuted, not checked from 0.
#[test]
fn reborrow_keeps_the_pointer_offset() {
    let reborrow = Place { local: 3, projections: vec![Projection::Deref] };
    let mut engine = array_engine(Ty::u8());
    offset(&mut engine, 2, 60, 3, false);
    engine.interpret_address_of(&Place::local(5), &reborrow, false, &SourceSpan::default());
    offset(&mut engine, 5, 10, 3, false);
    assert_offset(&engine, Some(true));

    // Control: from the base, `add(4)` after the reborrow stays in bounds.
    let mut engine = array_engine(Ty::u8());
    offset(&mut engine, 2, 60, 3, false);
    engine.interpret_address_of(&Place::local(5), &reborrow, false, &SourceSpan::default());
    offset(&mut engine, 5, 4, 3, false);
    assert_offset(&engine, Some(false));
}
