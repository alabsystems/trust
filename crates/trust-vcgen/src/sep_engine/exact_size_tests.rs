//! Exercise actual memory-bound generation and routing, including physical padding.
use super::*;
use trust_types::{AggregateKind, BasicBlock, ConstValue, LocalDecl, UnwindEdge, VerifiableBody, VerificationResult};

#[derive(Clone, Copy, Debug)]
enum Access { Read, Slice, Copy }

fn padded() -> Ty { Ty::Tuple(vec![Ty::u32(), Ty::u8()]) }

fn access(ty: Ty, bytes: u64, operation: Access) -> VerifiableFunction {
    let ptr = |pointee| Ty::RawPtr { mutable: false, pointee: Box::new(pointee) };
    let mut_ptr = |pointee| Ty::RawPtr { mutable: true, pointee: Box::new(pointee) };
    let span = SourceSpan::default();
    let assign = |dest, rvalue| Statement::Assign { place: Place::local(dest), rvalue, span: span.clone() };
    let initialized = Rvalue::Aggregate(AggregateKind::Array,
        vec![Operand::Constant(ConstValue::Uint(0, 8)); usize::try_from(bytes).unwrap()]);
    let mut stmts = vec![
        assign(1, initialized.clone()),
        assign(2, Rvalue::AddressOf(false, Place::local(1))),
        assign(3, Rvalue::Cast(Operand::Move(Place::local(2)), ptr(ty.clone()))),
    ];
    let (callee, args) = match operation {
        Access::Read => ("core::ptr::read", vec![Operand::Copy(Place::local(3))]),
        Access::Slice => ("core::slice::raw::from_raw_parts", vec![
            Operand::Copy(Place::local(3)), Operand::Constant(ConstValue::Uint(1, 64))]),
        Access::Copy => {
            stmts.push(assign(4, initialized));
            stmts.push(assign(5, Rvalue::AddressOf(true, Place::local(4))));
            stmts.push(assign(6, Rvalue::Cast(Operand::Move(Place::local(5)), mut_ptr(ty.clone()))));
            ("core::ptr::copy", vec![Operand::Copy(Place::local(3)),
                Operand::Copy(Place::local(6)), Operand::Constant(ConstValue::Uint(1, 64))])
        }
    };
    let local = |index, ty| LocalDecl { index, ty, name: None };
    let buffer = Ty::Array { elem: Box::new(Ty::u8()), len: bytes };
    let return_ty = match operation {
        Access::Read => ty.clone(),
        Access::Slice => Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(ty.clone()) }) },
        Access::Copy => Ty::Unit,
    };
    VerifiableFunction {
        name: "layout_access".into(), def_path: "test::layout_access".into(), span: span.clone(),
        body: VerifiableBody {
            return_ty: return_ty.clone(), arg_count: 0, datatype_defs: Default::default(),
            locals: vec![local(0, return_ty), local(1, buffer.clone()), local(2, ptr(buffer.clone())),
                local(3, ptr(ty.clone())), local(4, buffer.clone()), local(5, mut_ptr(buffer)), local(6, mut_ptr(ty))],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable, func: callee.into(), args, dest: Place::local(0),
                target: Some(BlockId(1)), span, atomic: None, is_unsafe_sig: true,
                callee_identity: None, callee_key: super::tests::fixture_key(callee), is_foreign: false,
            } }, BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return }],
        },
        contracts: vec![], preconditions: vec![], postconditions: vec![], spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn table(ty: &Ty, sizes: &[Option<u64>]) -> crate::ElemSizeTable {
    let mut table = crate::ElemSizeTable::new();
    for size in sizes { table.record_ref(ty, *size); }
    table
}

fn bounds(func: &VerifiableFunction, context: &crate::VcgenContext) -> Vec<VerificationCondition> {
    crate::with_vcgen_context(context, || check_sep_unsafe(func)).into_iter()
        .filter(|vc| matches!(&vc.kind, VcKind::CopyBoundsViolation { .. })).collect()
}

fn assert_bound_sides(rows: &[VerificationCondition], operation: Access) {
    let mut directions: Vec<_> = rows.iter().map(|row| {
        let VcKind::CopyBoundsViolation { direction, .. } = &row.kind else { unreachable!() };
        direction.as_str()
    }).collect();
    directions.sort_unstable();
    let expected = if matches!(operation, Access::Copy) { vec!["dst", "src"] } else { vec!["src"] };
    assert_eq!(directions, expected, "every memory side must retain its own range row: {operation:?}");
}

fn solve(vc: &VerificationCondition) -> VerificationResult {
    // Use the production backend classes, not the AY-only test convenience:
    // CopyBoundsViolation's constant predicates reach the canonical evaluator;
    // in-process AY deliberately does not claim this kind today. No VC is
    // renamed or rewritten to give a solver permission it does not have.
    trust_router::Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(crate::test_router::test_ay_backend()),
        Box::new(trust_router::ty_backend::TyBackend),
        Box::new(trust_router::constant_folder::ConstantFolderBackend),
    ]).verify_all(std::slice::from_ref(vc))
        .into_iter().next().expect("one actual verdict").1
}

fn context(func: &VerifiableFunction, sizes: &[Option<u64>]) -> crate::VcgenContext {
    crate::VcgenContext::for_function(func.def_path.clone()).with_elem_sizes(table(&padded(), sizes), func)
}

fn assert_call_refusal(vcs: &[VerificationCondition], operation: Access) {
    if matches!(operation, Access::Read) {
        for requirement in ["null check", "allocation validity", "alignment check"] {
            let message = format!("[unsafe:sep:deref] {requirement} for *arg0_core_ptr_read");
            assert_eq!(vcs.iter().filter(|vc| matches!(&vc.kind,
                VcKind::Assertion { message: actual } if actual == &message)).count(), 1,
                "the call retains every existing fallback predicate: {message}");
        }
    }
    let specific: Vec<_> = vcs.iter().filter(|vc| match (&vc.kind, operation) {
        (VcKind::Assertion { message }, Access::Read) => {
            // This test needs a call-specific refusal witness, not a proof of
            // the independent heap/align models. The unconstrained null check
            // is linear; all three fallback rows remain present above.
            message == "[unsafe:sep:deref] null check for *arg0_core_ptr_read"
        }
        (VcKind::Assertion { message }, Access::Slice) => {
            message == "[unsafe:sep:call] unsafe function call to core::slice::raw::from_raw_parts (unverified)"
        }
        (VcKind::CopyBoundsViolation { callee, .. }, Access::Slice) => {
            callee == "core::slice::raw::from_raw_parts"
        }
        (VcKind::CopyBoundsViolation { callee, .. }, Access::Copy) => callee == "core::ptr::copy",
        _ => false,
    }).collect();
    assert_eq!(specific.len(), if matches!(operation, Access::Copy) { 2 } else { 1 },
        "this call keeps exactly its own fallback rows: {operation:?}");
    for row in specific {
        assert!(!matches!(solve(row), VerificationResult::Proved { .. }),
            "an unmodeled pointer/stride retains this call's unproved obligation: {row:?}");
    }
    if matches!(operation, Access::Copy) {
        let ranges: Vec<_> = vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::CopyBoundsViolation { .. }))
            .cloned().collect();
        assert_bound_sides(&ranges, operation);
    }
}

#[test]
fn padded_accesses_charge_the_complete_eight_bytes() {
    assert_eq!(std::mem::size_of::<(u32, u8)>(), 8, "native padding witness");
    for op in [Access::Read, Access::Slice, Access::Copy] {
        let func = access(padded(), 5, op);
        let rows = bounds(&func, &context(&func, &[Some(8)]));
        assert_bound_sides(&rows, op);
        for row in rows {
            let result = solve(&row);
            assert!(matches!(result, VerificationResult::Failed { .. }),
                "one padded value cannot fit a five-byte allocation: {result:?}, {row:?}");
        }
    }
}

#[test]
fn exact_padded_accesses_keep_the_in_bounds_positive_controls() {
    for op in [Access::Read, Access::Slice, Access::Copy] {
        let func = access(padded(), 8, op);
        let rows = bounds(&func, &context(&func, &[Some(8), Some(8)]));
        assert_bound_sides(&rows, op);
        for row in rows {
            let result = solve(&row);
            assert!(matches!(result, VerificationResult::Proved { .. }), "{result:?}, {row:?}");
        }
    }
}

#[test]
fn absent_unknown_and_conflicting_layouts_do_not_become_field_sums() {
    for op in [Access::Read, Access::Slice, Access::Copy] {
        let func = access(padded(), 5, op);
        for sizes in [vec![], vec![None], vec![Some(8), None], vec![Some(8), Some(12)]] {
            for row in bounds(&func, &context(&func, &sizes)) {
                assert!(!matches!(solve(&row), VerificationResult::Proved { .. }),
                    "the field sum cannot discharge a physical range: {sizes:?}, {row:?}");
            }
            let vcs = crate::with_vcgen_context(&context(&func, &sizes), || check_sep_unsafe(&func));
            // A stack-address liveness or alignment refusal cannot stand in for
            // this call's missing stride. Require its own precise fallback.
            assert_call_refusal(&vcs, op);
        }
    }
}

#[test]
fn a_layout_from_another_owner_or_changed_type_cannot_scale_an_access() {
    let func = access(padded(), 5, Access::Read);
    let wrong_owner = crate::VcgenContext::for_function("test::other")
        .with_elem_sizes(table(&padded(), &[Some(8)]), &func);
    assert!(bounds(&func, &wrong_owner).is_empty());
    let installed = context(&func, &[Some(8)]);
    let mut changed = func.clone();
    changed.body.locals[3].ty = Ty::RawPtr { mutable: false,
        pointee: Box::new(Ty::Tuple(vec![Ty::u32(), Ty::u32()])) };
    assert!(bounds(&changed, &installed).is_empty());
    // The bound table is still valid for its original function after the failed read.
    assert_eq!(bounds(&func, &installed).len(), 1);
}

#[test]
fn primitive_access_sizes_remain_exact_without_a_compiler_table() {
    for (ty, bytes) in [(Ty::u8(), 1), (Ty::u32(), 4), (Ty::Float { width: 64 }, 8)] {
        let func = access(ty, bytes, Access::Read);
        let rows = bounds(&func, &crate::VcgenContext::for_function(func.def_path.clone()));
        assert_eq!(rows.len(), 1);
        assert!(matches!(solve(&rows[0]), VerificationResult::Proved { .. }));
    }
}

#[test]
fn logical_widths_and_overflowing_arrays_never_mint_physical_extents() {
    let huge = Ty::Array { elem: Box::new(Ty::Array { elem: Box::new(Ty::u32()),
        len: u64::MAX }), len: u64::MAX };
    for ty in [Ty::Bv(8), Ty::Int { width: 7, signed: false }, Ty::Float { width: 7 }, huge] {
        let func = access(ty, 8, Access::Read);
        assert!(bounds(&func, &crate::VcgenContext::for_function(func.def_path.clone())).is_empty());
    }
}

#[test]
fn arrays_multiply_exact_padded_element_sizes() {
    let func = access(Ty::Array { elem: Box::new(padded()), len: 2 }, 15, Access::Read);
    let rows = bounds(&func, &context(&func, &[Some(8)]));
    assert_eq!(rows.len(), 1);
    assert!(matches!(solve(&rows[0]), VerificationResult::Failed { .. }),
        "two padded values need sixteen bytes, not ten: {:?}", rows[0]);
}

#[test]
fn whole_tuple_allocations_use_their_physical_extent() {
    let mut func = access(Ty::Int { width: 64, signed: false }, 8, Access::Read);
    func.body.locals[1].ty = padded();
    func.body.locals[2].ty = Ty::RawPtr { mutable: false, pointee: Box::new(padded()) };
    let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else { unreachable!() };
    *rvalue = Rvalue::Aggregate(AggregateKind::Tuple,
        vec![Operand::Constant(ConstValue::Uint(0, 32)), Operand::Constant(ConstValue::Uint(0, 8))]);
    let rows = bounds(&func, &context(&func, &[Some(8)]));
    assert_eq!(rows.len(), 1);
    assert!(matches!(solve(&rows[0]), VerificationResult::Proved { .. }),
        "the byte-range check sees eight real allocation bytes: {:?}", rows[0]);
    // No initialization, alignment, provenance or whole-operation proof is claimed.
}

#[test]
fn projected_pointer_values_do_not_borrow_the_holders_allocation_or_stride() {
    use trust_types::{AggregateKind, Projection};
    assert_eq!(std::mem::size_of::<(*const [u8; 32],)>(), 8, "native holder layout witness");
    let element = Ty::Array { elem: Box::new(Ty::u8()), len: 32 };
    let pointer = Ty::RawPtr { mutable: false, pointee: Box::new(element.clone()) };
    let holder = Ty::Tuple(vec![pointer]);
    for operation in [Access::Read, Access::Slice, Access::Copy] {
        let mut func = access(element.clone(), 5, operation);
        // holder=(pointer_into_five_byte_buffer,); r=&holder; call(r.0).
        // The eight-byte holder is not the pointer field's backing allocation.
        func.body.locals.push(LocalDecl { index: 7, ty: holder.clone(), name: None });
        func.body.locals.push(LocalDecl { index: 8,
            ty: Ty::Ref { mutable: false, inner: Box::new(holder.clone()) }, name: None });
        func.body.blocks[0].stmts.extend([
            Statement::Assign { place: Place::local(7), rvalue: Rvalue::Aggregate(
                AggregateKind::Tuple, vec![Operand::Copy(Place::local(3))]), span: SourceSpan::default() },
            Statement::Assign { place: Place::local(8), rvalue: Rvalue::Ref {
                mutable: false, place: Place::local(7) }, span: SourceSpan::default() },
        ]);
        let Terminator::Call { args, .. } = &mut func.body.blocks[0].terminator else { unreachable!() };
        args[0] = Operand::Copy(Place { local: 8,
            projections: vec![Projection::Deref, Projection::Field(0)] });
        let context = crate::VcgenContext::for_function(func.def_path.clone())
            .with_elem_sizes(table(&holder, &[Some(8)]), &func);
        let vcs = crate::with_vcgen_context(&context, || check_sep_unsafe(&func));
        assert_call_refusal(&vcs, operation);
        for row in bounds(&func, &context) {
            assert!(!matches!(solve(&row), VerificationResult::Proved { .. }),
                "projected source cannot use the holder's eight-byte range: {row:?}");
        }
    }
}


#[derive(Clone, Copy, Debug)]
enum ProjectedProducer { Ref, Raw, Cast, Call }

fn big_array() -> Ty { Ty::Array { elem: Box::new(Ty::u8()), len: 32 } }
fn raw_pointer(pointee: Ty, mutable: bool) -> Ty {
    Ty::RawPtr { mutable, pointee: Box::new(pointee) }
}
fn initialized_array(bytes: usize) -> Rvalue {
    Rvalue::Aggregate(AggregateKind::Array,
        vec![Operand::Constant(ConstValue::Uint(0, 8)); bytes])
}
fn assignment(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}
fn projected(local: usize, field: usize) -> Place {
    Place { local, projections: vec![trust_types::Projection::Field(field)] }
}
fn drive_identity_body(func: &VerifiableFunction) -> SepEngine {
    let mut engine = SepEngine::new(&func.def_path)
        .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect())
        .with_elem_sizes(func);
    for block in &func.body.blocks {
        for stmt in &block.stmts { engine.interpret_statement(stmt, &SourceSpan::default()); }
        engine.interpret_terminator(&block.terminator);
    }
    engine
}

// All buffers, holder fields, address temporaries, casts and call results have
// their real types. The bad field points into5; the separate sibling points into32.
fn projected_value_access(producer: ProjectedProducer) -> VerifiableFunction {
    let big = big_array();
    let pointer = raw_pointer(big.clone(), false);
    let reference = Ty::Ref { mutable: false, inner: Box::new(big.clone()) };
    let sibling = if matches!(producer, ProjectedProducer::Ref) { reference.clone() } else { pointer.clone() };
    let mut func = access(big.clone(), 5, Access::Read);
    for (index, ty) in [(7, big.clone()), (8, pointer.clone()),
        (9, Ty::Tuple(vec![pointer.clone(), sibling])),
        (10, raw_pointer(big.clone(), true)), (11, pointer.clone()), (12, reference)]
    { func.body.locals.push(LocalDecl { index, ty, name: None }); }
    let mut read = func.body.blocks[0].terminator.clone();
    let stmts = &mut func.body.blocks[0].stmts;
    stmts.push(assignment(Place::local(7), initialized_array(32)));
    stmts.push(assignment(Place::local(8), Rvalue::AddressOf(false, Place::local(7))));
    if matches!(producer, ProjectedProducer::Ref) {
        stmts.push(assignment(Place::local(12), Rvalue::Ref { mutable: false, place: Place::local(7) }));
    }
    stmts.push(assignment(Place::local(9), Rvalue::Aggregate(AggregateKind::Tuple,
        vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(
            if matches!(producer, ProjectedProducer::Ref) { 12 } else { 8 }))])));
    let casts = vec![
        assignment(Place::local(10), Rvalue::Cast(Operand::Copy(projected(9, 0)), raw_pointer(big, true))),
        assignment(Place::local(11), Rvalue::Cast(Operand::Copy(Place::local(10)), pointer.clone())),
    ];
    let Terminator::Call { args, target, .. } = &mut read else { unreachable!() };
    args[0] = Operand::Copy(Place::local(11));
    if matches!(producer, ProjectedProducer::Call) {
        *target = Some(BlockId(2));
        let callee = "core::ptr::const_ptr::cast";
        func.body.blocks[0].terminator = Terminator::Call {
            func: callee.into(), args: vec![Operand::Copy(Place::local(8))], dest: projected(9, 1),
            target: Some(BlockId(1)), span: SourceSpan::default(), unwind: UnwindEdge::Unreachable,
            atomic: None, is_unsafe_sig: false, callee_identity: None,
            callee_key: super::tests::fixture_key(callee), is_foreign: false,
        };
        func.body.blocks[1] = BasicBlock { id: BlockId(1), stmts: casts, terminator: read };
        func.body.blocks.push(BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return });
    } else {
        let value = match producer {
            ProjectedProducer::Ref => Rvalue::Ref { mutable: false, place: Place::local(7) },
            ProjectedProducer::Raw => Rvalue::AddressOf(false, Place::local(7)),
            ProjectedProducer::Cast => Rvalue::Cast(Operand::Copy(Place::local(8)), pointer),
            ProjectedProducer::Call => unreachable!(),
        };
        stmts.push(assignment(projected(9, 1), value));
        stmts.extend(casts);
        func.body.blocks[0].terminator = read;
    }
    func
}
fn assert_projected_value_refuses(producer: ProjectedProducer) {
    let func = projected_value_access(producer);
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    let vcs = crate::with_vcgen_context(&context, || check_sep_unsafe(&func));
    assert_call_refusal(&vcs, Access::Read);
    assert!(bounds(&func, &context).is_empty(), "no borrowed concrete sibling allocation");
    let engine = crate::with_vcgen_context(&context, || drive_identity_body(&func));
    assert!(!engine.local_to_ptr.contains_key(&9), "a field result cannot bind its holder: {producer:?}");
    if matches!(producer, ProjectedProducer::Raw) {
        assert_eq!(vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::Assertion { message }
            if message == "[unsafe:sep:addr_of] &raw const on `_7` (source liveness unverified)")).count(), 2,
            "whole and projected raw creations both keep their source rows");
    }
}
#[test]
fn projected_reference_store_then_field_cast_keeps_its_call_refusal() {
    assert_projected_value_refuses(ProjectedProducer::Ref);
}
#[test]
fn projected_raw_store_then_field_cast_keeps_its_source_and_call_rows() {
    assert_projected_value_refuses(ProjectedProducer::Raw);
}
#[test]
fn projected_cast_store_then_field_cast_cannot_bind_the_holder() {
    assert_projected_value_refuses(ProjectedProducer::Cast);
}
#[test]
fn projected_pointer_call_result_cannot_bind_the_holder() {
    assert_projected_value_refuses(ProjectedProducer::Call);
}

#[test]
fn whole_pointer_redefinitions_preserve_saved_value_heap_records() {
    for raw in [false, true] {
        let big = big_array();
        let pointer = raw_pointer(big.clone(), false);
        let value_ty = if raw { pointer.clone() } else { Ty::Ref { mutable: false, inner: Box::new(big.clone()) } };
        let mut func = access(big.clone(), 32, Access::Read);
        for (index, ty) in [(7, big), (8, value_ty.clone()), (9, value_ty), (10, pointer.clone())] {
            func.body.locals.push(LocalDecl { index, ty, name: None });
        }
        let make = |local| if raw { Rvalue::AddressOf(false, Place::local(local)) }
            else { Rvalue::Ref { mutable: false, place: Place::local(local) } };
        func.body.blocks[0].stmts.extend([
            assignment(Place::local(7), initialized_array(32)),
            assignment(Place::local(8), make(1)),
            assignment(Place::local(9), Rvalue::Use(Operand::Copy(Place::local(8)))),
            assignment(Place::local(8), make(7)),
            assignment(Place::local(10), Rvalue::Cast(Operand::Copy(Place::local(9)), pointer)),
        ]);
        let Terminator::Call { args, .. } = &mut func.body.blocks[0].terminator else { unreachable!() };
        args[0] = Operand::Copy(Place::local(10));
        let context = crate::VcgenContext::for_function(func.def_path.clone());
        let engine = crate::with_vcgen_context(&context, || drive_identity_body(&func));
        let saved = engine.local_to_ptr.get(&9).unwrap();
        let current = engine.local_to_ptr.get(&8).unwrap();
        assert_ne!(saved, current, "a new value cannot replace the saved alias's heap record");
        assert_ne!(engine.heap.pointer(saved).unwrap().provenance, engine.heap.pointer(current).unwrap().provenance);
        for local in [8, 9, 10] { assert_eq!(engine.local_alloc_size(local), Some(Formula::Int(32))); }
        let rows = bounds(&func, &context);
        assert_bound_sides(&rows, Access::Read);
        assert!(matches!(solve(&rows[0]), VerificationResult::Proved { .. }),
            "the saved whole-local positive still reaches its real32-byte allocation");
    }
}

#[test]
fn projected_deref_pointer_stores_preserve_root_heap_records_and_write_rows() {
    use trust_types::Projection;
    for raw in [false, true] {
        let big = big_array();
        let payload = if raw { raw_pointer(big.clone(), false) }
            else { Ty::Ref { mutable: false, inner: Box::new(big.clone()) } };
        let mut func = access(payload.clone(), 8, Access::Read);
        func.body.return_ty = Ty::Unit;
        func.body.locals[0].ty = Ty::Unit;
        func.body.locals[1].ty = payload.clone();
        func.body.locals[2].ty = raw_pointer(payload.clone(), false);
        let root = if raw { raw_pointer(payload.clone(), true) }
            else { Ty::Ref { mutable: true, inner: Box::new(payload.clone()) } };
        for (index, ty) in [(7, big.clone()), (8, big), (9, root),
            (10, raw_pointer(payload.clone(), true)), (11, payload.clone())]
        { func.body.locals.push(LocalDecl { index, ty, name: None }); }
        let value = |local| if raw { Rvalue::AddressOf(false, Place::local(local)) }
            else { Rvalue::Ref { mutable: false, place: Place::local(local) } };
        let root_value = if raw { Rvalue::AddressOf(true, Place::local(1)) }
            else { Rvalue::Ref { mutable: true, place: Place::local(1) } };
        func.body.blocks[0].stmts = vec![
            assignment(Place::local(7), initialized_array(32)),
            assignment(Place::local(8), initialized_array(32)),
            assignment(Place::local(1), value(7)),
            assignment(Place::local(9), root_value),
            assignment(Place::local(10), Rvalue::Cast(Operand::Copy(Place::local(9)), raw_pointer(payload.clone(), true))),
            assignment(Place { local: 9, projections: vec![Projection::Deref] }, value(8)),
            assignment(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(10)), raw_pointer(payload.clone(), false))),
        ];
        let Terminator::Call { args, dest, .. } = &mut func.body.blocks[0].terminator else { unreachable!() };
        args[0] = Operand::Copy(Place::local(3));
        *dest = Place::local(11);
        let context = crate::VcgenContext::for_function(func.def_path.clone())
            .with_elem_sizes(table(&payload, &[Some(8)]), &func);
        crate::with_vcgen_context(&context, || {
            let mut engine = SepEngine::new(&func.def_path)
                .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect()).with_elem_sizes(&func);
            for stmt in &func.body.blocks[0].stmts[..5] { engine.interpret_statement(stmt, &SourceSpan::default()); }
            let name = engine.local_to_ptr.get(&9).unwrap().clone();
            let original = engine.heap.pointer(&name).unwrap().provenance;
            assert_eq!(engine.local_alloc_size(9), Some(Formula::Int(8)), "root points to the pointer slot");
            engine.interpret_statement(&func.body.blocks[0].stmts[5], &SourceSpan::default());
            assert_eq!(engine.local_to_ptr.get(&9), Some(&name));
            assert_eq!(engine.heap.pointer(&name).unwrap().provenance, original,
                "restoring the root map alone would still leave an overwritten heap record");
            assert_eq!(engine.local_alloc_size(10), Some(Formula::Int(8)), "saved alias still names the slot");
            if raw {
                for message in [format!("[unsafe:sep:write] write permission for *{name}"),
                    "[unsafe:sep:addr_of] &raw const on `_8` (source liveness unverified)".into()]
                {
                    assert_eq!(engine.vcs.iter().filter(|vc| matches!(&vc.kind,
                        VcKind::Assertion { message: actual } if actual == &message)).count(), 1,
                        "source and raw-destination obligations remain: {message}");
                }
            }
        });
        let rows = bounds(&func, &context);
        assert_bound_sides(&rows, Access::Read);
        assert!(matches!(solve(&rows[0]), VerificationResult::Proved { .. }),
            "reading the still-live whole pointer slot remains a positive bound control");
    }
}

#[test]
fn constant_bounds_use_the_production_folder_without_granting_ay_a_new_kind() {
    for (bytes, in_bounds) in [(8, true), (7, false)] {
        let func = access(Ty::Int { width: 64, signed: false }, bytes, Access::Read);
        let context = crate::VcgenContext::for_function(func.def_path.clone());
        let rows = bounds(&func, &context);
        assert_bound_sides(&rows, Access::Read);
        let row = &rows[0];
        let ay_only = crate::test_router::deterministic_test_router()
            .verify_all(std::slice::from_ref(row)).pop().unwrap().1;
        assert!(matches!(ay_only, VerificationResult::Unknown { ref solver, ref reason, .. }
            if solver.as_str() == "none" && reason.contains("no backend can handle this VC")),
            "AY-only dispatch remains an explicit unsupported kind: {ay_only:?}");
        let result = solve(row);
        if in_bounds {
            assert!(matches!(result, VerificationResult::Proved { ref solver, .. }
                if solver.as_str() == "constant-folder"), "{result:?}");
        } else {
            assert!(matches!(result, VerificationResult::Failed { ref solver, .. }
                if solver.as_str() == "constant-folder"), "{result:?}");
        }
        assert!(matches!(row.kind, VcKind::CopyBoundsViolation { .. }),
            "the original generated kind is never recast as an Assertion");
    }
}
