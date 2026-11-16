//! The owning byte-capacity controls use the retained genuine compiler body,
//! then change one semantic edge at a time. No rendered source name mints facts.

use trust_types::{ConstValue, Statement, Terminator, Ty};

use super::*;

fn fixture() -> VerifiableFunction {
    serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/nncast_read_cast_mir.json"
    ))
    .unwrap()
}

fn call(func: &VerifiableFunction) -> (&[Operand], BlockId) {
    func.body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Terminator::Call { is_foreign: true, args, .. } => Some((args.as_slice(), block.id)),
            _ => None,
        })
        .unwrap()
}

fn count(func: &mut VerifiableFunction, n: u128) {
    for block in &mut func.body.blocks {
        if let Terminator::Call { is_foreign: true, args, .. }
        | Terminator::TailCall { is_foreign: true, args, .. } = &mut block.terminator
            && args.len() == 3
        {
            args[2] = Operand::Constant(ConstValue::Uint(n, 64));
        }
    }
}

fn extent(func: &VerifiableFunction) -> Option<u64> {
    let (args, id) = call(func);
    call_facts(func, &Default::default()).get(&id)?.byte_extents(args).get(&1).copied()
}

fn capacity(func: VerifiableFunction) -> VerificationCondition {
    std::thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || {
        let rows: Vec<_> = super::generate_vcs(&func).into_iter().filter(|row| {
            matches!(&row.kind, VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("available byte extent"))
        }).collect();
        assert_eq!(rows.len(), 1, "the real FFI call must keep exactly one capacity obligation: {rows:?}");
        rows.into_iter().next().unwrap()
    }).unwrap().join().unwrap()
}

fn folded(row: VerificationCondition) -> Formula {
    crate::simplify::SimplificationPipeline::default_pipeline().run(row.formula).0
}

#[test]
fn ffi_buffer_extent_real_array_len_and_literal_counts_have_actual_capacity_rows() {
    let func = fixture();
    assert_eq!(extent(&func), Some(64));
    assert_eq!(
        folded(capacity(func)),
        Formula::Bool(false),
        "buf.len() must fit its actual buffer"
    );
    for n in [0, 1, 63, 64, 65, 4096] {
        let mut func = fixture();
        count(&mut func, n);
        assert_eq!(folded(capacity(func)), Formula::Bool(n > 64), "literal count {n}");
    }
    let mut empty = fixture();
    for decl in &mut empty.body.locals {
        let ty = match &mut decl.ty {
            Ty::Ref { inner, .. } => inner.as_mut(),
            other => other,
        };
        if let Ty::Array { len, .. } = ty {
            *len = 0;
        }
    }
    for block in &mut empty.body.blocks {
        for stmt in &mut block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Repeat(_, n), .. } = stmt {
                *n = 0;
            }
        }
    }
    assert_eq!(extent(&empty), Some(0));
    assert_eq!(folded(capacity(empty.clone())), Formula::Bool(false));
    count(&mut empty, 1);
    assert_eq!(folded(capacity(empty)), Formula::Bool(true));
}

#[test]
fn ffi_buffer_extent_casts_preserve_bytes_instead_of_rescaling_by_pointee() {
    let mut func = fixture();
    // A raw u32 pointee cast cannot turn a 64-byte allocation into 256 bytes.
    if let Ty::RawPtr { pointee, .. } =
        &mut func.body.locals.iter_mut().find(|d| d.index == 3).unwrap().ty
    {
        *pointee = Box::new(Ty::u32());
    }
    assert_eq!(extent(&func), Some(64));
    count(&mut func, 65);
    assert_eq!(folded(capacity(func)), Formula::Bool(true));

    let mut words = fixture();
    // The original 64-element buffer now really contains u16s: 128 bytes.
    for decl in &mut words.body.locals {
        fn widen(ty: &mut Ty) {
            match ty {
                Ty::Int { width: 8, signed: false } => *ty = Ty::Int { width: 16, signed: false },
                Ty::Array { elem, .. } | Ty::Slice { elem } => widen(elem),
                Ty::Ref { inner, .. } => widen(inner),
                Ty::RawPtr { pointee, .. } => widen(pointee),
                _ => {}
            }
        }
        widen(&mut decl.ty);
    }
    for block in &mut words.body.blocks {
        for stmt in &mut block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                match rvalue {
                    Rvalue::Repeat(Operand::Constant(ConstValue::Uint(_, width)), _) => *width = 16,
                    Rvalue::Cast(_, Ty::Ref { inner, .. }) => {
                        if let Ty::Slice { elem } = inner.as_mut() {
                            *elem = Box::new(Ty::Int { width: 16, signed: false });
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    assert_eq!(extent(&words), Some(128));
    for n in [128, 129] {
        count(&mut words, n);
        assert_eq!(folded(capacity(words.clone())), Formula::Bool(n > 128));
    }
}

#[test]
fn ffi_buffer_extent_unknown_raw_pointer_and_zero_count_are_distinct() {
    let mut func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/nncast_cast_of_param_mir.json"
    ))
    .unwrap();
    assert_eq!(extent(&func), None, "a declared raw pointee size is no allocation evidence");
    count(&mut func, 1);
    assert_eq!(folded(capacity(func.clone())), Formula::Bool(true));
    count(&mut func, 0);
    assert_eq!(folded(capacity(func)), Formula::Bool(false));
}

#[test]
fn ffi_buffer_extent_storage_death_and_alias_stores_retire_provenance() {
    for marker in [
        Statement::StorageDead(2),
        Statement::Deinit { place: Place::local(2) },
        Statement::Assign {
            place: Place { local: 3, projections: vec![trust_types::Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 8))),
            span: SourceSpan::default(),
        },
    ] {
        let mut func = fixture();
        func.body.blocks[2].stmts.insert(0, marker);
        assert_eq!(extent(&func), None);
        count(&mut func, 1);
        assert_eq!(folded(capacity(func)), Formula::Bool(true));
    }
}

#[test]
fn ffi_buffer_extent_reassignment_and_pointer_metadata_escape_refuse() {
    for mutate in [false, true] {
        let mut func = fixture();
        let stmt = if mutate {
            let ty = Ty::Ref {
                mutable: true,
                inner: Box::new(func.body.locals.iter().find(|d| d.index == 3).unwrap().ty.clone()),
            };
            func.body.locals.push(trust_types::LocalDecl { index: 10, ty, name: None });
            Statement::Assign {
                place: Place::local(10),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
                span: SourceSpan::default(),
            }
        } else {
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                span: SourceSpan::default(),
            }
        };
        func.body.blocks[2].stmts.insert(0, stmt);
        assert_eq!(extent(&func), None);
        count(&mut func, 1);
        assert_eq!(folded(capacity(func)), Formula::Bool(true));
    }
}

#[test]
fn ffi_buffer_extent_integer_truncation_and_forged_accessor_keys_refuse() {
    let mut truncated = fixture();
    // An integer hop (including a truncated address) cannot carry provenance.
    truncated.body.locals.iter_mut().find(|d| d.index == 4).unwrap().ty = Ty::u8();
    assert_eq!(extent(&truncated), None);
    for forged in [None, Some(trust_types::SysrootItem::VecAsMutPtr)] {
        let mut func = fixture();
        if let Terminator::Call { callee_key, .. } = &mut func.body.blocks[0].terminator {
            callee_key.as_mut().unwrap().sysroot_item = forged;
        }
        assert_eq!(extent(&func), None, "rendered core::slice name cannot mint extent");
    }
    let mut fake_sysroot = fixture();
    if let Terminator::Call { callee_key, .. } = &mut fake_sysroot.body.blocks[0].terminator {
        callee_key.as_mut().unwrap().krate_is_real_sysroot = false;
    }
    assert_eq!(extent(&fake_sysroot), None);
}

#[test]
fn ffi_buffer_extent_unknown_reallocator_invalidates_existing_aliases() {
    let mut func = fixture();
    let mut realloc = func.body.blocks[1].clone();
    realloc.id = BlockId(4);
    let raw_ty = func.body.locals.iter().find(|d| d.index == 3).unwrap().ty.clone();
    func.body.locals.push(trust_types::LocalDecl { index: 10, ty: raw_ty, name: None });
    if let Terminator::Call { target, .. } = &mut func.body.blocks[1].terminator {
        *target = Some(BlockId(4));
    }
    if let Terminator::Call { func, args, callee_key, is_foreign, dest, target, .. } =
        &mut realloc.terminator
    {
        *func = "libc::realloc".into();
        *args = vec![Operand::Copy(Place::local(3)), Operand::Constant(ConstValue::Uint(128, 64))];
        *callee_key = None;
        *is_foreign = true;
        *dest = Place::local(10);
        *target = Some(BlockId(2));
    }
    func.body.blocks.push(realloc);
    assert_eq!(extent(&func), None);
    count(&mut func, 1);
    // There are now two FFI calls, but only read has a buffer-count contract.
    assert_eq!(folded(capacity(func)), Formula::Bool(true));
}

#[test]
fn ffi_buffer_extent_cfg_join_requires_evidence_on_every_predecessor() {
    let mut func = fixture();
    let mut alternate = func.body.blocks[3].clone();
    alternate.id = BlockId(4);
    alternate.terminator = Terminator::Goto(BlockId(2));
    if let Terminator::Call { target, .. } = &mut func.body.blocks[1].terminator {
        *target = Some(BlockId(5));
    }
    let mut branch = func.body.blocks[3].clone();
    branch.id = BlockId(5);
    branch.terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(1)),
        targets: vec![(0, BlockId(2))],
        otherwise: BlockId(4),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    func.body.blocks.extend([alternate, branch]);
    assert_eq!(extent(&func), Some(64), "both branches preserve the same live extent");
    func.body
        .blocks
        .iter_mut()
        .find(|b| b.id == BlockId(4))
        .unwrap()
        .stmts
        .push(Statement::StorageDead(2));
    assert_eq!(extent(&func), None, "one invalid predecessor must retire the joined license");
}

#[test]
fn ffi_buffer_extent_unmodeled_layout_never_uses_an_element_count_as_bytes() {
    assert_eq!(byte_size(&Ty::Int { width: 7, signed: false }), None);
    assert_eq!(byte_size(&Ty::Array { elem: Box::new(Ty::u64()), len: u64::MAX }), None);
    let mut func = fixture();
    if let Ty::Array { elem, .. } =
        &mut func.body.locals.iter_mut().find(|d| d.index == 2).unwrap().ty
    {
        *elem = Box::new(Ty::Int { width: 7, signed: false });
    }
    assert_eq!(extent(&func), None);
    assert_eq!(call_facts(&func, &Default::default()).len(), func.body.blocks.len());
}

#[test]
fn ffi_buffer_extent_safety_declaration_cannot_discharge_an_actual_overrun() {
    let mut func = fixture();
    count(&mut func, 4096);
    let mut declared = crate::unsafe_verify::safety_declared::SafetyDeclaredUnsafeOps::default();
    declared.declare_terminator(call(&func).1);
    let (rows, _) = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            crate::unsafe_verify::safety_declared::with_safety_declared_unsafe_ops(
                &func,
                declared,
                || super::generate_vcs(&func),
            )
        })
        .unwrap()
        .join()
        .unwrap();
    let row = rows
        .into_iter()
        .find(|row| {
            matches!(&row.kind,
        VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("available byte extent"))
        })
        .unwrap();
    assert_eq!(folded(row), Formula::Bool(true));
}

#[test]
fn ffi_buffer_extent_real_reference_parameter_has_one_byte_without_raw_type_inference() {
    let mut func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/nncast_ref_param_mir.json"
    ))
    .unwrap();
    assert_eq!(extent(&func), Some(1));
    assert_eq!(folded(capacity(func.clone())), Formula::Bool(false));
    count(&mut func, 2);
    assert_eq!(folded(capacity(func)), Formula::Bool(true));
}

#[test]
fn ffi_buffer_extent_real_vec_accessor_does_not_invent_allocation_liveness() {
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/asptr_std_vec_mir.json"
    ))
    .unwrap();
    let facts = call_facts(&func, &Default::default());
    let (args, id) = call(&func);
    assert!(facts.get(&id).unwrap().byte_extents(args).is_empty());
}

// FFI-CALL-DEST-STORAGE-1 (2026-11-01): a call's whole-local destination of an exactly
// sized type is initialized storage on the return edge. Real MIR dumped by the stage 1 of
// 87c5b81eef from `tests/fixtures/ffi_buffer_extent_call_dest/sigbyte.rs.txt`: the
// agy-alab / claude-code-alab self-pipe handler shape `let byte =
// u8::try_from(sig).unwrap_or(0); write(fd, (&raw const byte).cast(), 1)`.

fn call_dest_fixture(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/ffi_buffer_extent_call_dest/{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
}

#[test]
fn a_sized_call_result_written_whole_has_its_byte_extent() {
    let byte = call_dest_fixture("sig_byte");
    assert_eq!(extent(&byte), Some(1));
    assert_eq!(folded(capacity(byte)), Formula::Bool(false), "one byte fits one byte");
    let word = call_dest_fixture("sig_word");
    assert_eq!(extent(&word), Some(4));
    assert_eq!(folded(capacity(word)), Formula::Bool(false), "four bytes fit four bytes");
}

#[test]
fn a_call_result_keeps_its_capacity_row_past_its_size_or_without_one() {
    // Negative: two bytes from a one-byte result. The extent is known, so the row is
    // the literal violation.
    let two = call_dest_fixture("sig_byte_two");
    assert_eq!(extent(&two), Some(1));
    assert_eq!(folded(capacity(two)), Formula::Bool(true), "two bytes do not fit one");
    // Negative: a tuple result, which `byte_size` does not size, gets no extent.
    let pair = call_dest_fixture("sig_pair");
    assert_eq!(extent(&pair), None);
    assert_ne!(folded(capacity(pair)), Formula::Bool(false), "an unsized result proves nothing");
}

#[test]
fn a_call_result_exists_only_on_the_return_edge_and_only_for_its_own_call() {
    // The same body with the result's call made to diverge (no return edge): the byte is
    // never initialized, so the write has no extent.
    let mut diverging = call_dest_fixture("sig_byte");
    let byte_local = 3;
    for block in &mut diverging.body.blocks {
        if let Terminator::Call { dest, target, .. } = &mut block.terminator
            && dest.local == byte_local
        {
            *target = None;
        }
    }
    let id = diverging
        .body
        .blocks
        .iter()
        .find(|b| matches!(&b.terminator, Terminator::Call { is_foreign: true, .. }))
        .unwrap()
        .id;
    assert!(
        call_facts(&diverging, &Default::default())
            .get(&id)
            .is_none_or(|f| f.byte_extents(call(&diverging).0).is_empty())
    );
    // A projected destination (a field of a larger local) is not the whole local and
    // seeds nothing.
    let mut projected = call_dest_fixture("sig_byte");
    for block in &mut projected.body.blocks {
        if let Terminator::Call { dest, .. } = &mut block.terminator
            && dest.local == byte_local
        {
            dest.projections.push(trust_types::Projection::Field(0));
        }
    }
    assert_eq!(extent(&projected), None);
    // Only the call's own destination is seeded: redirect the result into another local
    // and the borrowed `byte` is never written, so it has no extent.
    let mut killed = call_dest_fixture("sig_byte");
    let unwrap_block = killed
        .body
        .blocks
        .iter()
        .position(
            |b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == byte_local),
        )
        .unwrap();
    if let Terminator::Call { dest, .. } = &mut killed.body.blocks[unwrap_block].terminator {
        dest.local = 1; // the `fd` parameter's slot: `byte` is now never written
    }
    assert_eq!(extent(&killed), None, "an unwritten local has no extent");
}

// REVIEW-A4C4-MINORS-1 fix-forward (2026-11-07): a `become` ends the frame before the
// callee runs. The generation entry hands this lane the tail-call PROJECTION
// (`VerifiableFunction::with_tail_calls_expanded`), where `become write(..)` is an
// ordinary `_0 = write(..) -> bbN; bbN: return`, the shape of these real bodies' own
// last call. So each real body below, with that call made a tail call, is exactly what
// a `become` of the same call extracts to.

/// `func` with its foreign call (whose destination is the return slot) turned into the
/// `TailCall` a `become` of it is.
fn as_tail_call(mut func: VerifiableFunction) -> VerifiableFunction {
    let mut turned = 0;
    for block in &mut func.body.blocks {
        if let Terminator::Call {
            func: callee,
            args,
            dest,
            span,
            atomic,
            is_foreign: true,
            is_unsafe_sig,
            callee_identity,
            callee_key,
            ..
        } = &block.terminator
            && dest.local == 0
            && dest.projections.is_empty()
        {
            block.terminator = Terminator::TailCall {
                func: callee.clone(),
                args: args.clone(),
                span: span.clone(),
                atomic: atomic.clone(),
                is_foreign: true,
                is_unsafe_sig: *is_unsafe_sig,
                callee_identity: callee_identity.clone(),
                callee_key: callee_key.clone(),
            };
            turned += 1;
        }
    }
    assert_eq!(turned, 1, "the fixture has one foreign call into the return slot");
    func
}

/// The byte extent of the foreign call's buffer argument in the tail-call PROJECTION of
/// `source`, judged with the source's tail-call blocks (`ends_frame`, the generation
/// entry) or without them (the projection read as an ordinary call).
fn projected_extent(source: &VerifiableFunction, ends_frame: bool) -> Option<u64> {
    let projected = source.with_tail_calls_expanded();
    assert!(
        projected.body.blocks.iter().all(|b| !matches!(b.terminator, Terminator::TailCall { .. })),
        "the projection rewrites every tail call"
    );
    let blocks =
        if ends_frame { crate::sep_engine::tail_call_blocks(source) } else { Default::default() };
    let (args, id) = call(&projected);
    call_facts(&projected, &blocks).get(&id)?.byte_extents(args).get(&1).copied()
}

/// The extent at the source model's own `TailCall`, judged with no block set: the
/// terminator itself ends the frame.
fn source_tail_call_extent(source: &VerifiableFunction) -> Option<u64> {
    let (args, id) = source
        .body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator {
            Terminator::TailCall { is_foreign: true, args, .. } => {
                Some((args.as_slice(), block.id))
            }
            _ => None,
        })
        .unwrap();
    call_facts(source, &Default::default()).get(&id)?.byte_extents(args).get(&1).copied()
}

/// `nncast_ref_param_mir.json` (`write(fd, (&raw const *b) as *const c_void, 1)`, `b:
/// &u8`) with the pointer taken of the `fd` PARAMETER instead, and a count of 4:
/// `write(fd, (&raw const fd) as *const c_void, 4)`. The parameter's own storage is
/// seeded (4 bytes), so the ordinary call discharges.
fn parameter_storage_fixture() -> VerifiableFunction {
    let mut func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/nncast_ref_param_mir.json"
    ))
    .unwrap();
    let fd = 1;
    func.body.locals.iter_mut().find(|d| d.index == 4).unwrap().ty =
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) };
    let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else {
        panic!("the fixture's first statement is the `&raw const`")
    };
    *rvalue = Rvalue::AddressOf(false, Place::local(fd));
    count(&mut func, 4);
    func
}

#[test]
fn a_tail_call_keeps_no_extent_of_the_frame_it_ends() {
    for (shape, ordinary, bytes) in [
        // `let buf = [0u8; 64]; become read(fd, buf.as_mut_ptr().cast(), buf.len())`.
        ("a local array", fixture(), 64),
        // `become write(fd, (&raw const fd) as *const c_void, 4)`.
        ("a parameter", parameter_storage_fixture(), 4),
    ] {
        // Control: the ordinary call runs with this frame live, and discharges.
        assert_eq!(extent(&ordinary), Some(bytes), "{shape}: the ordinary call's extent");
        assert_eq!(
            folded(capacity(ordinary.clone())),
            Formula::Bool(false),
            "{shape}: the ordinary call fits its buffer"
        );
        let source = as_tail_call(ordinary);
        assert_eq!(
            projected_extent(&source, true),
            None,
            "{shape}: the frame has ended when the tail-called callee reads the buffer"
        );
        // Positive control: the projection read without the source's tail-call blocks is
        // the in-frame call, so this test can see the difference it pins.
        assert_eq!(projected_extent(&source, false), Some(bytes), "{shape}: positive control");
        assert_eq!(source_tail_call_extent(&source), None, "{shape}: the source `TailCall`");
        assert_ne!(
            folded(capacity(source)),
            Formula::Bool(false),
            "{shape}: through the generation entry, a `become` of the call keeps its row"
        );
    }
}

/// What survives the frame: the pointee of a reference PARAMETER, which the caller holds
/// borrowed until its own call returns. `become write(fd, (&raw const *b) as *const
/// c_void, 1)` (`b: &u8`) keeps its one byte and still discharges.
#[test]
fn a_tail_call_keeps_the_extent_of_a_reference_parameters_pointee() {
    let ordinary: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/nncast_ref_param_mir.json"
    ))
    .unwrap();
    let source = as_tail_call(ordinary);
    assert_eq!(projected_extent(&source, true), Some(1));
    assert_eq!(source_tail_call_extent(&source), Some(1));
    assert_eq!(folded(capacity(source.clone())), Formula::Bool(false));
    let mut over = source;
    count(&mut over, 2);
    assert_eq!(folded(capacity(over)), Formula::Bool(true), "two bytes still do not fit one");
}
