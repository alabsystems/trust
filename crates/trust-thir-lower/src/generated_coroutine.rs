//! Generated **built-MIR** bodies, not THIR and not the coroutine state protocol.
//!
//! The by-move query feeds `mir_built` directly, bypassing the ordinary producer
//! callback. This entry consumes its actual remapped body before that feed. The
//! bounded model below is an inspection artifact only: no source refinement,
//! state-transform certificate, differential agreement, flip or executable
//! module query is minted. Unsupported input contributes a typed refusal and
//! no fabricated function. The independent census does not consult this state.

use std::collections::BTreeMap;

use rustc_hir::def::DefKind;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::LocalDefId;
use trust_ir::{
    Constant, FieldDef, Module, Pred, PredId, StructDef, StructId, StructRepr, Ty, TyId,
};

mod model;
use model::{Operand, Refusal, ScalarBlock, ScalarBody, Statement, Terminator};

/// An immutable inspection-only result. Even a modelled built body has no
/// authority over the subsequently generated coroutine state machine.
#[derive(Clone)]
pub struct GeneratedBodyOutcome {
    original: u32,
    synthetic: u32,
    snapshot: Option<ScalarBody>,
    module: Option<Module>,
    refusal: Option<Refusal>,
}

impl GeneratedBodyOutcome {
    pub fn module_for_inspection(&self) -> Option<&Module> {
        self.module.as_ref()
    }
    pub fn refusal_detail(&self) -> Option<&str> {
        self.refusal.as_ref().map(|r| r.detail.as_str())
    }
    pub fn source_definition_indices(&self) -> (u32, u32) {
        (self.original, self.synthetic)
    }
    pub fn has_exact_scalar_snapshot(&self) -> bool {
        self.snapshot.is_some()
    }
    /// Deliberately no conversion to an executable or faithful-body capability.
    pub fn is_executable(&self) -> bool {
        false
    }
}

#[derive(Default)]
struct GeneratedBodies {
    outcomes: BTreeMap<u32, GeneratedBodyOutcome>,
}

/// Query consumers can inspect the retained result without re-querying HIR or
/// borrowing already-stolen MIR. This does not expose an executable capability.
pub fn retained_outcome(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<GeneratedBodyOutcome> {
    tcx.sess.with_trust_compiler_state::<GeneratedBodies, _>(|state| {
        state.outcomes.get(&def.local_def_index.as_u32()).cloned()
    })
}

fn scalar_type(ty: ty::Ty<'_>) -> Option<Ty> {
    Some(match ty.kind() {
        ty::Bool => Ty::Bool,
        ty::Int(ty::IntTy::I8) => Ty::I8,
        ty::Int(ty::IntTy::I16) => Ty::I16,
        ty::Int(ty::IntTy::I32) => Ty::I32,
        ty::Int(ty::IntTy::I64) => Ty::I64,
        ty::Int(ty::IntTy::Isize) => Ty::Isize,
        ty::Uint(ty::UintTy::U8) => Ty::U8,
        ty::Uint(ty::UintTy::U16) => Ty::U16,
        ty::Uint(ty::UintTy::U32) => Ty::U32,
        ty::Uint(ty::UintTy::U64) => Ty::U64,
        ty::Uint(ty::UintTy::Usize) => Ty::Usize,
        ty::Tuple(fields) if fields.is_empty() => Ty::Unit,
        _ => return None,
    })
}

fn path(tcx: TyCtxt<'_>, def: LocalDefId) -> String {
    rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def))
}

fn resume_pointer_range(repr: rustc_abi::BackendRepr) -> Option<(u128, u128)> {
    match repr {
        rustc_abi::BackendRepr::Scalar(rustc_abi::Scalar::Initialized {
            value: rustc_abi::Primitive::Pointer(space),
            valid_range,
        }) if space == rustc_abi::AddressSpace::ZERO => Some((valid_range.start, valid_range.end)),
        _ => None,
    }
}

/// Preserve the actual, unused async resume-context carrier. This is not a
/// `Unit`/opaque substitution: pointer fields remain real pointer values, and
/// every wrapper field, byte offset, size and alignment is retained. No body
/// operation may read, move, dereference, return or overwrite this argument.
fn resume_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    rust_ty: ty::Ty<'tcx>,
    structs: &mut Vec<StructDef>,
    types: &mut Vec<Ty>,
    predicates: &mut Vec<Pred>,
    depth: usize,
) -> Result<Ty, Refusal> {
    let error = || {
        Refusal::new(
            "resume argument",
            "GeneratedCoroutine(resume type)",
            format!("unsupported exact resume-context type {rust_ty:?}"),
        )
    };
    if depth > 4
        || rust_ty.references_error()
        || rust_ty.has_non_region_param()
        || rust_ty.has_non_region_infer()
    {
        return Err(error());
    }
    if depth == 0 && rust_ty.is_unit() {
        return Ok(Ty::Unit);
    }
    let layout = tcx.layout_of(typing_env.as_query_input(rust_ty)).map_err(|_| error())?;
    let pointer = match *rust_ty.kind() {
        ty::RawPtr(..) => Some((rust_ty, false)),
        ty::Pat(base, pattern)
            if matches!(*pattern, ty::PatternKind::NotNull)
                && matches!(base.kind(), ty::RawPtr(..)) =>
        {
            Some((base, true))
        }
        _ => None,
    };
    if let Some((base, nonnull)) = pointer {
        let base_layout = tcx.layout_of(typing_env.as_query_input(base)).map_err(|_| error())?;
        if depth == 0
            || !model::exact_resume_pointer_layout(
                tcx.data_layout.pointer_size().bytes(),
                (base_layout.size.bytes(), base_layout.align.bytes()),
                (layout.size.bytes(), layout.align.bytes()),
                resume_pointer_range(base_layout.backend_repr).ok_or_else(error)?,
                resume_pointer_range(layout.backend_repr).ok_or_else(error)?,
                nonnull,
            )
        {
            return Err(error());
        }
        if !nonnull {
            return Ok(Ty::Ptr);
        }
        // Preserve the actual pattern restriction, not merely its storage
        // shape. This sealed snapshot owns one canonical Ptr/NonNull row.
        if !types.is_empty() || !predicates.is_empty() {
            return Err(error());
        }
        let mut table = Module::new("generated-resume-type");
        let base = table.add_type(Ty::Ptr).map_err(|_| error())?;
        let predicate = table.intern_pred(Pred::NonNull).map_err(|_| error())?.ok_or_else(error)?;
        if base != TyId::new(0) || predicate != PredId::new(0) {
            return Err(error());
        }
        *types = table.types;
        *predicates = table.predicates;
        return Ok(Ty::Refine(base, predicate));
    }
    let ty::Adt(definition, args) = rust_ty.kind() else {
        return Err(error());
    };
    if depth == 0 && tcx.lang_items().resume_ty() != Some(definition.did()) {
        return Err(error());
    }
    if !definition.is_struct()
        || definition.non_enum_variant().fields.len() != 1
        || definition.has_dtor(tcx)
        || definition.repr().packed()
        || definition.repr().c()
        || definition.repr().simd()
    {
        return Err(error());
    }
    let field = definition.non_enum_variant().fields.iter().next().ok_or_else(error)?;
    let rust_field_ty =
        tcx.try_normalize_erasing_regions(typing_env, field.ty(tcx, *args)).map_err(|_| error())?;
    // Layout is checked independently from the IR spelling. The bounded
    // wrapper must preserve its one child's exact pointer representation.
    let field_layout =
        tcx.layout_of(typing_env.as_query_input(rust_field_ty)).map_err(|_| error())?;
    if layout.fields.count() != 1
        || layout.fields.offset(0).bytes() != 0
        || layout.size.bytes() != 8
        || layout.align.bytes() != 8
        || layout.size != field_layout.size
        || layout.align != field_layout.align
    {
        return Err(error());
    }
    let field_ty =
        resume_type(tcx, typing_env, rust_field_ty, structs, types, predicates, depth + 1)?;
    let id = StructId::new(u32::try_from(structs.len()).map_err(|_| error())?);
    structs.push(StructDef {
        id,
        name: rustc_middle::ty::print::with_no_trimmed_paths!(format!("{rust_ty:?}")),
        fields: vec![FieldDef {
            name: field.name.to_string(),
            ty: field_ty,
            offset: Some(layout.fields.offset(0).bytes()),
        }],
        size: Some(layout.size.bytes()),
        align: Some(layout.align.bytes()),
        repr: if definition.repr().transparent() {
            StructRepr::Transparent
        } else {
            StructRepr::Rust
        },
        origin: None,
    });
    Ok(Ty::Struct(id))
}

fn snapshot<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: LocalDefId,
    synthetic: LocalDefId,
    body: &mir::Body<'tcx>,
) -> Result<ScalarBody, Refusal> {
    let error = |reason, detail| Refusal::new("body", reason, detail);
    if tcx.def_kind(synthetic) != DefKind::SyntheticCoroutineBody
        || synthetic == original
        || tcx.local_parent(synthetic) != tcx.local_parent(original)
        || body.source.def_id() != synthetic.to_def_id()
        || body.source.promoted.is_some()
        || body.phase != mir::MirPhase::Built
        || body.tainted_by_errors.is_some()
        || body.arg_count != 2
        || body.spread_arg.is_some()
        || body.local_decls.len() < 3
        || body.local_decls.len() > 4096
        || body.basic_blocks.len() > 128
        || body.required_consts.as_ref().is_some_and(|constants| !constants.is_empty())
    {
        return Err(error(
            "GeneratedCoroutine(header)",
            "not an exact, untainted bounded by-move built body",
        ));
    }
    let rust_frame = body.local_decls[mir::Local::from_usize(1)].ty;
    if tcx.type_of(synthetic).instantiate_identity().skip_norm_wip() != rust_frame {
        return Err(error(
            "GeneratedCoroutine(frame identity)",
            "fed synthetic type differs from actual self argument",
        ));
    }
    let ty::Coroutine(frame_owner, args) = rust_frame.kind() else {
        return Err(error(
            "GeneratedCoroutine(frame type)",
            "self is not a coroutine capture carrier",
        ));
    };
    if *frame_owner != original.to_def_id()
        || rust_frame.references_error()
        || rust_frame.has_non_region_infer()
    {
        return Err(error(
            "GeneratedCoroutine(frame identity)",
            "capture carrier is not the original coroutine's fully resolved type",
        ));
    }
    let args = args.as_coroutine();
    let Some(coroutine) = body.coroutine.as_deref() else {
        return Err(error(
            "GeneratedCoroutine(coroutine signature)",
            "missing built coroutine metadata",
        ));
    };
    if args.kind_ty().to_opt_closure_kind() != Some(ty::ClosureKind::FnOnce)
        || args.return_ty() != body.return_ty()
        || body.resume_ty() != Some(args.resume_ty())
        || body.yield_ty() != Some(args.yield_ty())
        || body.resume_ty() != Some(body.local_decls[mir::Local::from_usize(2)].ty)
        || coroutine.coroutine_layout.is_some()
        || coroutine.coroutine_drop.is_some()
        || coroutine.coroutine_drop_async.is_some()
        || coroutine.coroutine_drop_proxy_async.is_some()
    {
        return Err(error(
            "GeneratedCoroutine(coroutine signature)",
            "by-move kind, exact resume/yield/return types or pre-state-transform phase differ",
        ));
    }
    // Do not use `upvar_tys`: it silently turns an error type into an empty
    // capture list and panics on an unresolved or otherwise non-tuple type.
    let tupled_upvars = args.tupled_upvars_ty();
    let ty::Tuple(captures) = tupled_upvars.kind() else {
        return Err(error(
            "GeneratedCoroutine(frame type)",
            "capture types are not an actual resolved tuple",
        ));
    };
    if captures.len() > 64 {
        return Err(error("GeneratedCoroutine(frame)", "capture count exceeds bounded slice"));
    }
    let fields = captures
        .iter()
        .enumerate()
        .map(|(i, rust_ty)| {
            let ty = scalar_type(rust_ty).ok_or_else(|| {
                Refusal::new(
                    format!("capture {i}"),
                    "GeneratedCoroutine(capture type)",
                    format!("requires a scalar by-value capture, got {rust_ty:?}"),
                )
            })?;
            Ok(FieldDef { name: format!("__upvar{i}"), ty, offset: None })
        })
        .collect::<Result<Vec<_>, Refusal>>()?;
    let mut structs = vec![StructDef {
        id: StructId::new(0),
        name: format!("generated-built-frame::{}", path(tcx, synthetic)),
        fields,
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    }];
    let rust_resume = body.local_decls[mir::Local::from_usize(2)].ty;
    let mut types = Vec::new();
    let mut predicates = Vec::new();
    let resume = resume_type(
        tcx,
        body.typing_env(tcx),
        rust_resume,
        &mut structs,
        &mut types,
        &mut predicates,
        0,
    )?;
    let locals = body
        .local_decls
        .iter_enumerated()
        .map(|(local, declaration)| match local.as_usize() {
            1 => Ok(Ty::Struct(StructId::new(0))),
            2 => Ok(resume.clone()),
            _ => scalar_type(declaration.ty).ok_or_else(|| {
                Refusal::new(
                    format!("local {local:?}"),
                    "GeneratedCoroutine(local type)",
                    format!("unsupported actual local type {:?}", declaration.ty),
                )
            }),
        })
        .collect::<Result<Vec<_>, Refusal>>()?;
    let mut blocks = Vec::new();
    let mut statement_count = 0usize;
    for (block_id, block) in body.basic_blocks.iter_enumerated() {
        if block.is_cleanup {
            return Err(error(
                "GeneratedCoroutine(cleanup)",
                "cleanup/unwind semantics are not in the scalar slice",
            ));
        }
        let mut statements = Vec::new();
        for (index, statement) in block.statements.iter().enumerate() {
            statement_count += 1;
            if statement_count > 4096 {
                return Err(error("GeneratedCoroutine(size)", "statement budget exceeded"));
            }
            let site = format!("{block_id:?}[{index}]");
            let converted = match &statement.kind {
                mir::StatementKind::Assign(assignment) => {
                    let (place, rvalue) = &**assignment;
                    let Some(destination) = place.as_local() else {
                        return Err(Refusal::new(
                            site,
                            "GeneratedCoroutine(store)",
                            format!("projected store {place:?}"),
                        ));
                    };
                    let mir::Rvalue::Use(operand, with_retag) = rvalue else {
                        return Err(Refusal::new(
                            site,
                            "GeneratedCoroutine(rvalue)",
                            format!("unmodeled actual rvalue {rvalue:?}"),
                        ));
                    };
                    let operand = operand_snapshot(operand, &site)?;
                    let source_ty = match &operand {
                        Operand::Local { local, .. } => locals.get(*local),
                        Operand::Capture { ty, .. } | Operand::Constant { ty, .. } => Some(ty),
                    };
                    if !use_retag_is_inert(
                        *with_retag,
                        locals.get(destination.as_usize()),
                        source_ty,
                    ) {
                        return Err(Refusal::new(
                            site,
                            "GeneratedCoroutine(retag)",
                            "operand use may retag a non-scalar or differently typed value",
                        ));
                    }
                    Statement::Assign { destination: destination.as_usize(), operand }
                }
                mir::StatementKind::StorageLive(local) => Statement::StorageLive(local.as_usize()),
                mir::StatementKind::StorageDead(local) => Statement::StorageDead(local.as_usize()),
                // These are compiler-only metadata, not loads, stores, retags,
                // assertions, coverage probes, calls or drop operations.
                mir::StatementKind::Nop
                | mir::StatementKind::FakeRead(..)
                | mir::StatementKind::AscribeUserType(..)
                | mir::StatementKind::PlaceMention(..) => Statement::Nop,
                other => {
                    return Err(Refusal::new(
                        site,
                        "GeneratedCoroutine(statement)",
                        format!("unmodeled actual statement {other:?}"),
                    ));
                }
            };
            statements.push(converted);
        }
        let Some(terminator) = &block.terminator else {
            return Err(error("GeneratedCoroutine(terminator)", "missing actual terminator"));
        };
        let terminator = match terminator.kind {
            mir::TerminatorKind::Goto { target, .. } => Terminator::Goto(target.as_usize()),
            mir::TerminatorKind::Return => Terminator::Return,
            ref other => {
                return Err(Refusal::new(
                    format!("{block_id:?} terminator"),
                    "GeneratedCoroutine(terminator)",
                    format!(
                        "unmodeled actual terminator {other:?}; calls, drops, unwind and suspension require real lowering"
                    ),
                ));
            }
        };
        blocks.push(ScalarBlock { statements, terminator });
    }
    Ok(ScalarBody { name: path(tcx, synthetic), structs, types, predicates, locals, blocks })
}

/// `Use(..., Yes)` selects default retagging while copying the operand. Only
/// matching pointer-free scalar carriers make that operation inert. Do not
/// silently discard this flag for a frame, resume wrapper, reference or pointer.
/// `No` performs no retag; the core still checks types, initialization and moves.
fn use_retag_is_inert(
    retag: mir::WithRetag,
    destination: Option<&Ty>,
    operand: Option<&Ty>,
) -> bool {
    match retag {
        mir::WithRetag::No => true,
        mir::WithRetag::Yes => {
            matches!((destination, operand), (Some(destination), Some(operand))
                if destination == operand && model::scalar(destination))
        }
    }
}

fn operand_snapshot(operand: &mir::Operand<'_>, site: &str) -> Result<Operand, Refusal> {
    let error = || {
        Refusal::new(
            site,
            "GeneratedCoroutine(operand)",
            format!("unmodeled exact operand {operand:?}"),
        )
    };
    match operand {
        mir::Operand::Copy(place) | mir::Operand::Move(place) => {
            let moved = matches!(operand, mir::Operand::Move(_));
            if let Some(local) = place.as_local() {
                return Ok(Operand::Local { local: local.as_usize(), moved });
            }
            if place.local.as_usize() == 1 {
                if let [mir::ProjectionElem::Field(field, ty)] = place.projection.as_slice() {
                    return Ok(Operand::Capture {
                        field: field.as_usize(),
                        ty: scalar_type(*ty).ok_or_else(error)?,
                        moved,
                    });
                }
            }
            Err(error())
        }
        mir::Operand::Constant(constant) => {
            let ty = scalar_type(constant.const_.ty()).ok_or_else(error)?;
            // Never trigger CTFE or assume a named constant evaluated. Only
            // already-materialized literal values are read from the actual MIR.
            let mir::Const::Val(value, _) = constant.const_ else {
                return Err(error());
            };
            if ty == Ty::Unit && matches!(value, mir::ConstValue::ZeroSized) {
                return Ok(Operand::Constant { ty, value: Constant::PhantomData });
            }
            let (width, signed) = match ty {
                Ty::Bool => (8, false),
                Ty::I8 => (8, true),
                Ty::I16 => (16, true),
                Ty::I32 => (32, true),
                Ty::I64 => (64, true),
                Ty::U8 => (8, false),
                Ty::U16 => (16, false),
                Ty::U32 => (32, false),
                Ty::U64 => (64, false),
                _ => return Err(error()),
            };
            let bits =
                constant.const_.try_to_bits(rustc_abi::Size::from_bits(width)).ok_or_else(error)?;
            let value = if ty == Ty::Bool {
                if bits > 1 {
                    return Err(error());
                }
                Constant::Bool(bits == 1)
            } else if signed {
                Constant::Int(((bits << (128 - width)) as i128) >> (128 - width))
            } else {
                Constant::Int(bits as i128)
            };
            Ok(Operand::Constant { ty, value })
        }
        _ => Err(error()),
    }
}

/// Called only with the actual owned body after `MakeByMoveBody` and type feeds,
/// before feeding/storing `mir_built`. No parent lowering/verdict is consumed.
pub fn record_by_move_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: LocalDefId,
    def: LocalDefId,
    body: &mir::Body<'tcx>,
) {
    if !tcx.sess.trust_ir_lower_enabled() && !crate::crate_module::emit_requested(tcx) {
        return;
    }
    let reflected = snapshot(tcx, original, def, body);
    let lowered = reflected.as_ref().map_err(Clone::clone).and_then(model::lower);
    let outcome = GeneratedBodyOutcome {
        original: original.local_def_index.as_u32(),
        synthetic: def.local_def_index.as_u32(),
        snapshot: reflected.ok(),
        module: lowered.as_ref().ok().cloned(),
        refusal: lowered.err(),
    };
    // Keep the first exact result; duplicate callbacks still reach record(),
    // whose duplicate ledger makes semantic finalization fail closed.
    tcx.sess.with_trust_compiler_state::<GeneratedBodies, _>(|state| {
        state.outcomes.entry(outcome.synthetic).or_insert_with(|| outcome.clone());
    });
    let unsupported = outcome
        .refusal
        .as_ref()
        .map(|refusal| (format!("{}: {}", refusal.site, refusal.detail), refusal.reason))
        .into_iter()
        .collect::<Vec<_>>();
    let detail = outcome.refusal.as_ref().map_or_else(
        || "actual generated built-MIR scalar model; coroutine state protocol/source refinement unproved; not executable".into(),
        |refusal| format!("{}: {}; no generated function emitted", refusal.site, refusal.detail),
    );
    let lowered = crate::Lowered {
        global_origins: Vec::new(),
        module: outcome.module.unwrap_or_else(|| Module::new(path(tcx, def))),
        body_kind: crate::BodyKind::Fn,
        unsupported: unsupported.clone(),
        symbolic: false,
        unsubstituted_opaque_return: false,
        opaque_collapse: false,
        union_lane: false,
        // Nothing here withholds a layout, so R2 stays as strict as it was (empty witness).
        layout_withheld_structs: Vec::new(),
        enum_param_lane: false,
        contains_call: false,
        place_path_carrier: false,
        zst_closure_arg: false,
        coroutine_frame_ptr: false,
        fnptr_adapter: false,
        thin_reborrows: Vec::new(),
        mut_reborrows: Vec::new(),
        callees: Vec::new(),
        pending_consts: Vec::new(),
        enum_declines: Vec::new(),
        enum_fold_switch_blocks: Default::default(),
    };
    let interpreter = crate::differential::DiffReport {
        unsupported: unsupported.clone(),
        notes: vec![detail.clone()],
        ..Default::default()
    };
    let derived = crate::mir_differential::DerivedReport {
        verdict: crate::mir_differential::DerivedVerdict::DerivedUnsupported,
        detail: detail.clone(),
        markers_exact: false,
        markers_detail: String::new(),
        source_header_correspondence: None,
        norms: Vec::new(),
        tally: (0, 0, 0),
    };
    tracing::debug!(target: "rustc_mir_build::builder", ?def, symbolic = false, opaque = false,
        clean = unsupported.is_empty(), "trust-ir-lower: body class");
    for (at, what) in &unsupported {
        tracing::debug!(target: "rustc_mir_build::builder", ?def, at = at.as_str(), what,
            "trust-ir-lower: unsupported shape");
    }
    if !unsupported.is_empty() {
        tracing::debug!(target: "rustc_mir_build::builder", ?def, unsupported = unsupported.len(),
            "trust-ir-lower: unsupported THIR shapes");
        if tcx.sess.trust_ir_lower_strict() {
            tcx.dcx().span_err(
                tcx.def_span(def),
                format!("-Ztrust-ir-lower=strict: generated coroutine lowering refused: {detail}"),
            );
        }
    }
    tracing::debug!(target: "rustc_mir_build::builder", ?def, equal = false, samples = 0,
        mode = ?crate::differential::DiffMode::NotRun, note = detail.as_str(), "trust-ir-lower: differential");
    tracing::debug!(target: "rustc_mir_build::builder", ?def, verdict = ?derived.verdict,
        detail = detail.as_str(), markers_exact = false, markers = "not checked",
        "trust-ir-lower: derived-MIR differential");
    crate::crate_module::record(
        tcx,
        def,
        lowered,
        &interpreter,
        &derived,
        None,
        &unsupported,
        false,
    );
}

#[cfg(test)]
mod adapter_tests {
    use super::*;

    #[test]
    fn resume_pointer_range_rejects_fat_uninitialized_integer_and_foreign_space_carriers() {
        use rustc_abi::{AddressSpace, BackendRepr, Integer, Primitive, Scalar, WrappingRange};
        let range = WrappingRange { start: 1, end: u64::MAX as u128 };
        let pointer = Scalar::Initialized {
            value: Primitive::Pointer(AddressSpace::ZERO),
            valid_range: range,
        };
        assert_eq!(resume_pointer_range(BackendRepr::Scalar(pointer)), Some((1, u64::MAX as u128)));
        for wrong in [
            BackendRepr::ScalarPair {
                a: pointer,
                b: pointer,
                b_offset: rustc_abi::Size::from_bytes(8),
            },
            BackendRepr::Scalar(Scalar::Union { value: Primitive::Pointer(AddressSpace::ZERO) }),
            BackendRepr::Scalar(Scalar::Initialized {
                value: Primitive::Int(Integer::I64, false),
                valid_range: range,
            }),
            BackendRepr::Scalar(Scalar::Initialized {
                value: Primitive::Pointer(AddressSpace(1)),
                valid_range: range,
            }),
        ] {
            assert_eq!(resume_pointer_range(wrong), None);
        }
    }

    #[test]
    fn use_retag_requires_an_exact_pointer_free_scalar_carrier() {
        for ty in [
            Ty::Unit,
            Ty::Bool,
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::Isize,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::Usize,
        ] {
            assert!(use_retag_is_inert(mir::WithRetag::Yes, Some(&ty), Some(&ty)));
            assert!(use_retag_is_inert(mir::WithRetag::No, Some(&ty), Some(&ty)));
        }
        for ty in [Ty::Ptr, Ty::Struct(StructId::new(0)), Ty::Refine(TyId::new(0), PredId::new(0))]
        {
            assert!(!use_retag_is_inert(mir::WithRetag::Yes, Some(&ty), Some(&ty)));
        }
        assert!(!use_retag_is_inert(mir::WithRetag::Yes, Some(&Ty::U32), Some(&Ty::I32)));
        assert!(!use_retag_is_inert(mir::WithRetag::Yes, Some(&Ty::U32), Some(&Ty::U16)));
        assert!(!use_retag_is_inert(mir::WithRetag::Yes, None, Some(&Ty::U32)));
        assert!(!use_retag_is_inert(mir::WithRetag::Yes, Some(&Ty::U32), None));
        // No retag is not a carrier-admission decision. These values are still
        // rejected by snapshot/model type and operand checks independently.
        assert!(use_retag_is_inert(mir::WithRetag::No, Some(&Ty::Ptr), Some(&Ty::Ptr)));
    }
}
