//! Borrow the real pass input and output; never reconstruct a before body from
//! optimized_mir and never change the pass's decisions. Diagnostic-only.

use rustc_hir::def::DefKind;
use rustc_middle::mir::{self, Body, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::DefId;
use trust_certify::scalar_mir::capture::{
    ScalarBodyObservation, ScalarCaptureRegistry, ScalarPassObservation, ScalarSourceIdentity,
    ScalarSourceObservation,
};
use trust_certify::scalar_mir::{
    ScalarMirAbi, ScalarMirBlock, ScalarMirBody, ScalarMirOperand, ScalarMirPlace, ScalarMirRetag,
    ScalarMirRvalue, ScalarMirStatement, ScalarMirTerminator, ScalarMirUnwind,
};
use trust_certify::scalar_return::{ScalarType, ScalarValue};

/// Affine pairing object, private to this actual pass invocation. It is not
/// serializable and has no constructor from an external record or model body.
pub(super) struct PassCapture {
    item_source: bool,
    phase: MirPhase,
    pass_count: usize,
    sequence: u64,
    def_id: DefId,
}

pub(super) fn begin<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<PassCapture> {
    if std::env::var_os("TRUST_SCALAR_CAPTURE_DIR").is_none() {
        return None;
    }
    let def_id = body.source.def_id();
    // Keep only lifetime-free Item identity in the pairing token; all other
    // kinds still receive a refusal row, but never a forged concrete instance.
    let item_source =
        matches!(body.source.instance, ty::InstanceKind::Item(_)) && body.source.promoted.is_none();
    let before = observe(tcx, body);
    let sequence = tcx.sess.with_trust_compiler_state::<ScalarCaptureRegistry, _>(|state| {
        let sequence = state.next_sequence;
        state.next_sequence += 1;
        state.records.entry(def_id.index.as_u32()).or_default().push(ScalarPassObservation {
            sequence,
            def_path_hash: format!("{:?}", tcx.def_path_hash(def_id)),
            before,
            after: None,
            pair_error: None,
        });
        sequence
    });
    Some(PassCapture {
        item_source,
        phase: body.phase,
        pass_count: body.pass_count,
        sequence,
        def_id,
    })
}

impl PassCapture {
    pub(super) fn finish<'tcx>(self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
        let after = observe(tcx, body);
        let pair_error = if body.source.def_id() != self.def_id
            || body.phase != self.phase
            || body.pass_count != self.pass_count
            || !self.item_source
            || !matches!(body.source.instance, ty::InstanceKind::Item(did) if did == self.def_id)
            || body.source.promoted.is_some()
        {
            Some("same-invocation source/phase/pass identity changed or unsupported".into())
        } else {
            None
        };
        tcx.sess.with_trust_compiler_state::<ScalarCaptureRegistry, _>(|state| {
            if let Some(row) = state
                .records
                .get_mut(&self.def_id.index.as_u32())
                .and_then(|rows| rows.iter_mut().find(|row| row.sequence == self.sequence))
            {
                if row.after.is_some() {
                    row.pair_error = Some("duplicate pass completion".into());
                } else {
                    row.after = Some(after);
                    row.pair_error = pair_error;
                }
            }
        });
    }
}

fn observe<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> ScalarBodyObservation {
    let mut model = project(tcx, body);
    // This retained spelling is diagnostic identity, NOT a portable source
    // certificate. The full typed projection is what the kernel checker sees.
    let full_debug_body = if body.local_decls.len() <= 16
        && body.basic_blocks.len() <= 8
        && body.basic_blocks.iter().all(|block| block.statements.len() <= 16)
    {
        match bounded_debug(body) {
            Ok(text) => text,
            Err(reason) => {
                model = Err(reason.clone());
                format!("<refused: {reason}>")
            }
        }
    } else {
        "<refused before bounded whole-body retention>".into()
    };
    let source = source_observation(tcx, body);
    if let Err(reason) = &source {
        model = Err(reason.clone());
    }
    let identity = match bounded_debug_with_limit(
        &(
            body.source,
            tcx.def_path_hash(body.source.def_id()),
            body.phase,
            body.pass_count,
            &tcx.sess.opts.target_triple,
            tcx.sess.overflow_checks(),
        ),
        4096,
    ) {
        Ok(identity) => identity,
        Err(_) => {
            model = Err("actual source/phase identity exceeds diagnostic bound".into());
            "<refused oversized source/phase identity; DefIndex and DefPathHash retained>".into()
        }
    };
    let observed = ScalarBodyObservation {
        identity,
        full_debug_body,
        field_accounting: account_fields(body),
        source,
        model,
    };
    tcx.sess
        .with_trust_compiler_state::<ScalarCaptureRegistry, _>(|state| state.retain_body(observed))
}

fn bounded_debug(value: &impl std::fmt::Debug) -> Result<String, String> {
    bounded_debug_with_limit(value, 1024 * 1024)
}

fn bounded_debug_with_limit(value: &impl std::fmt::Debug, limit: usize) -> Result<String, String> {
    use std::fmt::Write;
    struct Bounded {
        text: String,
        limit: usize,
    }
    impl Write for Bounded {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            if text.len() > self.limit.saturating_sub(self.text.len()) {
                return Err(std::fmt::Error);
            }
            self.text.push_str(text);
            Ok(())
        }
    }
    let mut retained = Bounded { text: String::new(), limit };
    write!(&mut retained, "{value:#?}")
        .map_err(|_| "whole Body diagnostic exceeds retained-byte bound".to_string())?;
    Ok(retained.text)
}

fn source_observation(tcx: TyCtxt<'_>, body: &Body<'_>) -> Result<ScalarSourceObservation, String> {
    if body.span.is_dummy() || body.span.from_expansion() {
        return Err("dummy or expanded body source is outside the fixed capture boundary".into());
    }
    let file = tcx.sess.source_map().lookup_source_file(body.span.lo());
    let source = file.src.as_ref().ok_or("actual normalized SourceFile bytes unavailable")?;
    if source.len() > 1024 * 1024 {
        return Err("actual SourceFile exceeds retained-byte bound".into());
    }
    let identity = ScalarSourceIdentity {
        file_name: format!("{:?}", file.name),
        stable_source_id: format!("{:?}", file.stable_id),
        original_source_hash: file.src_hash.to_string(),
        normalized_source_hash: rustc_span::SourceFileHash::new_in_memory(
            rustc_span::SourceFileHashAlgorithm::Sha256,
            source.as_bytes(),
        )
        .to_string(),
    };
    tcx.sess.with_trust_compiler_state::<ScalarCaptureRegistry, _>(|state| {
        state.intern_source(identity, source.as_str(), format!("{:?}", body.span))
    })
}

/// No `..`: a newly added rustc Body field must be classified before this
/// adapter compiles. Diagnostic metadata is retained, not silently omitted.
fn account_fields(body: &Body<'_>) -> Vec<(&'static str, &'static str)> {
    let Body {
        basic_blocks: _,
        phase: _,
        pass_count: _,
        source: _,
        source_scopes: _,
        coroutine: _,
        local_decls: _,
        user_type_annotations: _,
        arg_count: _,
        spread_arg: _,
        var_debug_info: _,
        span: _,
        required_consts: _,
        mentioned_items: _,
        is_polymorphic: _,
        injection_phase: _,
        tainted_by_errors: _,
        coverage_early_info: _,
        coverage_mir_info: _,
    } = body;
    vec![
        ("basic_blocks", "every statement/terminator/cleanup bit projected or refused"),
        ("phase", "exact runtime-post-cleanup and paired"),
        ("pass_count", "exact paired epoch"),
        ("source", "local nongeneric Item, no promotion; full identity retained"),
        ("local_decls", "all types projected; declaration metadata retained"),
        ("arg_count", "projected"),
        ("spread_arg", "refused if present"),
        ("coroutine", "refused if present"),
        ("is_polymorphic", "refused if true"),
        ("injection_phase", "refused if present"),
        ("tainted_by_errors", "refused if present"),
        (
            "required_consts",
            "unknown inventory refused; only evaluated scalar literals; no query fallback",
        ),
        ("mentioned_items", "refused if nonempty"),
        ("coverage_early_info", "refused if present"),
        ("coverage_mir_info", "refused if present"),
        ("source_scopes", "diagnostic metadata retained in complete body spelling"),
        ("user_type_annotations", "diagnostic metadata retained in complete body spelling"),
        ("var_debug_info", "diagnostic metadata retained in complete body spelling"),
        ("span", "diagnostic metadata retained; never authority"),
    ]
}

fn scalar_type(ty: ty::Ty<'_>) -> Result<ScalarType, String> {
    match ty.kind() {
        ty::Uint(ty::UintTy::U8) => Ok(ScalarType::U8),
        ty::Uint(ty::UintTy::U16) => Ok(ScalarType::U16),
        ty::Bool => Ok(ScalarType::Bool),
        ty::Tuple(fields) if fields.len() == 2 && matches!(fields[1].kind(), ty::Bool) => {
            match fields[0].kind() {
                ty::Uint(ty::UintTy::U8) => Ok(ScalarType::CheckedU8),
                ty::Uint(ty::UintTy::U16) => Ok(ScalarType::CheckedU16),
                _ => Err("unsupported checked-pair element type".into()),
            }
        }
        _ => Err("unsupported scalar local type".into()),
    }
}

fn place<'tcx>(body: &Body<'tcx>, place: mir::Place<'tcx>) -> Result<ScalarMirPlace, String> {
    let local = u32::try_from(place.local.as_usize()).map_err(|_| "local index overflow")?;
    let declaration = body.local_decls.get(place.local).ok_or("invalid place local")?;
    match &place.projection[..] {
        [] => Ok(ScalarMirPlace::Local(local)),
        [mir::ProjectionElem::Field(field, field_ty)] => {
            let ty::Tuple(fields) = declaration.ty.kind() else {
                return Err("field of non-pair".into());
            };
            if fields.len() != 2 || fields.get(field.as_usize()) != Some(field_ty) {
                return Err("field index/type identity mismatch".into());
            }
            scalar_type(declaration.ty)?;
            match field.as_usize() {
                0 => Ok(ScalarMirPlace::PairValue(local)),
                1 => Ok(ScalarMirPlace::PairFlag(local)),
                _ => Err("unsupported pair field".into()),
            }
        }
        _ => Err("projected/indirect place unsupported".into()),
    }
}

/// Upstream 1.101 removed `ScalarInt::try_to_bits`; `to_bits` panics on a
/// width disagreement, so the width is checked first (the old error arm).
fn scalar_bits(scalar: rustc_middle::ty::ScalarInt, bytes: u64) -> Result<u128, String> {
    let size = rustc_abi::Size::from_bytes(bytes);
    if scalar.size() != size {
        return Err("constant scalar width mismatch".into());
    }
    Ok(scalar.to_bits(size))
}

fn constant(value: &mir::ConstOperand<'_>) -> Result<ScalarValue, String> {
    if value.user_ty.is_some() {
        return Err("ascribed constant unsupported".into());
    }
    // Accept already-evaluated values only, never query const-evaluation and
    // change the compilation pipeline while observing it.
    if matches!(value.const_, mir::Const::Unevaluated(..)) {
        return Err("unevaluated constant".into());
    }
    let scalar = value.const_.try_to_scalar_int().ok_or("non-scalar constant")?;
    match value.const_.ty().kind() {
        ty::Uint(ty::UintTy::U8) => Ok(ScalarValue::U8(scalar_bits(scalar, 1)? as u8)),
        ty::Uint(ty::UintTy::U16) => Ok(ScalarValue::U16(scalar_bits(scalar, 2)? as u16)),
        ty::Bool => {
            Ok(ScalarValue::Bool(scalar.try_to_bool().map_err(|_| "invalid bool constant")?))
        }
        _ => Err("unsupported scalar constant type".into()),
    }
}

fn operand<'tcx>(body: &Body<'tcx>, op: &mir::Operand<'tcx>) -> Result<ScalarMirOperand, String> {
    match op {
        mir::Operand::Copy(p) => Ok(ScalarMirOperand::Copy(place(body, *p)?)),
        mir::Operand::Move(p) => Ok(ScalarMirOperand::Move(place(body, *p)?)),
        mir::Operand::Constant(c) => Ok(ScalarMirOperand::Constant(constant(c)?)),
        mir::Operand::RuntimeChecks(_) => Err("runtime-check query operand unsupported".into()),
    }
}

fn project<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Result<ScalarMirBody, String> {
    let did = body.source.def_id();
    if !did.is_local()
        || tcx.def_kind(did) != DefKind::Fn
        || tcx.generics_of(did).count() != 0
        || !matches!(body.source.instance, ty::InstanceKind::Item(_))
        || body.source.promoted.is_some()
        || body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup)
        || body.coroutine.is_some()
        || body.spread_arg.is_some()
        || body.is_polymorphic
        || body.injection_phase.is_some()
        || body.tainted_by_errors.is_some()
        || body.coverage_early_info.is_some()
        || body.coverage_mir_info.is_some()
        || body.mentioned_items.as_ref().is_some_and(|items| !items.is_empty())
        || body.local_decls.len() != 4
        || body.basic_blocks.len() != 2
        || body.arg_count != 1
    {
        return Err("body/instance/phase outside fixed scalar capture family".into());
    }
    let sig = tcx.fn_sig(did).instantiate_identity().skip_binder();
    if !sig.is_fn_trait_compatible()
        || sig.splatted().is_some()
        || sig.inputs() != [tcx.types.u8]
        || sig.output() != tcx.types.u16
    {
        return Err("actual signature is not safe Rust fn(u8)->u16".into());
    }
    let constants =
        body.required_consts.as_ref().ok_or("required-constant inventory has not been computed")?;
    for value in constants {
        constant(value)?;
    }
    let locals = body
        .local_decls
        .iter()
        .map(|decl| {
            let mir::LocalDecl { mutability: _, local_info: _, ty, user_ty: _, source_info: _ } =
                decl;
            scalar_type(*ty)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut blocks = Vec::new();
    for block in body.basic_blocks.iter() {
        if block.statements.len() > 16 {
            return Err("statement bound exceeded".into());
        }
        let mut statements = Vec::new();
        for statement in &block.statements {
            let mir::StatementKind::Assign(assignment) = &statement.kind else {
                return Err("storage/no-op/effect statement is not omitted by capture".into());
            };
            let (destination, value) = &**assignment;
            let Some(local) = destination.as_local() else {
                return Err("projected assignment".into());
            };
            let value = match value {
                mir::Rvalue::Use(value, retag) => ScalarMirRvalue::Use(
                    operand(body, value)?,
                    match retag {
                        mir::WithRetag::Yes => ScalarMirRetag::Yes,
                        mir::WithRetag::No => ScalarMirRetag::No,
                    },
                ),
                mir::Rvalue::Cast(mir::CastKind::IntToInt, value, ty)
                    if *ty == tcx.types.u16 && value.ty(&body.local_decls, tcx) == tcx.types.u8 =>
                {
                    ScalarMirRvalue::WidenU8ToU16(operand(body, value)?)
                }
                mir::Rvalue::BinaryOp(mir::BinOp::AddWithOverflow, args) => {
                    ScalarMirRvalue::CheckedAdd(operand(body, &args.0)?, operand(body, &args.1)?)
                }
                _ => return Err("rvalue outside exact scalar model".into()),
            };
            statements.push(ScalarMirStatement::Assign(local.as_usize() as u32, value));
        }
        let terminator = match &block.terminator().kind {
            mir::TerminatorKind::Goto { target, .. } => {
                ScalarMirTerminator::Goto(target.as_usize() as u32)
            }
            mir::TerminatorKind::Return => ScalarMirTerminator::Return,
            mir::TerminatorKind::Assert { cond, expected, msg, target, unwind } => {
                let mir::AssertKind::Overflow(mir::BinOp::Add, left, right) = &**msg else {
                    return Err("non-add overflow assertion".into());
                };
                // The model does not distinguish Terminate(Abi/InCleanup).
                // Refuse both rather than collapse a semantic field.
                let unwind = match unwind {
                    mir::UnwindAction::Continue => ScalarMirUnwind::Continue,
                    mir::UnwindAction::Unreachable => ScalarMirUnwind::Unreachable,
                    mir::UnwindAction::Cleanup(target) => {
                        ScalarMirUnwind::Cleanup(target.as_usize() as u32)
                    }
                    mir::UnwindAction::Terminate(_) => {
                        return Err("terminate reason not modeled".into());
                    }
                };
                ScalarMirTerminator::AssertOverflowAdd {
                    condition: operand(body, cond)?,
                    expected: *expected,
                    target: target.as_usize() as u32,
                    unwind,
                    left: operand(body, left)?,
                    right: operand(body, right)?,
                }
            }
            _ => return Err("call/cleanup/control terminator outside exact model".into()),
        };
        blocks.push(ScalarMirBlock { cleanup: block.is_cleanup, statements, terminator });
    }
    Ok(ScalarMirBody { abi: ScalarMirAbi::Rust, argument_count: 1, locals, blocks })
}

#[cfg(test)]
mod tests;
