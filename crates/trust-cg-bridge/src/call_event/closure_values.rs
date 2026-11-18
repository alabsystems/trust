//! Logical closure capture values for CER's producer-side evaluator.
//!
//! This is value transport, not a memory or indirect-call model. Incoming
//! environments retain an opaque code identity; a constructor retains its
//! exact target. Neither identity is an extra physical capture field.

use trust_ir::ClosureTyId;

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum TargetIdentity {
    Known(FuncId),
    Incoming(ValueId),
}

#[derive(Clone)]
pub(super) struct Capture {
    ty: IrTy,
    value: IrValue,
}

impl Capture {
    pub(super) fn checked(ty: IrTy, value: IrValue) -> Result<Self, String> {
        let width = capture_width(&ty)?;
        if width != value.width {
            return Err("closure capture formula has the wrong declared width".into());
        }
        Ok(Self { ty, value })
    }
}

#[derive(Clone)]
pub(super) struct ClosureValue {
    pub nominal: ClosureTyId,
    pub target: TargetIdentity,
    pub captures: Vec<Capture>,
}

fn capture_width(ty: &IrTy) -> Result<u32, String> {
    match ty {
        IrTy::Ptr
        | IrTy::I8
        | IrTy::I16
        | IrTy::I32
        | IrTy::I64
        | IrTy::Isize
        | IrTy::U8
        | IrTy::U16
        | IrTy::U32
        | IrTy::U64
        | IrTy::Usize => scalar_reg_width(ty),
        _ => Err(format!("closure capture type {ty:?} is outside the scalar value model")),
    }
}

/// The original-transition census admits an observed empty frame or the nominal
/// one-field thin-pointer carrier. The environment stays a Closure value, including its
/// opaque/known code identity; this check never substitutes Ptr for that type.
/// Source/codegen declarations, apparent signatures and observed frames must
/// agree independently. Numeric width or a helper/symbol name is insufficient.
pub(super) fn original_nominal(
    source: &Module,
    codegen: &Module,
    nominal: ClosureTyId,
) -> Result<(), String> {
    for module in [source, codegen] {
        if !abi_extensions::qualified_target(module) {
            return Err("original closure carrier has no qualified target".into());
        }
        module.validate_closure_layouts().map_err(|e| format!("original closure frame: {e}"))?;
    }
    let declaration = source.closure_type(nominal).ok_or("original nominal closure is absent")?;
    let actual = codegen.closure_type(nominal).ok_or("codegen nominal closure is absent")?;
    let signature =
        source.func_type(declaration.func).ok_or("closure apparent signature absent")?;
    let actual_signature =
        codegen.func_type(actual.func).ok_or("codegen closure signature absent")?;
    let frame = source
        .closure_layout_descriptor(nominal)
        .map_err(|e| format!("original closure frame: {e}"))?
        .ok_or("original closure has no observed frame")?;
    let actual_frame = codegen
        .closure_layout_descriptor(nominal)
        .map_err(|e| format!("codegen closure frame: {e}"))?
        .ok_or("codegen closure has no observed frame")?;
    if actual.captures != declaration.captures
        || signature != actual_signature
        || signature.is_vararg
        || signature.abi.is_some()
        || actual_frame.size != frame.size
        || actual_frame.align != frame.align
        || actual_frame.capture_offsets != frame.capture_offsets
        || actual_frame.origin != frame.origin
    {
        return Err("original nominal closure declaration/signature/observed frame differs from the supported complete carrier".into());
    }
    // An empty environment adds no capture formula or memory observation.
    // Its code identity remains opaque/known under the existing direct-edge
    // rules; the complete original census still checks every scalar operation.
    let empty = declaration.captures.is_empty()
        && frame.size == 0 && frame.align == 1 && frame.capture_offsets.is_empty()
        && signature.returns.len() <= 1
        && signature.params.iter().chain(&signature.returns)
            .all(|ty| source_memory::width(ty).is_ok());
    let pointer = declaration.captures == [IrTy::Ptr]
        && signature.params.is_empty() && signature.returns == [IrTy::Ptr]
        && frame.size == 8 && frame.align == 8 && frame.capture_offsets == [0];
    if !empty && !pointer {
        return Err("original nominal closure is outside the observed empty/pointer carrier".into());
    }
    Ok(())
}

/// Check the logical aggregate and its exact declared field before the full
/// original census may include a projection. The existing ClosureValue
/// evaluator supplies its typed capture formula, never a memory load or alias
/// premise. All other aggregate projections remain outside this census.
pub(super) fn original_projection(
    source: &Module,
    function: &trust_ir::Function,
    codegen: &Module,
    aggregate: ValueId,
    field: u32,
    ty: &IrTy,
) -> Result<(), String> {
    let value = function
        .typed_value(source, aggregate)
        .ok_or("original closure projection has no typed aggregate")?;
    let IrTy::Closure(nominal) = value.ty else {
        return Err("original projection is not a nominal closure value".into());
    };
    original_nominal(source, codegen, nominal)?;
    if field != 0 || *ty != IrTy::Ptr
        || source.closure_type(nominal)
            .and_then(|declaration| declaration.captures.get(field as usize)) != Some(ty)
    {
        return Err("original projection differs from the exact nominal capture field/type".into());
    }
    Ok(())
}

/// Captures alone do not encode a closure's code identity. Such an argument
/// may cross only a direct edge into this exact producer's non-preemptible
/// body. That body's own certificate must cover its handling of the opaque
/// identity. An indirect application, memory observation, or further unmodeled
/// use remains Unknown there and blocks the existing whole-object closure.
pub(super) fn direct_call_boundary(
    input: &CerInput<'_>,
    caller: ProducerBody,
    callee: FuncId,
    symbol: &str,
    non_preemptible: bool,
) -> Result<(), String> {
    let body =
        input.bodies.get(symbol).ok_or("closure code identity has no co-emitted callee body")?;
    if !non_preemptible || body.producer != caller.producer || body.func != callee {
        return Err("closure code identity requires the same producer's exact non-preemptible direct callee".into());
    }
    let producer =
        input.producers.get(body.producer).ok_or("closure callee producer is missing")?;
    let function =
        producer.module.function_by_id(body.func).ok_or("closure callee body is missing")?;
    if function.is_declaration()
        || function.name != symbol
        || producer.symbols.get(&callee).map(String::as_str) != Some(symbol)
    {
        return Err(
            "closure code identity has no exact same-module callee definition/symbol".into()
        );
    }
    Ok(())
}

/// Qualify an ignored/scalar/pair environment against its observed physical frame.
/// P is in logical capture order. Its register order must instead follow the
/// recorded offsets: reversing source fields cannot reverse the ABI words.
/// Packed fields, padding-only words, extensions and stack carriers remain
/// outside this model rather than being reconstructed by a size guess.
pub(super) fn placement(
    module: &Module,
    nominal: ClosureTyId,
    place: &ParamPlace,
) -> Result<Vec<ScalarPlace>, String> {
    let target = module.target_info.as_ref().ok_or("closure ABI has no target descriptor")?;
    if target.pointer_size != 8 || target.endianness != trust_ir::Endianness::Little {
        return Err("closure ABI is not the modeled 64-bit little-endian transport".into());
    }
    module.validate_closure_layouts().map_err(|e| format!("closure frame: {e}"))?;
    let closure = module.closure_type(nominal).ok_or("closure ABI has no nominal declaration")?;
    let frame = module
        .closure_layout_descriptor(nominal)
        .map_err(|e| format!("closure frame: {e}"))?
        .ok_or("closure ABI has no observed frame")?;
    let slots = match place {
        // The logical nominal environment survives an empty physical ABI.
        // Its exact frame is checked below; no incoming code identity is minted.
        ParamPlace::Ignore if closure.captures.is_empty() => vec![],
        ParamPlace::Scalar(slot) if closure.captures.len() == 1 => vec![*slot],
        ParamPlace::Pair(a, b) if closure.captures.len() == 2 => vec![*a, *b],
        _ => {
            return Err("closure ABI scalar/pair arity differs from its capture declaration".into());
        }
    };
    let mut size = 0u64;
    let mut align = 1u64;
    for (ty, slot) in closure.captures.iter().zip(&slots) {
        let bits = capture_width(ty)?;
        if slot.width != bits || slot.ext != AbiExt::None {
            return Err("closure ABI width/extension differs from its declared capture".into());
        }
        if !matches!(slot.slot, Slot::Gpr(r) if r < 8) {
            return Err(
                "closure ABI needs an independently modeled integer-register carrier".into()
            );
        }
        let bytes = u64::from(bits / 8);
        align = align.max(bytes);
        size = size.div_ceil(bytes) * bytes + bytes;
    }
    size = size.div_ceil(align) * align;
    if frame.size != size || frame.align != align {
        return Err("closure frame totals disagree with the native scalar carrier".into());
    }
    match slots.as_slice() {
        [] if frame.capture_offsets.is_empty() && size == 0 && align == 1 => {}
        [_] if frame.capture_offsets == [0] && size <= 8 => {}
        [a, b] if size > 8 && size <= 16 => {
            let (first, second) = match frame.capture_offsets.as_slice() {
                [0, 8] => (a, b),
                [8, 0] => (b, a),
                _ => {
                    return Err("closure pair is not two separately observed argument words".into());
                }
            };
            if !matches!((first.slot, second.slot), (Slot::Gpr(a), Slot::Gpr(b)) if b == a + 1) {
                return Err(
                    "closure ABI registers do not follow its observed physical field order".into(),
                );
            }
        }
        _ => return Err("closure ABI is not the observed one/two-word source transport".into()),
    }
    Ok(slots)
}

impl ClosureValue {
    /// A typed local store retains this value, not a scalar encoding of its
    /// environment. The cell's immutable module has independently supplied
    /// its unique storage target and complete declared capture types.
    pub(super) fn check_local_storage(
        &self,
        nominal: ClosureTyId,
        target: FuncId,
        captures: &[IrTy],
    ) -> Result<(), String> {
        if self.nominal != nominal || self.target != TargetIdentity::Known(target) {
            return Err("nominal local store has a different or unknown closure target/type".into());
        }
        if self.captures.len() != captures.len() {
            return Err("nominal local store has a different capture count".into());
        }
        for (actual, declared) in self.captures.iter().zip(captures) {
            if actual.ty != *declared || actual.value.width != capture_width(declared)? {
                return Err("nominal local store has a different capture type/width".into());
            }
        }
        Ok(())
    }

    pub(super) fn incoming(
        module: &Module,
        nominal: ClosureTyId,
        id: ValueId,
        place: &ParamPlace,
    ) -> Result<Self, String> {
        let slots = placement(module, nominal, place)?;
        let closure = module.closure_type(nominal).ok_or("closure type disappeared")?;
        let captures = closure
            .captures
            .iter()
            .zip(slots)
            .map(|(ty, slot)| {
                Capture::checked(
                    ty.clone(),
                    IrValue { f: read_slot_spec(&slot)?, width: slot.width },
                )
            })
            .collect::<Result<_, String>>()?;
        Ok(Self { nominal, target: TargetIdentity::Incoming(id), captures })
    }

    /// A MakeClosure target has captures ++ apparent parameters. Its direct
    /// callee may subsequently take the one logical environment; these are
    /// different signatures and are never conflated by this check.
    pub(super) fn construct(
        module: &Module,
        nominal: ClosureTyId,
        target: FuncId,
        captures: Vec<Capture>,
    ) -> Result<Self, String> {
        let closure = module.closure_type(nominal).ok_or("MakeClosure nominal type is missing")?;
        let apparent =
            module.func_type(closure.func).ok_or("MakeClosure apparent signature is missing")?;
        let function = module.function_by_id(target).ok_or("MakeClosure target is missing")?;
        let physical =
            module.func_type(function.ty).ok_or("MakeClosure physical signature is missing")?;
        let expected: Vec<_> = closure.captures.iter().chain(&apparent.params).cloned().collect();
        if apparent.is_vararg
            || physical.is_vararg
            || physical.params != expected
            || physical.returns != apparent.returns
            || physical.abi != apparent.abi
        {
            return Err("MakeClosure target is not the capture-prefix physical signature".into());
        }
        if captures.len() != closure.captures.len()
            || captures.iter().zip(&closure.captures).any(|(actual, ty)| actual.ty != *ty)
        {
            return Err("MakeClosure values differ from the nominal capture types/arity".into());
        }
        Ok(Self { nominal, target: TargetIdentity::Known(target), captures })
    }

    pub(super) fn project(&self, ty: &IrTy, field: u32) -> Result<IrValue, String> {
        let capture =
            self.captures.get(field as usize).ok_or("closure capture index is out of bounds")?;
        if capture.ty != *ty {
            return Err("ExtractField closure result differs from the declared capture type".into());
        }
        Ok(capture.value.clone())
    }

    pub(super) fn arguments(
        &self,
        module: &Module,
        expected: &IrTy,
        place: &ParamPlace,
    ) -> Result<Vec<Formula>, String> {
        if expected != &IrTy::Closure(self.nominal) {
            return Err("direct call closure has the wrong nominal environment type".into());
        }
        let slots = placement(module, self.nominal, place)?;
        let declared =
            &module.closure_type(self.nominal).ok_or("closure type is missing")?.captures;
        if self.captures.len() != declared.len() {
            return Err("direct call closure has the wrong capture arity".into());
        }
        self.captures
            .iter()
            .zip(declared)
            .zip(slots)
            .map(|((capture, ty), slot)| {
                if capture.ty != *ty || capture.value.width != slot.width {
                    Err("direct call closure capture differs from its declared type/placement"
                        .into())
                } else {
                    Ok(capture.value.f.clone())
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests;
