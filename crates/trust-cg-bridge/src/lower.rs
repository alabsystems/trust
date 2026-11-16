//! Lowering from trust-types IR to trust_cg LIR.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cg_lower::function::{
    BasicBlock as LirBlock, Function as LirFunction, Signature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, DirectCallBinding, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, AssertMessage, AtomicOpKind, BasicBlock as TrustBlock, BinOp, ConstValue,
    Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    UnOp, VerifiableBody, VerifiableFunction,
};

use crate::BridgeError;
use crate::mapping::{
    cmpxchg_failure_ordering, deref_type, downcast_type, element_type, encode_switch_case,
    encode_switch_cases, field_type, is_trivially_copy_ty, map_atomic_ordering, map_atomic_rmw_op,
    map_binop, map_float_binop, map_type, map_unop,
};

const ABORT_SYMBOL: &str = "abort";
pub(crate) const TRUST_LOCATION_FILE_GLOBAL_PREFIX: &str = "__trust_panic_file_";

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PanicRuntimeSymbols {
    pub add_overflow: Option<String>,
    pub sub_overflow: Option<String>,
    pub mul_overflow: Option<String>,
    pub div_overflow: Option<String>,
    pub rem_overflow: Option<String>,
    pub neg_overflow: Option<String>,
    pub shl_overflow: Option<String>,
    pub shr_overflow: Option<String>,
    pub div_by_zero: Option<String>,
    pub rem_by_zero: Option<String>,
    pub null_pointer_dereference: Option<String>,
}

impl PanicRuntimeSymbols {
    fn symbol_for_assert(&self, msg: &AssertMessage) -> Option<&str> {
        match msg {
            AssertMessage::Overflow(BinOp::Add) => self.add_overflow.as_deref(),
            AssertMessage::Overflow(BinOp::Sub) => self.sub_overflow.as_deref(),
            AssertMessage::Overflow(BinOp::Mul) => self.mul_overflow.as_deref(),
            AssertMessage::Overflow(BinOp::Div) => self.div_overflow.as_deref(),
            AssertMessage::Overflow(BinOp::Rem) => self.rem_overflow.as_deref(),
            AssertMessage::Overflow(BinOp::Shl) => self.shl_overflow.as_deref(),
            AssertMessage::Overflow(BinOp::Shr) => self.shr_overflow.as_deref(),
            AssertMessage::OverflowNeg => self.neg_overflow.as_deref(),
            AssertMessage::DivisionByZero => self.div_by_zero.as_deref(),
            AssertMessage::RemainderByZero => self.rem_by_zero.as_deref(),
            AssertMessage::NullPointerDereference => self.null_pointer_dereference.as_deref(),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LoweringOptions {
    pub panic_symbols: PanicRuntimeSymbols,
    /// Function-entry register bindings for a binary-lifted body (see
    /// `crate::entry_binding`). `None` — the default, and the only value the
    /// MIR lane ever passes — leaves lowering byte-identical to before the
    /// field existed. `Some` makes bare bound register `Var`s and the 8-byte
    /// little-endian load shape lowerable against real LIR parameters, each
    /// use individually justified by the per-block write-freedom certificate
    /// computed over the body being lowered.
    pub entry_bindings: Option<crate::entry_binding::BinaryEntryBindings>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum PanicBlockAction {
    Abort,
    RuntimeCall { symbol: String, span: SourceSpan },
}

#[derive(Clone, Debug)]
struct BlockParam {
    local: usize,
    value: Value,
    ty: LirType,
}

fn is_type_only_projection(projection: &Projection) -> bool {
    matches!(projection, Projection::OpaqueCast(_) | Projection::UnwrapUnsafeBinder(_))
}

fn place_is_direct_local(place: &Place) -> bool {
    place.projections.iter().all(is_type_only_projection)
}

fn is_addressable_local_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Tuple(_) | Ty::Adt { .. } | Ty::Array { .. })
}

/// Whether `resolve_place_addr` computes the address of `place` from the base local's pointer
/// VALUE: the place starts by dereferencing a thin pointer (one I64) or a slice fat pointer held
/// in a non-aggregate local, so the address of `*p…` is `p` itself and `p` needs no memory of
/// its own. (`resolve_place` reads `*p…` the same way.) Spilling `p` to a slot instead would
/// make a later read of `p` reload it from the frame after a store THROUGH `p`, which the
/// output gate cannot show does not alias the slot. Any other pointer shape keeps the slot.
fn place_addr_starts_at_pointer_value(place: &Place, base_ty: &Ty) -> bool {
    if !matches!(place.projections.first(), Some(Projection::Deref))
        || is_addressable_local_ty(base_ty)
    {
        return false;
    }
    match deref_type(base_ty) {
        Ok(Ty::Slice { .. }) => map_lowering_type(base_ty).is_ok(),
        Ok(_) => matches!(map_lowering_type(base_ty), Ok(LirType::I64)),
        Err(_) => false,
    }
}

fn slice_element_type(ty: &Ty) -> Option<Ty> {
    match ty {
        Ty::Slice { elem } => Some((**elem).clone()),
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => match inner.as_ref() {
            Ty::Slice { elem } => Some((**elem).clone()),
            _ => None,
        },
        _ => None,
    }
}

fn slice_fat_pointer_lir_ty_for_elem(elem_ty: &Ty) -> Result<LirType, BridgeError> {
    let _ = map_type(elem_ty)?;
    Ok(LirType::Struct(vec![LirType::I64, LirType::I64]))
}

fn slice_fat_pointer_lir_ty(source_ty: &Ty) -> Result<LirType, BridgeError> {
    let elem_ty = slice_element_type(source_ty).ok_or_else(|| {
        BridgeError::UnsupportedOp(format!("expected slice fat-pointer type, got {source_ty:?}"))
    })?;
    slice_fat_pointer_lir_ty_for_elem(&elem_ty)
}

#[allow(rustc::default_hash_types)]
fn new_lir_value_type_map() -> std::collections::HashMap<Value, LirType> {
    // trust-cg's public LIR API owns this map as `std::collections::HashMap`.
    std::collections::HashMap::new()
}

fn subslice_result_type(
    ty: &Ty,
    from: usize,
    to: usize,
    from_end: bool,
) -> Result<Ty, BridgeError> {
    match ty {
        Ty::Array { elem, len } => {
            let start = from as u64;
            let end = if from_end {
                len.checked_sub(to as u64).ok_or_else(|| {
                    BridgeError::UnsupportedOp(format!(
                        "Subslice from_end offset {to} exceeds array length {len}"
                    ))
                })?
            } else {
                to as u64
            };
            if start > end || end > *len {
                return Err(BridgeError::UnsupportedOp(format!(
                    "Subslice range {from}..{} exceeds array length {len}",
                    if from_end { format!("-{to}") } else { to.to_string() }
                )));
            }
            Ok(Ty::Array { elem: elem.clone(), len: end - start })
        }
        Ty::Slice { elem } => {
            if !from_end && to < from {
                return Err(BridgeError::UnsupportedOp(format!(
                    "Subslice range {from}..{to} is inverted"
                )));
            }
            Ok(Ty::Slice { elem: elem.clone() })
        }
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => match inner.as_ref() {
            Ty::Slice { elem } => {
                if !from_end && to < from {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "Subslice range {from}..{to} is inverted"
                    )));
                }
                Ok(Ty::Slice { elem: elem.clone() })
            }
            _ => Err(BridgeError::UnsupportedOp(format!(
                "Subslice projection on non-slice pointer type {ty:?}"
            ))),
        },
        _ => Err(BridgeError::UnsupportedOp(format!(
            "Subslice projection on non-slice/array type {ty:?}"
        ))),
    }
}

/// Internal state for the lowering pass.
#[allow(rustc::default_hash_types)]
struct LoweringCtx<'a> {
    /// Local variable declarations from the trust-types body.
    locals: &'a [LocalDecl],
    /// Map from trust-types local index to LIR Value.
    local_values: FxHashMap<usize, Value>,
    /// Type hints for Values whose producing opcode omits result type metadata.
    value_types: std::collections::HashMap<Value, LirType>,
    /// Next available Value id.
    next_value: u32,
    /// Stack slots allocated for memory operations (aggregates, address-of, etc.).
    stack_slots: Vec<StackSlotInfo>,
    /// Map from trust-types local index to stack slot index (for locals that
    /// need an address, e.g., aggregates or locals whose address is taken).
    local_stack_slots: FxHashMap<usize, u32>,
    /// Locals whose value lives in ONE stack slot for the whole function (see
    /// `collect_memory_backed_locals`): the slot is allocated before any block is
    /// lowered, every whole-local definition stores into it, and every read loads
    /// from it, so what a path reads never depends on which block was lowered first.
    memory_backed: FxHashSet<usize>,
    /// Values that ARE the address of an aggregate's bytes (a tuple/ADT/array or a slice fat
    /// pointer; `emit_store_value`): every snapshot `emit_load_value` takes and every fat
    /// pointer `emit_slice_fat_pointer` builds. A whole write of an aggregate type copies bytes
    /// FROM its value, so a write whose value is not one of these (a scalar, a constant) is
    /// refused (`emit_checked_store`) instead of copying from an address the value is not.
    aggregate_carriers: FxHashSet<Value>,
    /// Lazily-allocated panic block ID for Assert terminators.
    /// Blocks are inserted into the function after lowering.
    panic_blocks: Vec<(PanicBlockAction, Block)>,
    /// Lowering policy for runtime-sensitive constructs.
    options: &'a LoweringOptions,
    /// Synthetic edge blocks used to materialize block-param copies on
    /// conditional control-flow edges.
    pending_blocks: Vec<(Block, LirBlock)>,
    /// Next available block ID (tracks the highest block ID seen + 1).
    next_block_id: u32,
    /// Entry-register binding state for a binary-lifted body (None on the MIR
    /// lane and when the per-body analysis refused the table).
    entry_bindings: Option<EntryBindingState>,
    /// When the entry-binding table was supplied but refused for this body,
    /// the reason — attached to symbolic-operand refusals so they carry the
    /// fix instead of a bare "unsupported".
    entry_binding_refusal: Option<String>,
    /// Source block id currently being lowered (drives the per-block
    /// write-freedom gate on entry-register uses).
    current_block: usize,
    /// Statement index within the current block (keys consumption records).
    current_statement: usize,
    /// True while the current block's TERMINATOR is being lowered. Entry-binding
    /// lowering is refused in this position: consumption records are keyed by
    /// statement index, terminator operands have none (and no evidence rows to
    /// mark), so consuming here would misattribute the consumption. Production
    /// discriminants are flag formulas that refuse regardless; this keeps the
    /// latent bare-Var-discriminant path fail-closed instead of mis-keyed.
    in_terminator: bool,
    /// Symbolic formulas this lowering consumed with target semantics.
    consumed_symbolic: Vec<crate::entry_binding::ConsumedSymbolicLowering>,
}

/// Materialized entry-register bindings: the params' LIR values plus the
/// per-block write-freedom certificate that justifies each use.
struct EntryBindingState {
    bindings: crate::entry_binding::BinaryEntryBindings,
    /// var name (e.g. "X7") -> (param index, the param's LIR Value).
    params_by_var: FxHashMap<String, (usize, Value)>,
    preservation: crate::entry_binding::EntryPreservation,
}

/// Outcome of the per-body entry-binding analysis, fed into `LoweringCtx`.
enum EntryBindingInputs {
    /// The table cross-checked against the body and the certificate computed:
    /// params become real LIR formals.
    Justified {
        bindings: crate::entry_binding::BinaryEntryBindings,
        preservation: crate::entry_binding::EntryPreservation,
    },
    /// The table was supplied but refused for this body; lowering proceeds
    /// without params and symbolic refusals carry the reason.
    Refused { reason: String },
}

impl<'a> LoweringCtx<'a> {
    fn new(
        locals: &'a [LocalDecl],
        arg_count: usize,
        max_block_id: u32,
        options: &'a LoweringOptions,
        entry: Option<EntryBindingInputs>,
    ) -> Self {
        let mut ctx = Self {
            locals,
            local_values: FxHashMap::with_capacity_and_hasher(locals.len(), Default::default()),
            value_types: new_lir_value_type_map(),
            next_value: 0,
            stack_slots: Vec::new(),
            local_stack_slots: FxHashMap::default(),
            memory_backed: FxHashSet::default(),
            aggregate_carriers: FxHashSet::default(),
            panic_blocks: Vec::new(),
            options,
            pending_blocks: Vec::new(),
            next_block_id: max_block_id + 1,
            entry_bindings: None,
            entry_binding_refusal: None,
            current_block: 0,
            current_statement: 0,
            in_terminator: false,
            consumed_symbolic: Vec::new(),
        };
        // trust_cg ISel convention: Value(0)..Value(k-1) are formal arguments.
        // Entry-register binding params come first (the binary lane, where
        // arg_count is 0 by the lift's observations-not-arguments rule); MIR
        // argument locals follow the same convention below. The two lanes are
        // mutually exclusive, enforced in lower_body_to_lir_with_options.
        match entry {
            Some(EntryBindingInputs::Justified { bindings, preservation }) => {
                let mut params_by_var = FxHashMap::default();
                for (param_index, param) in bindings.params.iter().enumerate() {
                    let value = Value(ctx.next_value);
                    ctx.next_value += 1;
                    params_by_var.insert(param.var_name.clone(), (param_index, value));
                }
                ctx.entry_bindings =
                    Some(EntryBindingState { bindings, params_by_var, preservation });
            }
            Some(EntryBindingInputs::Refused { reason }) => {
                ctx.entry_binding_refusal = Some(reason);
            }
            None => {}
        }
        // Trust-types convention: local 0 is the return slot, locals 1..=arg_count are args.
        // Assign argument locals first to match ISel expectations.
        for i in 1..=arg_count {
            let local = locals
                .get(i)
                .filter(|l| l.index == i)
                .or_else(|| locals.iter().find(|l| l.index == i));
            if let Some(local) = local {
                let val = Value(ctx.next_value);
                ctx.next_value += 1;
                ctx.local_values.insert(local.index, val);
            }
        }
        // Then assign remaining locals (return slot at index 0, and any others).
        for local in locals {
            if !ctx.local_values.contains_key(&local.index) {
                let val = Value(ctx.next_value);
                ctx.next_value += 1;
                ctx.local_values.insert(local.index, val);
            }
        }
        ctx
    }

    /// Allocate a fresh temporary Value.
    fn fresh_value(&mut self) -> Value {
        let v = Value(self.next_value);
        self.next_value += 1;
        v
    }

    /// Get the LIR Value for a trust-types local index.
    fn local_value(&self, index: usize) -> Result<Value, BridgeError> {
        self.local_values.get(&index).copied().ok_or(BridgeError::MissingLocal(index))
    }

    /// Record a type hint for a Value whose opcode omits typed results.
    fn record_value_type(&mut self, value: Value, ty: LirType) {
        self.value_types.insert(value, ty);
    }

    /// Get the type of a local by index.
    fn local_ty(&self, index: usize) -> Result<&Ty, BridgeError> {
        self.locals
            .get(index)
            .filter(|l| l.index == index)
            .or_else(|| self.locals.iter().find(|l| l.index == index))
            .map(|l| &l.ty)
            .ok_or(BridgeError::MissingLocal(index))
    }

    /// Get the fully-projected type of a place.
    fn place_ty(&self, place: &Place) -> Result<Ty, BridgeError> {
        let mut current_ty = self.local_ty(place.local)?.clone();
        // The variant a `Downcast` names, live for the one `Field` after it
        // (`projected_field`): the same rule `resolve_place` and
        // `resolve_place_addr` apply, so the three walks agree on the field.
        let mut active_variant: Option<usize> = None;

        for proj in &place.projections {
            let downcast = active_variant.take();
            check_downcast_followed_by_field(&current_ty, downcast, proj)?;
            current_ty = match proj {
                Projection::Field(field_idx) => {
                    projected_field(&current_ty, downcast, *field_idx, "place type")?.1
                }
                Projection::Deref => deref_type(&current_ty)?,
                Projection::Index(_) | Projection::ConstantIndex { .. } => {
                    element_type(&current_ty)?
                }
                Projection::Downcast(variant_idx) => {
                    active_variant = Some(*variant_idx);
                    downcast_type(&current_ty, *variant_idx)?
                }
                Projection::Subslice { from, to, from_end } => {
                    subslice_result_type(&current_ty, *from, *to, *from_end)?
                }
                Projection::OpaqueCast(ty) | Projection::UnwrapUnsafeBinder(ty) => ty.clone(),
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "unsupported projection in place_ty: {other:?}"
                    )));
                }
            };
        }

        Ok(current_ty)
    }

    /// Get the LIR pointee type for an atomic pointer operand.
    fn atomic_lir_ty(&self, place: &Place) -> Result<LirType, BridgeError> {
        let ptr_ty = self.place_ty(place)?;
        let pointee_ty = ptr_ty.pointee_ty().ok_or_else(|| {
            BridgeError::UnsupportedOp(format!(
                "atomic pointer operand is not pointer-like: {ptr_ty:?}"
            ))
        })?;
        map_type(pointee_ty)
    }

    /// Get the bit width of a type (for cast width comparisons).
    fn ty_bit_width(ty: &Ty) -> Option<u32> {
        match ty {
            Ty::Bool => Some(1),
            Ty::Int { width, .. } => Some(*width),
            Ty::Bv(w) => Some(*w),
            _ => None,
        }
    }

    /// Allocate a stack slot and return its index.
    fn alloc_stack_slot(&mut self, ty: &LirType) -> u32 {
        let slot = self.stack_slots.len() as u32;
        self.stack_slots.push(StackSlotInfo::new(ty.bytes(), ty.align()));
        slot
    }

    /// Ensure a local has an associated stack slot, returning the slot index.
    fn ensure_local_stack_slot(&mut self, local_idx: usize) -> Result<u32, BridgeError> {
        if let Some(&slot) = self.local_stack_slots.get(&local_idx) {
            return Ok(slot);
        }
        let ty = self.local_ty(local_idx)?;
        let lir_ty = map_lowering_type(ty)?;
        let slot = self.alloc_stack_slot(&lir_ty);
        self.local_stack_slots.insert(local_idx, slot);
        Ok(slot)
    }

    /// Make every local in `candidates` whose type has a LIR lowering memory-backed, and
    /// allocate its single slot now, before any block is lowered (ascending local order, so
    /// slot numbering is deterministic).
    fn plan_memory_backed_locals(&mut self, candidates: &FxHashSet<usize>) {
        let mut locals: Vec<usize> = candidates.iter().copied().collect();
        locals.sort_unstable();
        for local_idx in locals {
            // A local without a LIR type cannot live in a slot; any path that asks for its
            // address fails in `materialize_local_stack_addr` with the type error, as before.
            let Ok(ty) = self.local_ty(local_idx) else { continue };
            if map_lowering_type(ty).is_err() {
                continue;
            }
            if self.ensure_local_stack_slot(local_idx).is_ok() {
                self.memory_backed.insert(local_idx);
            }
        }
    }

    fn is_memory_backed(&self, local_idx: usize) -> bool {
        self.memory_backed.contains(&local_idx)
    }

    /// The single slot of a memory-backed local. Asking for the slot of any other local is a
    /// planning gap (`collect_memory_backed_locals` missed a place that needs the local's
    /// address), refused rather than papered over with a lazily initialized slot: a lazy slot
    /// is initialized in whichever block happens to be lowered first, which is exactly the
    /// order-dependent wrong code this planning exists to remove.
    fn memory_backed_slot(&self, local_idx: usize) -> Result<u32, BridgeError> {
        if self.is_memory_backed(local_idx)
            && let Some(&slot) = self.local_stack_slots.get(&local_idx)
        {
            return Ok(slot);
        }
        // Keep the type error for a local that has no LIR representation at all.
        map_lowering_type(self.local_ty(local_idx)?)?;
        Err(BridgeError::UnsupportedOp(format!(
            "local _{local_idx} needs a stack slot but was not planned memory-backed; \
             refusing to materialize it lazily (a lazily initialized slot is written only in \
             the first block lowered, so sibling paths would read memory they never wrote)"
        )))
    }

    /// The address of a memory-backed local's slot. Emits no store: the slot is kept current
    /// at every definition (`store_memory_backed_definition`, the function-entry prologue and
    /// the aggregate constructors), so it already holds the value on every path.
    fn materialize_local_stack_addr(
        &mut self,
        local_idx: usize,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let slot = self.memory_backed_slot(local_idx)?;
        Ok(self.emit_stack_addr(slot, instructions))
    }

    /// The current value of a whole local. A memory-backed local is loaded from its slot (it
    /// may have been written through a pointer or a field store since its last SSA
    /// definition); every other local is its SSA value.
    fn read_local(
        &mut self,
        local_idx: usize,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if !self.is_memory_backed(local_idx) {
            return self.local_value(local_idx);
        }
        let ty = map_lowering_type(self.local_ty(local_idx)?)?;
        let addr = self.materialize_local_stack_addr(local_idx, instructions)?;
        Ok(self.emit_load_value(ty, addr, instructions))
    }

    /// Keep a memory-backed local's slot current at a whole-local definition. A no-op for
    /// every other local.
    fn store_memory_backed_definition(
        &mut self,
        local_idx: usize,
        value: Value,
        instructions: &mut Vec<Instruction>,
    ) -> Result<(), BridgeError> {
        if !self.is_memory_backed(local_idx) {
            return Ok(());
        }
        let ty = map_lowering_type(self.local_ty(local_idx)?)?;
        let addr = self.materialize_local_stack_addr(local_idx, instructions)?;
        self.emit_store_value(ty, value, addr, instructions);
        Ok(())
    }

    /// Copy the `ty.bytes()` bytes of an aggregate from `src` to `dest` with one exact-width
    /// `Memcpy` (trust-cg inlines a small constant length as exact LDR/STR lanes).
    fn emit_aggregate_copy(
        &mut self,
        ty: &LirType,
        dest: Value,
        src: Value,
        instructions: &mut Vec<Instruction>,
    ) {
        let len = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(ty.bytes()) },
            args: vec![],
            results: vec![len],
        });
        instructions.push(Instruction {
            opcode: Opcode::Memcpy,
            args: vec![dest, src, len],
            results: vec![],
        });
    }

    /// Store `value`, of LIR type `ty`, at `addr`.
    ///
    /// LIR represents an aggregate value (`Struct`/`Array`/`Enum`) by its ADDRESS — trust-cg's
    /// instruction selectors bind aggregate formals, call results and returns as address
    /// carriers — and has no whole-aggregate `Store`: `select_store` would emit ONE register
    /// store, writing the carrier (or the first eight bytes) and leaving the rest of the
    /// destination unwritten. So an aggregate is copied byte-exactly from the address it is;
    /// a scalar is one `Store`.
    fn emit_store_value(
        &mut self,
        ty: LirType,
        value: Value,
        addr: Value,
        instructions: &mut Vec<Instruction>,
    ) {
        if ty.is_aggregate() {
            self.emit_aggregate_copy(&ty, addr, value, instructions);
        } else {
            push_store(instructions, ty, value, addr);
        }
    }

    /// `emit_store_value` for a value an rvalue computed: an aggregate is copied only from a
    /// value that carries the address of its bytes (`aggregate_carriers`). A value that does
    /// not (a scalar or a constant written as a whole tuple, ill-typed MIR) is refused, never
    /// reinterpreted as an address (ticket 216 cg review 4).
    fn emit_checked_store(
        &mut self,
        ty: LirType,
        value: Value,
        addr: Value,
        instructions: &mut Vec<Instruction>,
    ) -> Result<(), BridgeError> {
        if ty.is_aggregate() && !self.aggregate_carriers.contains(&value) {
            return Err(BridgeError::UnsupportedOp(format!(
                "a write of aggregate type {ty:?} needs the address of the value's bytes; \
                 {value:?} does not carry one"
            )));
        }
        self.emit_store_value(ty, value, addr, instructions);
        Ok(())
    }

    /// Load the value of LIR type `ty` at `addr`.
    ///
    /// A scalar is one `Load`. An aggregate value is an address (see `emit_store_value`), and
    /// a whole-aggregate `Load` would read only its first register-width lane, so the bytes
    /// are copied into a fresh slot and the value is that SNAPSHOT's address: a later write
    /// to `addr` (a field store, a store through a pointer, the next definition of the local)
    /// cannot change a value already read.
    fn emit_load_value(
        &mut self,
        ty: LirType,
        addr: Value,
        instructions: &mut Vec<Instruction>,
    ) -> Value {
        if ty.is_aggregate() {
            let slot = self.alloc_stack_slot(&ty);
            let snapshot = self.emit_stack_addr(slot, instructions);
            self.emit_aggregate_copy(&ty, snapshot, addr, instructions);
            self.aggregate_carriers.insert(snapshot);
            return snapshot;
        }
        let loaded = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Load { ty, align: None },
            args: vec![addr],
            results: vec![loaded],
        });
        loaded
    }

    /// Get or create the panic block used by Assert terminators.
    ///
    /// Returns the Block id. The actual block is inserted into the function's
    /// block map by `lower_body_to_lir` after all blocks are lowered.
    fn get_or_create_panic_block(&mut self, action: PanicBlockAction) -> Block {
        if let Some((_, blk)) = self.panic_blocks.iter().find(|(existing, _)| existing == &action) {
            return *blk;
        }
        let blk = Block(self.next_block_id);
        self.next_block_id += 1;
        self.panic_blocks.push((action, blk));
        blk
    }

    /// Allocate a fresh synthetic block ID.
    fn fresh_block(&mut self) -> Block {
        let blk = Block(self.next_block_id);
        self.next_block_id += 1;
        blk
    }

    /// Emit a StackAddr instruction for a stack slot and return the pointer Value.
    fn emit_stack_addr(&mut self, slot: u32, instructions: &mut Vec<Instruction>) -> Value {
        let ptr = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::StackAddr { slot },
            args: vec![],
            results: vec![ptr],
        });
        ptr
    }

    /// Resolve an Operand to a LIR Value, emitting Iconst/Fconst as needed.
    fn resolve_operand(
        &mut self,
        op: &Operand,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.resolve_place(place, instructions),
            Operand::Constant(cv) => self.emit_const(cv, instructions),
            Operand::Symbolic(formula) => self.resolve_symbolic_operand(formula, instructions),
            _ => Err(BridgeError::UnsupportedOp("unknown operand variant".to_string())),
        }
    }

    /// Resolve a widthless integer at the chosen operation type; explicit
    /// operand types remain untouched. Preserve upper-half u64 bit patterns.
    fn resolve_integer_operand(
        &mut self,
        op: &Operand,
        ty: Option<Ty>,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if let (Operand::Constant(ConstValue::Int(value)), Some(Ty::Int { width, signed })) =
            (op, ty)
        {
            if matches!(width, 8 | 16 | 32 | 64) {
                let (minimum, maximum) = if signed {
                    let bound = 1_i128 << (width - 1);
                    (-bound, bound - 1)
                } else {
                    (0, (1_i128 << width) - 1)
                };
                if !(minimum..=maximum).contains(value) {
                    return Err(BridgeError::InvalidMir(format!(
                        "integer constant {value} does not fit operand type width {width}, signed {signed}"
                    )));
                }
                let result = self.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: lir_int_type(width), imm: *value as i64 },
                    args: vec![],
                    results: vec![result],
                });
                return Ok(result);
            }
        }
        self.resolve_operand(op, instructions)
    }

    /// Same-width arithmetic takes the declared destination type. Shifts keep
    /// the count's independent type; comparisons/other operations use the peer.
    fn resolve_binop_operands(
        &mut self,
        op: BinOp,
        lhs: &Operand,
        rhs: &Operand,
        value_ty: &Ty,
        instructions: &mut Vec<Instruction>,
    ) -> Result<(Value, Value), BridgeError> {
        let (lhs_ty, rhs_ty) = if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
            (Some(value_ty.clone()), Some(value_ty.clone()))
        } else if matches!(op, BinOp::Shl | BinOp::Shr)
            && matches!(value_ty, Ty::Int { width: 8 | 16 | 32 | 64, .. })
        {
            (Some(value_ty.clone()), None)
        } else {
            (direct_operand_ty(self, rhs)?, direct_operand_ty(self, lhs)?)
        };
        Ok((
            self.resolve_integer_operand(lhs, lhs_ty, instructions)?,
            self.resolve_integer_operand(rhs, rhs_ty, instructions)?,
        ))
    }

    /// Resolve a Place to a LIR Value.
    ///
    /// A direct local is read by `read_local` (loaded from its slot when it is memory-backed).
    /// A projected place walks from the base — a tuple/ADT/array base from its slot, any other
    /// base (a pointer) from its CURRENT value — and loads the final value. A step that reaches
    /// a tuple/ADT/array (a field, element or pointee) keeps its ADDRESS instead of loading it,
    /// so a nested place (`(s.e as B).0`, `(*p).1`) reads to any depth; a place whose final
    /// type is one of those is read as a snapshot of its bytes (`emit_load_value`), like a
    /// whole-local read.
    fn resolve_place(
        &mut self,
        place: &Place,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if place_is_direct_local(place) {
            return self.read_local(place.local, instructions);
        }

        // Start with the base local's address. If it's an aggregate with a
        // stack slot, use StackAddr; otherwise treat the local value as a pointer.
        // Track the current type through projections so we know field types.
        let base_ty = self.local_ty(place.local)?.clone();
        let mut current_val = if is_addressable_local_ty(&base_ty) {
            self.materialize_local_stack_addr(place.local, instructions)?
        } else {
            self.read_local(place.local, instructions)?
        };
        let mut current_ty = base_ty;
        let mut current_is_addr = is_addressable_local_ty(&current_ty);
        // Trust (ticket 216 cg-bridge): the variant a `Downcast` names, live for
        // the one `Field` after it — `(e as V).k` reads variant V's lane.
        let mut active_variant: Option<usize> = None;

        for proj in &place.projections {
            let downcast = active_variant.take();
            check_downcast_followed_by_field(&current_ty, downcast, proj)?;
            match proj {
                Projection::Field(field_idx) => {
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Field projection requires addressable aggregate base: {current_ty:?}"
                        )));
                    }
                    let (flat_index, field_ty) =
                        projected_field(&current_ty, downcast, *field_idx, "field read")?;
                    let lir_struct_ty = map_type(&current_ty)?;
                    let field_addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: lir_struct_ty,
                            field_index: flat_index as u32,
                        },
                        args: vec![current_val],
                        results: vec![field_addr],
                    });
                    (current_val, current_is_addr) =
                        self.load_unless_aggregate(field_addr, &field_ty, map_type, instructions)?;
                    current_ty = field_ty;
                }
                Projection::Deref => {
                    // Dereferencing a slice fat pointer preserves the data and
                    // metadata lanes; it does not load an unsized `[T]` value.
                    let pointee_ty = deref_type(&current_ty)?;
                    if matches!(pointee_ty, Ty::Slice { .. }) {
                        current_ty = pointee_ty;
                        current_is_addr = false;
                        continue;
                    }
                    (current_val, current_is_addr) = self.load_unless_aggregate(
                        current_val,
                        &pointee_ty,
                        map_lowering_type,
                        instructions,
                    )?;
                    current_ty = pointee_ty;
                }
                Projection::Index(idx_local) => {
                    let idx_val = self.read_local(*idx_local, instructions)?;
                    let elem_ty = element_type(&current_ty).or_else(|_| {
                        slice_element_type(&current_ty).ok_or_else(|| {
                            BridgeError::UnsupportedOp(format!(
                                "Index projection on non-sequence type: {current_ty:?}"
                            ))
                        })
                    })?;
                    let addr = if slice_element_type(&current_ty).is_some() {
                        self.emit_slice_index_addr(current_val, &current_ty, idx_val, instructions)?
                    } else {
                        if !current_is_addr {
                            return Err(BridgeError::UnsupportedOp(format!(
                                "Index projection requires addressable array/slice base: {current_ty:?}"
                            )));
                        }
                        self.emit_ptr_offset(current_val, &elem_ty, idx_val, instructions)?
                    };
                    (current_val, current_is_addr) =
                        self.load_unless_aggregate(addr, &elem_ty, map_type, instructions)?;
                    current_ty = elem_ty;
                }
                Projection::Downcast(variant_idx) => {
                    // Downcast: select a variant of an enum. The data pointer is
                    // the same and no instruction is emitted, but the variant is
                    // NOT type-only: it picks the lane the next `Field` reads
                    // (`projected_field`).
                    current_ty = downcast_type(&current_ty, *variant_idx)?;
                    active_variant = Some(*variant_idx);
                }
                Projection::ConstantIndex { offset, min_length, from_end } => {
                    if let Some(elem_ty) = slice_element_type(&current_ty) {
                        let index = if *from_end {
                            let len =
                                self.emit_slice_metadata(current_val, &current_ty, instructions)?;
                            let offset_value = self.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Iconst { ty: LirType::I64, imm: *offset as i64 },
                                args: vec![],
                                results: vec![offset_value],
                            });
                            let index = self.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Isub,
                                args: vec![len, offset_value],
                                results: vec![index],
                            });
                            index
                        } else {
                            let index = self.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Iconst { ty: LirType::I64, imm: *offset as i64 },
                                args: vec![],
                                results: vec![index],
                            });
                            index
                        };
                        let addr = self.emit_slice_index_addr(
                            current_val,
                            &current_ty,
                            index,
                            instructions,
                        )?;
                        (current_val, current_is_addr) =
                            self.load_unless_aggregate(addr, &elem_ty, map_type, instructions)?;
                        current_ty = elem_ty;
                        continue;
                    }
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "ConstantIndex projection requires addressable array/slice base: {current_ty:?}"
                        )));
                    }
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();

                    // Trust: #828 — support ConstantIndex from_end for fixed-size arrays.
                    let element_offset = match &current_ty {
                        Ty::Array { len, .. } => {
                            if *len < *min_length as u64 {
                                return Err(BridgeError::UnsupportedOp(format!(
                                    "ConstantIndex min_length {min_length} exceeds array length {len}"
                                )));
                            }
                            if *from_end {
                                len.checked_sub(*offset as u64).ok_or_else(|| {
                                    BridgeError::UnsupportedOp(format!(
                                        "ConstantIndex from_end offset {offset} exceeds array length {len}"
                                    ))
                                })?
                            } else {
                                *offset as u64
                            }
                        }
                        _ if *from_end => {
                            return Err(BridgeError::UnsupportedOp(
                                "ConstantIndex from_end not yet supported".to_string(),
                            ));
                        }
                        _ => *offset as u64,
                    };
                    let byte_offset = (element_offset as u32) * elem_size;
                    let offset_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(byte_offset) },
                        args: vec![],
                        results: vec![offset_const],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset_const],
                        results: vec![addr],
                    });
                    (current_val, current_is_addr) =
                        self.load_unless_aggregate(addr, &elem_ty, map_type, instructions)?;
                    current_ty = elem_ty;
                }
                Projection::Subslice { from, to, from_end } => {
                    let result_ty = subslice_result_type(&current_ty, *from, *to, *from_end)?;
                    if current_is_addr && matches!(current_ty, Ty::Array { .. }) {
                        // A sub-array is an aggregate: the walk keeps its address.
                        current_val = self.emit_array_subslice_addr(
                            current_val,
                            &current_ty,
                            *from,
                            *to,
                            *from_end,
                            instructions,
                        )?;
                        current_is_addr = true;
                    } else if slice_element_type(&current_ty).is_some() {
                        current_val = self.emit_slice_subslice_value(
                            current_val,
                            &current_ty,
                            *from,
                            *to,
                            *from_end,
                            instructions,
                        )?;
                        current_is_addr = false;
                    } else {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Subslice projection requires array address or slice fat pointer base: {current_ty:?}"
                        )));
                    }
                    current_ty = result_ty;
                }
                Projection::OpaqueCast(ty) | Projection::UnwrapUnsafeBinder(ty) => {
                    current_ty = ty.clone();
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "unsupported projection: {other:?}"
                    )));
                }
            }
        }
        // A walk that ends at a tuple/ADT/array holds its ADDRESS; the value read is a snapshot
        // of its bytes, as a whole-local read is (`read_local`), so a later write to the place
        // cannot change a value already read.
        if current_is_addr {
            current_val =
                self.emit_load_value(map_lowering_type(&current_ty)?, current_val, instructions);
        }
        Ok(current_val)
    }

    /// The value at `addr` of type `ty` for a read walk: a tuple/ADT/array stays at its
    /// address (`(addr, true)`, so the walk can continue into it), anything else is loaded at
    /// the LIR type `lir` gives it (`(value, false)`; a slice fat pointer is a snapshot of its
    /// two words, `emit_load_value`).
    fn load_unless_aggregate(
        &mut self,
        addr: Value,
        ty: &Ty,
        lir: fn(&Ty) -> Result<LirType, BridgeError>,
        instructions: &mut Vec<Instruction>,
    ) -> Result<(Value, bool), BridgeError> {
        if is_addressable_local_ty(ty) {
            return Ok((addr, true));
        }
        Ok((self.emit_load_value(lir(ty)?, addr, instructions), false))
    }

    /// Resolve a Place to a pointer Value (address) rather than loading.
    ///
    /// Used by Ref and AddressOf rvalues that need the address of a place.
    fn resolve_place_addr(
        &mut self,
        place: &Place,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let base_ty = self.local_ty(place.local)?.clone();
        let (mut current_val, mut current_ty, mut current_is_addr, projections) =
            if place_addr_starts_at_pointer_value(place, &base_ty) {
                // `*p…`: start from the pointer's value, exactly what the leading `Deref` below
                // would load back out of `p`'s slot (the data pointer, or the whole slice fat
                // pointer), without giving `p` a slot.
                let pointer = self.read_local(place.local, instructions)?;
                let pointee_ty = deref_type(&base_ty)?;
                let pointee_is_addr = !matches!(pointee_ty, Ty::Slice { .. });
                (pointer, pointee_ty, pointee_is_addr, &place.projections[1..])
            } else {
                let base_addr = self.materialize_local_stack_addr(place.local, instructions)?;
                if place.projections.is_empty() {
                    return Ok(base_addr);
                }
                (base_addr, base_ty, true, &place.projections[..])
            };

        // Trust (ticket 216 cg-bridge): as in `resolve_place` — a write to
        // `(e as V).k` lands in the lane a read of it reads.
        let mut active_variant: Option<usize> = None;

        for proj in projections {
            let downcast = active_variant.take();
            check_downcast_followed_by_field(&current_ty, downcast, proj)?;
            match proj {
                Projection::Field(field_idx) => {
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Field address projection requires addressable aggregate base: {current_ty:?}"
                        )));
                    }
                    let (flat_index, field_ty) =
                        projected_field(&current_ty, downcast, *field_idx, "field address")?;
                    let lir_struct_ty = map_type(&current_ty)?;
                    let result = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: lir_struct_ty,
                            field_index: flat_index as u32,
                        },
                        args: vec![current_val],
                        results: vec![result],
                    });
                    current_val = result;
                    current_ty = field_ty;
                }
                Projection::Deref => {
                    // Load the pointer, then the result is the address. Slice
                    // fat pointers load the full `(data, len)` value instead.
                    let pointee_ty = deref_type(&current_ty)?;
                    if matches!(pointee_ty, Ty::Slice { .. }) {
                        let fat_ty = slice_fat_pointer_lir_ty(&current_ty)?;
                        current_val = self.emit_load_value(fat_ty, current_val, instructions);
                        current_ty = pointee_ty;
                        current_is_addr = false;
                        continue;
                    }

                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: LirType::I64, align: None },
                        args: vec![current_val],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = pointee_ty;
                    current_is_addr = true;
                }
                Projection::Index(idx_local) => {
                    if slice_element_type(&current_ty).is_some() {
                        let idx_val = self.read_local(*idx_local, instructions)?;
                        if current_is_addr {
                            current_val = materialize_aggregate_value(
                                self,
                                current_val,
                                &slice_fat_pointer_lir_ty(&current_ty)?,
                                instructions,
                            );
                        }
                        current_val = self.emit_slice_index_addr(
                            current_val,
                            &current_ty,
                            idx_val,
                            instructions,
                        )?;
                        current_ty = slice_element_type(&current_ty).expect("checked above");
                        current_is_addr = true;
                        continue;
                    }
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Index address projection requires addressable array/slice base: {current_ty:?}"
                        )));
                    }
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();

                    let idx_val = self.read_local(*idx_local, instructions)?;
                    let size_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(elem_size) },
                        args: vec![],
                        results: vec![size_const],
                    });
                    let offset = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Imul,
                        args: vec![idx_val, size_const],
                        results: vec![offset],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset],
                        results: vec![addr],
                    });
                    current_val = addr;
                    current_ty = elem_ty;
                    current_is_addr = true;
                }
                Projection::Downcast(variant_idx) => {
                    current_ty = downcast_type(&current_ty, *variant_idx)?;
                    active_variant = Some(*variant_idx);
                }
                // Trust: #828 — support ConstantIndex in address-of lowering too.
                Projection::ConstantIndex { offset, min_length, from_end } => {
                    if slice_element_type(&current_ty).is_some() {
                        if current_is_addr {
                            current_val = materialize_aggregate_value(
                                self,
                                current_val,
                                &slice_fat_pointer_lir_ty(&current_ty)?,
                                instructions,
                            );
                        }
                        let index = if *from_end {
                            let len =
                                self.emit_slice_metadata(current_val, &current_ty, instructions)?;
                            let offset_value = self.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Iconst { ty: LirType::I64, imm: *offset as i64 },
                                args: vec![],
                                results: vec![offset_value],
                            });
                            let index = self.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Isub,
                                args: vec![len, offset_value],
                                results: vec![index],
                            });
                            index
                        } else {
                            let index = self.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Iconst { ty: LirType::I64, imm: *offset as i64 },
                                args: vec![],
                                results: vec![index],
                            });
                            index
                        };
                        current_val = self.emit_slice_index_addr(
                            current_val,
                            &current_ty,
                            index,
                            instructions,
                        )?;
                        current_ty = slice_element_type(&current_ty).expect("checked above");
                        current_is_addr = true;
                        continue;
                    }
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "ConstantIndex address projection requires addressable array/slice base: {current_ty:?}"
                        )));
                    }
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();
                    let element_offset = match &current_ty {
                        Ty::Array { len, .. } => {
                            if *len < *min_length as u64 {
                                return Err(BridgeError::UnsupportedOp(format!(
                                    "ConstantIndex min_length {min_length} exceeds array length {len}"
                                )));
                            }
                            if *from_end {
                                len.checked_sub(*offset as u64).ok_or_else(|| {
                                    BridgeError::UnsupportedOp(format!(
                                        "ConstantIndex from_end offset {offset} exceeds array length {len}"
                                    ))
                                })?
                            } else {
                                *offset as u64
                            }
                        }
                        _ if *from_end => {
                            return Err(BridgeError::UnsupportedOp(
                                "ConstantIndex from_end on non-array in addr context".to_string(),
                            ));
                        }
                        _ => *offset as u64,
                    };
                    let actual_offset = (element_offset as u32) * elem_size;
                    let offset_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(actual_offset) },
                        args: vec![],
                        results: vec![offset_const],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset_const],
                        results: vec![addr],
                    });
                    current_val = addr;
                    current_ty = elem_ty;
                    current_is_addr = true;
                }
                Projection::Subslice { from, to, from_end } => {
                    let result_ty = subslice_result_type(&current_ty, *from, *to, *from_end)?;
                    current_val = if current_is_addr && matches!(current_ty, Ty::Array { .. }) {
                        self.emit_array_subslice_addr(
                            current_val,
                            &current_ty,
                            *from,
                            *to,
                            *from_end,
                            instructions,
                        )?
                    } else if slice_element_type(&current_ty).is_some() {
                        if current_is_addr {
                            current_val = materialize_aggregate_value(
                                self,
                                current_val,
                                &slice_fat_pointer_lir_ty(&current_ty)?,
                                instructions,
                            );
                        }
                        self.emit_slice_subslice_value(
                            current_val,
                            &current_ty,
                            *from,
                            *to,
                            *from_end,
                            instructions,
                        )?
                    } else {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Subslice address projection requires array address or slice fat pointer base: {current_ty:?}"
                        )));
                    };
                    current_ty = result_ty;
                    current_is_addr = matches!(current_ty, Ty::Array { .. });
                }
                Projection::OpaqueCast(ty) | Projection::UnwrapUnsafeBinder(ty) => {
                    current_ty = ty.clone();
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "address-of projection not supported: {other:?}"
                    )));
                }
            }
        }
        Ok(current_val)
    }

    /// Emit an Iconst or Fconst instruction and return its result Value.
    fn emit_const(
        &mut self,
        cv: &ConstValue,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let (opcode, result) = match cv {
            ConstValue::Bool(b) => {
                let v = self.fresh_value();
                let opcode = Opcode::Iconst { ty: LirType::B1, imm: i64::from(*b) };
                (opcode, v)
            }
            ConstValue::Int(val) => {
                let v = self.fresh_value();
                let imm = i64::try_from(*val).map_err(|_| {
                    BridgeError::UnsupportedOp(format!(
                        "signed integer constant {val} exceeds the exact 64-bit Iconst domain"
                    ))
                })?;
                // Trust: #826 — infer the narrowest signed LIR type from value range.
                let ty = match *val {
                    -128..=127 => LirType::I8,
                    -32_768..=32_767 => LirType::I16,
                    -2_147_483_648..=2_147_483_647 => LirType::I32,
                    _ => LirType::I64,
                };
                let opcode = Opcode::Iconst { ty, imm };
                (opcode, v)
            }
            ConstValue::Uint(val, width) => {
                let v = self.fresh_value();
                let ty = match width {
                    8 => LirType::I8,
                    16 => LirType::I16,
                    32 => LirType::I32,
                    64 => LirType::I64,
                    128 => {
                        return Err(BridgeError::UnsupportedOp(
                            "u128 constants cannot be represented by LIR's signed 64-bit Iconst immediate"
                                .to_string(),
                        ));
                    }
                    _ => return Err(BridgeError::UnsupportedType(format!("u{width}"))),
                };
                let max = (1_u128 << *width) - 1;
                if *val > max {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "unsigned integer constant {val} does not fit declared width {width}"
                    )));
                }
                // For u64 values above i64::MAX the signed immediate retains
                // exactly the same 64-bit two's-complement bit pattern.
                let opcode = Opcode::Iconst { ty, imm: (*val as u64) as i64 };
                (opcode, v)
            }
            ConstValue::Float(val) => {
                let v = self.fresh_value();
                let opcode = Opcode::Fconst { ty: LirType::F64, imm: *val };
                (opcode, v)
            }
            ConstValue::Unit | ConstValue::CallableItem { .. } => {
                return Err(BridgeError::UnsupportedOp(
                    "unit-like constants have no value-level LIR representation".to_string(),
                ));
            }
            _ => {
                return Err(BridgeError::UnsupportedOp("unknown constant variant".to_string()));
            }
        };
        instructions.push(Instruction { opcode, args: vec![], results: vec![result] });
        Ok(result)
    }

    fn emit_slice_field_load(
        &mut self,
        fat_ptr: Value,
        source_ty: &Ty,
        field_index: u32,
        field_ty: LirType,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let fat_ty = slice_fat_pointer_lir_ty(source_ty)?;
        // A fat pointer is a two-lane aggregate, and an aggregate value IS the address of its
        // bytes (`emit_store_value`), so the lane is read straight through `fat_ptr`.
        let field_addr = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::StructGep { struct_ty: fat_ty, field_index },
            args: vec![fat_ptr],
            results: vec![field_addr],
        });
        let loaded = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Load { ty: field_ty, align: None },
            args: vec![field_addr],
            results: vec![loaded],
        });
        Ok(loaded)
    }

    fn emit_slice_data_ptr(
        &mut self,
        fat_ptr: Value,
        source_ty: &Ty,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        self.emit_slice_field_load(fat_ptr, source_ty, 0, LirType::I64, instructions)
    }

    fn emit_slice_metadata(
        &mut self,
        fat_ptr: Value,
        source_ty: &Ty,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        self.emit_slice_field_load(fat_ptr, source_ty, 1, LirType::I64, instructions)
    }

    fn emit_ptr_offset(
        &mut self,
        base_ptr: Value,
        elem_ty: &Ty,
        index: Value,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let lir_elem = map_type(elem_ty)?;
        let elem_size = lir_elem.bytes();
        let size_const = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(elem_size) },
            args: vec![],
            results: vec![size_const],
        });
        let offset = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Imul,
            args: vec![index, size_const],
            results: vec![offset],
        });
        let addr = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Iadd,
            args: vec![base_ptr, offset],
            results: vec![addr],
        });
        Ok(addr)
    }

    fn emit_const_ptr_offset(
        &mut self,
        base_ptr: Value,
        elem_ty: &Ty,
        index: u64,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let lir_elem = map_type(elem_ty)?;
        let byte_offset = (index as u32) * lir_elem.bytes();
        let offset_const = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(byte_offset) },
            args: vec![],
            results: vec![offset_const],
        });
        let addr = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Iadd,
            args: vec![base_ptr, offset_const],
            results: vec![addr],
        });
        Ok(addr)
    }

    fn emit_slice_index_addr(
        &mut self,
        fat_ptr: Value,
        source_ty: &Ty,
        index: Value,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let elem_ty = slice_element_type(source_ty).ok_or_else(|| {
            BridgeError::UnsupportedOp(format!(
                "slice index projection on non-slice fat pointer type {source_ty:?}"
            ))
        })?;
        let data_ptr = self.emit_slice_data_ptr(fat_ptr, source_ty, instructions)?;
        self.emit_ptr_offset(data_ptr, &elem_ty, index, instructions)
    }

    fn emit_slice_fat_pointer(
        &mut self,
        elem_ty: &Ty,
        data_ptr: Value,
        len: Value,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let fat_ty = slice_fat_pointer_lir_ty_for_elem(elem_ty)?;
        let slot = self.alloc_stack_slot(&fat_ty);
        let slice_addr = self.emit_stack_addr(slot, instructions);

        let ptr_field = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::StructGep { struct_ty: fat_ty.clone(), field_index: 0 },
            args: vec![slice_addr],
            results: vec![ptr_field],
        });
        push_store(instructions, LirType::I64, data_ptr, ptr_field);

        let len_field = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::StructGep { struct_ty: fat_ty.clone(), field_index: 1 },
            args: vec![slice_addr],
            results: vec![len_field],
        });
        push_store(instructions, LirType::I64, len, len_field);

        // The fat pointer's value is the address of the fresh slot it was just built in.
        self.aggregate_carriers.insert(slice_addr);
        Ok(slice_addr)
    }

    fn emit_array_subslice_addr(
        &mut self,
        base_addr: Value,
        source_ty: &Ty,
        from: usize,
        to: usize,
        from_end: bool,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let Ty::Array { elem, len } = source_ty else {
            return Err(BridgeError::UnsupportedOp(format!(
                "Subslice address projection on non-array type: {source_ty:?}"
            )));
        };

        let start = from as u64;
        let end = if from_end {
            len.checked_sub(to as u64).ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "Subslice from_end offset {to} exceeds array length {len}"
                ))
            })?
        } else {
            to as u64
        };
        if start > end || end > *len {
            return Err(BridgeError::UnsupportedOp(format!(
                "Subslice range {from}..{} exceeds array length {len}",
                if from_end { format!("-{to}") } else { to.to_string() }
            )));
        }

        let elem_ty = (**elem).clone();
        self.emit_const_ptr_offset(base_addr, &elem_ty, start, instructions)
    }

    fn emit_slice_subslice_value(
        &mut self,
        fat_ptr: Value,
        source_ty: &Ty,
        from: usize,
        to: usize,
        from_end: bool,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let elem_ty = slice_element_type(source_ty).ok_or_else(|| {
            BridgeError::UnsupportedOp(format!(
                "Subslice projection on non-slice fat pointer type {source_ty:?}"
            ))
        })?;
        if !from_end && to < from {
            return Err(BridgeError::UnsupportedOp(format!(
                "Subslice range {from}..{to} is inverted"
            )));
        }

        let data_ptr = self.emit_slice_data_ptr(fat_ptr, source_ty, instructions)?;
        let start = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Iconst { ty: LirType::I64, imm: from as i64 },
            args: vec![],
            results: vec![start],
        });
        let start_ptr = self.emit_ptr_offset(data_ptr, &elem_ty, start, instructions)?;

        let new_len = if from_end {
            let base_len = self.emit_slice_metadata(fat_ptr, source_ty, instructions)?;
            let trim = from.checked_add(to).ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "Subslice trim from {from} plus to {to} overflows usize"
                ))
            })?;
            let trim_value = self.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::Iconst { ty: LirType::I64, imm: trim as i64 },
                args: vec![],
                results: vec![trim_value],
            });
            let result = self.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::Isub,
                args: vec![base_len, trim_value],
                results: vec![result],
            });
            result
        } else {
            let len_value = self.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::Iconst { ty: LirType::I64, imm: (to - from) as i64 },
                args: vec![],
                results: vec![len_value],
            });
            len_value
        };

        self.emit_slice_fat_pointer(&elem_ty, start_ptr, new_len, instructions)
    }

    /// Materialize a symbolic operand only when it is already an exactly
    /// representable ground machine constant.
    ///
    /// Variables and compound formulas need a target-semantic implementation;
    /// replacing them with an arbitrary integer would turn proof IR into different
    /// executable semantics. Unsupported formulas therefore fail closed.
    fn emit_ground_symbolic_constant(
        &mut self,
        formula: &Formula,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let result = self.fresh_value();
        let (ty, imm) = ground_symbolic_formula_lir_const(formula)?;
        instructions.push(Instruction {
            opcode: Opcode::Iconst { ty, imm },
            args: vec![],
            results: vec![result],
        });
        Ok(result)
    }

    /// Lower a symbolic operand: first the entry-register-binding shapes
    /// (each use justified by the per-block write-freedom certificate), then
    /// exact ground constants; everything else refuses, with the refusal
    /// carrying the closest missing justification instead of a bare
    /// "unsupported".
    fn resolve_symbolic_operand(
        &mut self,
        formula: &Formula,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if let Some(value) = self.try_entry_binding_lowering(formula, instructions) {
            return Ok(value);
        }
        self.emit_ground_symbolic_constant(formula, instructions)
            .map_err(|err| self.enrich_symbolic_refusal(formula, err))
    }

    /// The two entry-binding shapes: a bare bound register `Var`, and the
    /// exact 8-byte little-endian load over the machine memory seed rooted at
    /// a bound register (optionally plus a constant displacement). Returns
    /// `None` — falling through to the fail-closed refusal — on ANY missing
    /// justification; nothing here substitutes a value.
    fn try_entry_binding_lowering(
        &mut self,
        formula: &Formula,
        instructions: &mut Vec<Instruction>,
    ) -> Option<Value> {
        use crate::entry_binding::{recognize_bare_reg_var, recognize_le_load};

        // No consumption from terminator position: the records are keyed by
        // statement index, which a terminator operand does not have, and no
        // evidence row exists to mark — falling through to the refusal keeps
        // the latent bare-Var-discriminant path fail-closed.
        if self.in_terminator {
            return None;
        }
        let entry = self.entry_bindings.as_ref()?;

        if let Some(name) = recognize_bare_reg_var(formula) {
            let &(param_index, value) = entry.params_by_var.get(name)?;
            if !entry.preservation.is_preserved(self.current_block, param_index) {
                return None;
            }
            let param = &entry.bindings.params[param_index];
            self.record_symbolic_consumption(
                formula,
                format!(
                    "bare {var} lowered to LIR param {param_index} ({reg} at function entry); \
                     justified: {reg} proven write-free on every entry\u{2192}block-{block} path \
                     (Assign-derived kill sets over the lifted body); candidacy from the \
                     entry-block read-before-write observation",
                    var = param.var_name,
                    reg = param.reg_name,
                    block = self.current_block,
                ),
            );
            return Some(value);
        }

        if let Some(root) = recognize_le_load(formula) {
            let &(param_index, base_value) = entry.params_by_var.get(&root.base_var)?;
            if !entry.preservation.is_preserved(self.current_block, param_index) {
                return None;
            }
            let param_reg = entry.bindings.params[param_index].reg_name.clone();
            let param_var = entry.bindings.params[param_index].var_name.clone();
            let address = match root.displacement {
                None => base_value,
                Some(displacement) => {
                    let imm = i64::try_from(displacement).ok()?;
                    let displacement_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm },
                        args: vec![],
                        results: vec![displacement_const],
                    });
                    let address = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![base_value, displacement_const],
                        results: vec![address],
                    });
                    address
                }
            };
            let loaded = self.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::Load { ty: LirType::I64, align: None },
                args: vec![address],
                results: vec![loaded],
            });
            self.record_symbolic_consumption(
                formula,
                format!(
                    "8-byte little-endian load lowered to Opcode::Load{{ty: I64}} at address \
                     LIR param {param_index} ({reg} at function entry){disp}; justified: {reg} \
                     ({var}) proven write-free on every entry\u{2192}block-{block} path \
                     (Assign-derived kill sets over the lifted body); candidacy from the \
                     entry-block read-before-write observation",
                    reg = param_reg,
                    var = param_var,
                    block = self.current_block,
                    disp = match root.displacement {
                        Some(d) => format!(" + {d}"),
                        None => String::new(),
                    },
                ),
            );
            return Some(loaded);
        }

        None
    }

    fn record_symbolic_consumption(&mut self, formula: &Formula, detail: String) {
        self.consumed_symbolic.push(crate::entry_binding::ConsumedSymbolicLowering {
            block: self.current_block,
            statement_index: self.current_statement,
            formula: formula.clone(),
            detail,
        });
    }

    /// Attach the closest missing justification to a symbolic-operand
    /// refusal, so the error names the fix (and its options) instead of only
    /// the fact of refusal. Never changes WHETHER lowering refuses.
    fn enrich_symbolic_refusal(&self, formula: &Formula, err: BridgeError) -> BridgeError {
        use crate::entry_binding::{recognize_bare_reg_var, recognize_le_load};

        let BridgeError::UnsupportedOp(message) = err else {
            return err;
        };
        let mut message = message;

        if let Some(reason) = &self.entry_binding_refusal {
            message.push_str(&format!(
                "; entry-register bindings were supplied but refused for this body: {reason}"
            ));
        } else if let Some(entry) = &self.entry_bindings {
            let base_var = recognize_le_load(formula)
                .map(|root| root.base_var)
                .or_else(|| recognize_bare_reg_var(formula).map(str::to_string));
            match base_var {
                Some(var) => match entry.params_by_var.get(&var) {
                    Some(&(param_index, _)) => {
                        let param = &entry.bindings.params[param_index];
                        let kills = entry.preservation.kill_sites(param_index);
                        if kills.is_empty() {
                            message.push_str(&format!(
                                "; the shape is modeled but {reg} ({var})'s function-entry \
                                 binding is not established at block {block} (no concrete kill \
                                 located: the block is unreachable from entry or a structural \
                                 gate voided the certificate)",
                                reg = param.reg_name,
                                block = self.current_block,
                            ));
                        } else {
                            let sites = kills
                                .iter()
                                .map(|(block, stmt)| format!("block {block} statement {stmt}"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            message.push_str(&format!(
                                "; the shape is modeled but {reg} ({var}) is assigned at {sites}, \
                                 so its function-entry value is not what reaches block {block} on \
                                 every path; only a use whose block the write-freedom certificate \
                                 covers can bind",
                                reg = param.reg_name,
                                block = self.current_block,
                            ));
                        }
                    }
                    None => {
                        let candidates = entry
                            .bindings
                            .params
                            .iter()
                            .map(|param| format!("{} ({})", param.reg_name, param.var_name))
                            .collect::<Vec<_>>()
                            .join(", ");
                        message.push_str(&format!(
                            "; the shape is modeled but its base register {var} is outside the \
                             bound ABI argument-register prefix [{candidates}]; a non-argument \
                             base needs its own justified binding before it can lower"
                        ));
                    }
                },
                None => {
                    message.push_str(
                        "; the modeled target-semantic shapes are: a bare bound 64-bit register \
                         Var, and the 8-byte little-endian load over the machine memory seed \
                         rooted at a bound register (optionally plus a constant displacement); \
                         extending the recognizer requires extending its mutation battery in the \
                         same change",
                    );
                }
            }
        }

        BridgeError::UnsupportedOp(message)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReturnLowering {
    Value,
    NoValue,
}

fn return_lowering_for(body: &VerifiableBody) -> ReturnLowering {
    if !matches!(body.return_ty, Ty::Unit | Ty::Never) {
        return ReturnLowering::Value;
    }

    ReturnLowering::NoValue
}

fn return_args(
    ctx: &mut LoweringCtx<'_>,
    return_lowering: ReturnLowering,
    instructions: &mut Vec<Instruction>,
) -> Result<Vec<Value>, BridgeError> {
    match return_lowering {
        // A memory-backed return place is loaded from its slot (it may have been written
        // through `&mut _0` or a field store). An aggregate return place is returned as its
        // slot's address, with no snapshot: `Return` reads the bytes through it at once, and
        // nothing can write the slot in between.
        ReturnLowering::Value => {
            if ctx.is_memory_backed(0) && map_lowering_type(ctx.local_ty(0)?)?.is_aggregate() {
                return Ok(vec![ctx.materialize_local_stack_addr(0, instructions)?]);
            }
            Ok(vec![ctx.read_local(0, instructions)?])
        }
        ReturnLowering::NoValue => Ok(vec![]),
    }
}

fn abort_call_instruction() -> Instruction {
    Instruction {
        opcode: Opcode::Call {
            name: ABORT_SYMBOL.to_string(),
            binding: DirectCallBinding::Interposable,
        },
        args: vec![],
        results: vec![],
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

pub(crate) fn trust_location_file_global_name(file: &str) -> String {
    format!("{TRUST_LOCATION_FILE_GLOBAL_PREFIX}{}", hex_encode(file.as_bytes()))
}

pub(crate) fn trust_location_file_global_data(name: &str) -> Option<Vec<u8>> {
    let hex = name.strip_prefix(TRUST_LOCATION_FILE_GLOBAL_PREFIX)?;
    if hex.len() % 2 != 0 {
        return None;
    }

    let mut bytes = Vec::with_capacity(hex.len() / 2 + 1);
    for pair in hex.as_bytes().chunks_exact(2) {
        let hi = hex_value(pair[0])?;
        let lo = hex_value(pair[1])?;
        bytes.push((hi << 4) | lo);
    }
    bytes.push(0);
    Some(bytes)
}

fn emit_struct_field_store(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    base_ptr: Value,
    struct_ty: &LirType,
    field_index: u32,
    field_ty: LirType,
    value: Value,
) {
    let field_ptr = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::StructGep { struct_ty: struct_ty.clone(), field_index },
        args: vec![base_ptr],
        results: vec![field_ptr],
    });
    push_store(instructions, field_ty, value, field_ptr);
}

fn emit_panic_location(
    ctx: &mut LoweringCtx<'_>,
    span: &SourceSpan,
    instructions: &mut Vec<Instruction>,
) -> Value {
    let location_ty = LirType::Struct(vec![LirType::I64, LirType::I64, LirType::I32, LirType::I32]);
    let location_slot = ctx.alloc_stack_slot(&location_ty);
    let location_ptr = ctx.emit_stack_addr(location_slot, instructions);

    let file_ptr = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::GlobalRef { name: trust_location_file_global_name(&span.file) },
        args: vec![],
        results: vec![file_ptr],
    });
    emit_struct_field_store(
        ctx,
        instructions,
        location_ptr,
        &location_ty,
        0,
        LirType::I64,
        file_ptr,
    );

    let file_len = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty: LirType::I64, imm: span.file.len() as i64 },
        args: vec![],
        results: vec![file_len],
    });
    emit_struct_field_store(
        ctx,
        instructions,
        location_ptr,
        &location_ty,
        1,
        LirType::I64,
        file_len,
    );

    let line = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty: LirType::I32, imm: i64::from(span.line_start) },
        args: vec![],
        results: vec![line],
    });
    emit_struct_field_store(ctx, instructions, location_ptr, &location_ty, 2, LirType::I32, line);

    let col = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty: LirType::I32, imm: i64::from(span.col_start) },
        args: vec![],
        results: vec![col],
    });
    emit_struct_field_store(ctx, instructions, location_ptr, &location_ty, 3, LirType::I32, col);

    location_ptr
}

fn panic_block_instructions(
    ctx: &mut LoweringCtx<'_>,
    action: &PanicBlockAction,
) -> Vec<Instruction> {
    match action {
        PanicBlockAction::Abort => vec![abort_call_instruction()],
        PanicBlockAction::RuntimeCall { symbol, span } => {
            let mut instructions = Vec::new();
            let location = emit_panic_location(ctx, span, &mut instructions);
            instructions.push(Instruction {
                opcode: Opcode::Call {
                    name: symbol.clone(),
                    binding: DirectCallBinding::Interposable,
                },
                args: vec![location],
                results: vec![],
            });
            instructions
        }
    }
}

fn panic_action_for_assert(
    ctx: &LoweringCtx<'_>,
    msg: &AssertMessage,
    span: &SourceSpan,
) -> PanicBlockAction {
    ctx.options
        .panic_symbols
        .symbol_for_assert(msg)
        .map(|symbol| PanicBlockAction::RuntimeCall {
            symbol: symbol.to_string(),
            span: span.clone(),
        })
        .unwrap_or(PanicBlockAction::Abort)
}

fn is_fieldless_adt(ty: &Ty) -> bool {
    matches!(ty, Ty::Adt { fields, .. } if fields.is_empty())
}

fn validate_aggregate_kind_for_lir(kind: &AggregateKind, dest_ty: &Ty) -> Result<(), BridgeError> {
    match kind {
        AggregateKind::Tuple | AggregateKind::Array => Ok(()),
        AggregateKind::Adt { active_field: Some(active_field), .. } => {
            Err(BridgeError::UnsupportedOp(format!(
                "ADT aggregate active_field {active_field} requires union layout semantics"
            )))
        }
        AggregateKind::Adt { .. } if is_fieldless_adt(dest_ty) => Err(BridgeError::UnsupportedOp(
            format!("fieldless ADT aggregate has no trustworthy LIR layout: {dest_ty:?}"),
        )),
        AggregateKind::Adt { .. } => Ok(()),
        other => Err(BridgeError::UnsupportedOp(format!("unsupported aggregate kind: {other:?}"))),
    }
}

fn map_lowering_type(ty: &Ty) -> Result<LirType, BridgeError> {
    if slice_element_type(ty).is_some() { slice_fat_pointer_lir_ty(ty) } else { map_type(ty) }
}

fn push_store(instructions: &mut Vec<Instruction>, ty: LirType, value: Value, ptr: Value) {
    instructions.push(Instruction {
        opcode: Opcode::Store { ty, align: None },
        args: vec![value, ptr],
        results: vec![],
    });
}

/// The byte extent a MIR `Repeat` of `count` elements of `elem_size` bytes fills, checked to be
/// EXACTLY the extent of the stack slot typed `slot_ty` that holds it.
///
/// The slot is sized from `slot_ty.bytes()`, a `u32` that SATURATES; the fill is a `u64` product.
/// If the two ever differ, the fill writes past the slot (or leaves part of it unwritten), so a
/// mismatch is refused as malformed input rather than lowered. [`map_type`] refuses every type
/// whose extent the carrier cannot describe, so for a mapped array type the two agree; this is
/// the fill's own statement of that invariant, at the one place a whole-array write is sized.
pub(crate) fn repeat_fill_extent(
    slot_ty: &LirType,
    elem_size: u64,
    count: u64,
) -> Result<u64, BridgeError> {
    let fill = count.checked_mul(elem_size).ok_or_else(|| {
        BridgeError::UnsupportedType(format!(
            "Repeat of {count} x {elem_size}-byte elements overflows u64"
        ))
    })?;
    match slot_ty.checked_bytes() {
        Some(slot) if slot == fill => Ok(fill),
        slot => Err(BridgeError::InvalidMir(format!(
            "Repeat fills {fill} bytes of a slot whose LIR extent is {slot:?}"
        ))),
    }
}

/// A byte offset or length as the I64 immediate LIR carries it.
fn carrier_imm(bytes: u64) -> Result<i64, BridgeError> {
    i64::try_from(bytes).map_err(|_| {
        BridgeError::UnsupportedType(format!("{bytes} bytes exceed the I64 offset carrier"))
    })
}

/// The one byte every byte of `operand`'s value is, when `operand` is an integer or bool
/// constant of the scalar element type `elem` and its little-endian image (at `elem`'s width)
/// repeats a single byte — so `[operand; N]` is a `Memset` of that byte. `None` for anything
/// else (a place, a float, a wider pattern), which takes the store-and-double fill.
pub(crate) fn repeated_fill_byte(operand: &Operand, elem: &Ty) -> Option<u8> {
    let (width_bytes, bits) = match (elem, operand) {
        (Ty::Bool, Operand::Constant(ConstValue::Bool(b))) => (1, u128::from(*b)),
        (Ty::Int { width, .. }, Operand::Constant(ConstValue::Int(v))) => (*width / 8, *v as u128),
        (Ty::Int { width, .. }, Operand::Constant(ConstValue::Uint(v, _))) => (*width / 8, *v),
        _ => return None,
    };
    let bytes = bits.to_le_bytes();
    let image = bytes.get(..usize::try_from(width_bytes).ok().filter(|w| *w > 0)?)?;
    image.iter().all(|b| *b == image[0]).then_some(image[0])
}

fn infer_int_const_ty(val: i128) -> Ty {
    match val {
        -128..=127 => Ty::i8(),
        -32_768..=32_767 => Ty::i16(),
        -2_147_483_648..=2_147_483_647 => Ty::i32(),
        -9_223_372_036_854_775_808..=9_223_372_036_854_775_807 => Ty::i64(),
        _ => Ty::i128(),
    }
}

fn operand_ty(ctx: &LoweringCtx<'_>, operand: &Operand) -> Result<Ty, BridgeError> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => ctx.place_ty(place),
        Operand::Constant(ConstValue::Bool(_)) => Ok(Ty::Bool),
        Operand::Constant(ConstValue::Int(val)) => Ok(infer_int_const_ty(*val)),
        Operand::Constant(ConstValue::Uint(_, width)) => {
            Ok(Ty::Int { width: *width, signed: false })
        }
        Operand::Constant(ConstValue::Float(_)) => Ok(Ty::f64_ty()),
        Operand::Constant(ConstValue::Unit | ConstValue::CallableItem { .. }) => Ok(Ty::Unit),
        Operand::Symbolic(formula) => ground_symbolic_formula_trust_ty(formula),
        _ => Err(BridgeError::UnsupportedOp("unknown operand variant".to_string())),
    }
}

fn direct_operand_ty(ctx: &LoweringCtx<'_>, operand: &Operand) -> Result<Option<Ty>, BridgeError> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Ok(Some(ctx.place_ty(place)?)),
        _ => Ok(None),
    }
}

fn cmp_operand_ty(ctx: &LoweringCtx<'_>, lhs: &Operand, rhs: &Operand) -> Result<Ty, BridgeError> {
    let lhs_direct_ty = direct_operand_ty(ctx, lhs)?;
    let rhs_direct_ty = direct_operand_ty(ctx, rhs)?;

    if let (Some(lhs_ty), Some(rhs_ty)) = (&lhs_direct_ty, &rhs_direct_ty)
        && lhs_ty != rhs_ty
    {
        return Err(BridgeError::InvalidMir(format!(
            "Cmp operand types must match, got {lhs_ty:?} and {rhs_ty:?}"
        )));
    }

    if let Some(ty) = lhs_direct_ty.or(rhs_direct_ty) {
        return Ok(ty);
    }

    let lhs_ty = operand_ty(ctx, lhs)?;
    let rhs_ty = operand_ty(ctx, rhs)?;
    if lhs_ty != rhs_ty {
        return Err(BridgeError::InvalidMir(format!(
            "Cmp operand types must match, got {lhs_ty:?} and {rhs_ty:?}"
        )));
    }
    Ok(lhs_ty)
}

/// A type whose VALUE the lowering carries as the ADDRESS of its bytes: a tuple, ADT or
/// array, and a slice FAT pointer (`&[T]`, `*const [T]`, and the `Ty::Slice` spelling of the
/// same two-word value). Their LIR types are aggregates (`emit_store_value`), so a value of
/// one never reaches an arithmetic, compare or cast instruction as itself: that would act on
/// the address, not on the bytes.
fn is_carried_ty(ty: &Ty) -> bool {
    is_addressable_local_ty(ty) || slice_element_type(ty).is_some()
}

/// The type of a binary operation's operands when they are CARRIED — an aggregate or a slice
/// fat pointer, whose value `resolve_operand` gives as the ADDRESS of its bytes
/// (`is_carried_ty`) — or `None` for scalar operands. A carried operand never reaches an
/// arithmetic or compare instruction as itself: that would act on the address of the bytes,
/// not on the value (ticket 216 cg review 6: `==` on two `*const [T]` compared the addresses
/// of the two fat pointers' words). Rust's comparisons of two slice fat pointers are the one
/// binary operation on carried operands (`lower_fat_pointer_compare`); any other is refused
/// here.
fn carried_operand_ty(
    ctx: &LoweringCtx<'_>,
    op: BinOp,
    operands: &[&Operand],
) -> Result<Option<Ty>, BridgeError> {
    let mut carried = None;
    let mut scalar = false;
    for operand in operands {
        match direct_operand_ty(ctx, operand)? {
            Some(ty) if is_carried_ty(&ty) => carried = Some(ty),
            _ => scalar = true,
        }
    }
    let Some(ty) = carried else {
        return Ok(None);
    };
    let comparison =
        matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
    if scalar || !comparison || slice_element_type(&ty).is_none() {
        return Err(BridgeError::UnsupportedOp(format!(
            "{op:?} with a fat pointer or aggregate operand ({ty:?}) is not lowered: such an \
             operand is carried by the address of its bytes; only ==, !=, <, <=, >, >= of two \
             slice fat pointers are"
        )));
    }
    Ok(Some(ty))
}

/// Rust's comparison of two slice fat pointers: the pairs (data, length)
/// compared lexicographically and unsigned, as rustc's codegen compares a
/// wide pointer (`==` both words equal, `!=` either differs, `<` the data
/// word less, or equal and the length less; `<=`, `>`, `>=` likewise).
/// `lhs` and `rhs` are CARRIERS: each word is read from them in place.
fn lower_fat_pointer_compare(
    dest: &Place,
    op: BinOp,
    fat_ty: &Ty,
    lhs: Value,
    rhs: Value,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    let lhs_data = ctx.emit_slice_data_ptr(lhs, fat_ty, instructions)?;
    let lhs_len = ctx.emit_slice_metadata(lhs, fat_ty, instructions)?;
    let rhs_data = ctx.emit_slice_data_ptr(rhs, fat_ty, instructions)?;
    let rhs_len = ctx.emit_slice_metadata(rhs, fat_ty, instructions)?;
    let compare = |ctx: &mut LoweringCtx<'_>,
                   instructions: &mut Vec<Instruction>,
                   cmp: BinOp,
                   a: Value,
                   b: Value| {
        Ok::<Value, BridgeError>(emit_binary_inst(ctx, instructions, map_binop(cmp, false)?, a, b))
    };
    let result = match op {
        BinOp::Eq | BinOp::Ne => {
            let data = compare(ctx, instructions, op, lhs_data, rhs_data)?;
            let len = compare(ctx, instructions, op, lhs_len, rhs_len)?;
            let join = if op == BinOp::Eq { Opcode::Band } else { Opcode::Bor };
            emit_binary_inst(ctx, instructions, join, data, len)
        }
        _ => {
            let strict = match op {
                BinOp::Le => BinOp::Lt,
                BinOp::Ge => BinOp::Gt,
                other => other,
            };
            let by_data = compare(ctx, instructions, strict, lhs_data, rhs_data)?;
            let same_data = compare(ctx, instructions, BinOp::Eq, lhs_data, rhs_data)?;
            let by_len = compare(ctx, instructions, op, lhs_len, rhs_len)?;
            let tie = emit_binary_inst(ctx, instructions, Opcode::Band, same_data, by_len);
            emit_binary_inst(ctx, instructions, Opcode::Bor, by_data, tie)
        }
    };
    assign_to_place(dest, result, ctx, instructions)
}

fn cmp_int_conditions(
    ctx: &LoweringCtx<'_>,
    lhs: &Operand,
    rhs: &Operand,
) -> Result<(IntCC, IntCC), BridgeError> {
    match cmp_operand_ty(ctx, lhs, rhs)? {
        Ty::Int { signed: true, .. } => Ok((IntCC::SignedLessThan, IntCC::SignedGreaterThan)),
        Ty::Int { signed: false, .. } => Ok((IntCC::UnsignedLessThan, IntCC::UnsignedGreaterThan)),
        other => Err(BridgeError::UnsupportedOp(format!(
            "three-way Cmp requires integer operands with signedness, got {other:?}"
        ))),
    }
}

fn raw_ptr_pointee_support_error(pointee_ty: &Ty) -> Option<String> {
    match pointee_ty {
        Ty::Dynamic { .. } => {
            Some("trait-object pointers carry a vtable metadata lane".to_string())
        }
        Ty::Unsupported { kind, detail } => {
            Some(format!("pointee type {kind} is unsupported: {detail}"))
        }
        _ => None,
    }
}

enum RawPtrAggregateOperands<'a> {
    Thin { data: &'a Operand },
    Slice { data: &'a Operand, metadata: &'a Operand, elem_ty: Ty },
}

fn ensure_raw_ptr_aggregate_data_operand(
    ctx: &LoweringCtx<'_>,
    operand: &Operand,
    expected_pointee: &Ty,
    mutable: bool,
) -> Result<(), BridgeError> {
    match operand_ty(ctx, operand)? {
        Ty::RawPtr { mutable: data_mutable, pointee } => {
            if data_mutable != mutable {
                return Err(BridgeError::UnsupportedOp(format!(
                    "raw pointer aggregate data pointer mutability {data_mutable} does not match aggregate mutability {mutable}"
                )));
            }
            if pointee.as_ref() != expected_pointee {
                return Err(BridgeError::UnsupportedOp(format!(
                    "raw pointer aggregate data pointer pointee {pointee:?} does not match expected thin pointee {expected_pointee:?}"
                )));
            }
            if let Some(reason) = raw_ptr_pointee_support_error(&pointee) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "raw pointer aggregate data operand must be a thin raw pointer; got {pointee:?}: {reason}"
                )));
            }
            Ok(())
        }
        other => Err(BridgeError::UnsupportedOp(format!(
            "raw pointer aggregate first operand must be a raw pointer; got {other:?}"
        ))),
    }
}

fn ensure_slice_metadata_operand(
    ctx: &LoweringCtx<'_>,
    operand: &Operand,
) -> Result<(), BridgeError> {
    match operand_ty(ctx, operand)? {
        ty if ty == Ty::usize() => Ok(()),
        other => Err(BridgeError::UnsupportedOp(format!(
            "slice raw pointer aggregate metadata operand must be a precise usize length lane; got {other:?}"
        ))),
    }
}

fn raw_ptr_aggregate_operands<'a>(
    ctx: &LoweringCtx<'_>,
    dest_ty: &Ty,
    pointee_ty: &Ty,
    mutable: bool,
    operands: &'a [Operand],
) -> Result<RawPtrAggregateOperands<'a>, BridgeError> {
    match dest_ty {
        Ty::RawPtr { mutable: dest_mutable, pointee }
            if *dest_mutable == mutable && pointee.as_ref() == pointee_ty => {}
        Ty::RawPtr { .. } => {
            return Err(BridgeError::UnsupportedOp(format!(
                "raw pointer aggregate kind does not match destination type: kind pointee={pointee_ty:?} mutable={mutable}, dest={dest_ty:?}"
            )));
        }
        other => {
            return Err(BridgeError::UnsupportedOp(format!(
                "raw pointer aggregate destination must be raw pointer; got {other:?}"
            )));
        }
    }

    if operands.len() != 2 {
        return Err(BridgeError::UnsupportedOp(format!(
            "raw pointer aggregate must have data pointer and metadata operands; got {} operands",
            operands.len()
        )));
    }

    if let Some(reason) = raw_ptr_pointee_support_error(pointee_ty) {
        return Err(BridgeError::UnsupportedOp(format!(
            "raw pointer aggregate for pointee {pointee_ty:?} requires fat-pointer metadata semantics: {reason}"
        )));
    }

    if let Ty::Slice { elem } = pointee_ty {
        ensure_raw_ptr_aggregate_data_operand(ctx, &operands[0], elem, mutable)?;
        ensure_slice_metadata_operand(ctx, &operands[1])?;
        return Ok(RawPtrAggregateOperands::Slice {
            data: &operands[0],
            metadata: &operands[1],
            elem_ty: (**elem).clone(),
        });
    }

    ensure_raw_ptr_aggregate_data_operand(ctx, &operands[0], pointee_ty, mutable)?;
    match operand_ty(ctx, &operands[1])? {
        Ty::Unit => Ok(RawPtrAggregateOperands::Thin { data: &operands[0] }),
        other => Err(BridgeError::UnsupportedOp(format!(
            "thin raw pointer aggregate metadata must be unit; got {other:?}"
        ))),
    }
}

fn ptr_metadata_support_error(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Dynamic { .. } => Some("trait-object metadata is a vtable pointer".to_string()),
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
            ptr_metadata_support_error(inner)
        }
        _ => None,
    }
}

fn unsupported_symbolic_formula(formula: &Formula) -> BridgeError {
    BridgeError::UnsupportedOp(format!(
        "symbolic operand requires target-semantic lowering; refusing to replace `{formula:?}` with an arbitrary integer"
    ))
}

fn ground_symbolic_formula_lir_const(formula: &Formula) -> Result<(LirType, i64), BridgeError> {
    match formula {
        Formula::Bool(value) => Ok((LirType::B1, i64::from(*value))),
        Formula::BitVec { value, width } => {
            if !matches!(*width, 1 | 8 | 16 | 32 | 64) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "ground symbolic bit-vector width {width} has no exact Iconst representation"
                )));
            }
            let mask = (1_u128 << *width) - 1;
            if *value >= 0 && (*value as u128) > mask {
                return Err(BridgeError::UnsupportedOp(format!(
                    "ground symbolic bit-vector value {value} does not fit width {width}"
                )));
            }
            let bits = (*value as u128) & mask;
            Ok((lir_int_type(*width), bits as i64))
        }
        _ => Err(unsupported_symbolic_formula(formula)),
    }
}

fn ground_symbolic_formula_trust_ty(formula: &Formula) -> Result<Ty, BridgeError> {
    match formula {
        Formula::Bool(_) => Ok(Ty::Bool),
        Formula::BitVec { width, .. } if matches!(*width, 1 | 8 | 16 | 32 | 64) => {
            Ok(Ty::Int { width: *width, signed: false })
        }
        Formula::BitVec { width, .. } => Err(BridgeError::UnsupportedOp(format!(
            "ground symbolic bit-vector width {width} has no exact Iconst representation"
        ))),
        _ => Err(unsupported_symbolic_formula(formula)),
    }
}

fn lir_int_type(width: u32) -> LirType {
    match width {
        1 => LirType::B1,
        8 => LirType::I8,
        16 => LirType::I16,
        32 => LirType::I32,
        64 => LirType::I64,
        128 => LirType::I128,
        _ => LirType::I64,
    }
}

fn checked_binary_value_ty(ctx: &LoweringCtx<'_>, dest: &Place) -> Result<Ty, BridgeError> {
    match ctx.place_ty(dest)? {
        Ty::Tuple(fields) if fields.len() == 2 && fields[1] == Ty::Bool => Ok(fields[0].clone()),
        other => Err(BridgeError::InvalidMir(format!(
            "CheckedBinaryOp destination must be a 2-field tuple ending in bool, got place type {other:?}"
        ))),
    }
}

fn next_wider_int_type(ty: &LirType) -> Option<LirType> {
    match ty {
        LirType::I8 => Some(LirType::I16),
        LirType::I16 => Some(LirType::I32),
        LirType::I32 => Some(LirType::I64),
        LirType::I64 => Some(LirType::I128),
        _ => None,
    }
}

fn integer_type_for_bits(bits: u32) -> Result<LirType, BridgeError> {
    match bits {
        1 => Ok(LirType::B1),
        8 => Ok(LirType::I8),
        16 => Ok(LirType::I16),
        32 => Ok(LirType::I32),
        64 => Ok(LirType::I64),
        128 => Ok(LirType::I128),
        _ => Err(BridgeError::UnsupportedType(format!("integer width {bits}"))),
    }
}

fn emit_iconst(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    ty: LirType,
    imm: i64,
) -> Value {
    let value = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty, imm },
        args: vec![],
        results: vec![value],
    });
    value
}

fn emit_binary_inst(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    opcode: Opcode,
    lhs: Value,
    rhs: Value,
) -> Value {
    let result = ctx.fresh_value();
    instructions.push(Instruction { opcode, args: vec![lhs, rhs], results: vec![result] });
    result
}

fn emit_int_cast(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    value: Value,
    from_ty: &LirType,
    to_ty: &LirType,
    signed: bool,
) -> Result<Value, BridgeError> {
    if from_ty == to_ty {
        return Ok(value);
    }

    let opcode = if to_ty.bits() > from_ty.bits() {
        if signed {
            Opcode::Sextend { from_ty: from_ty.clone(), to_ty: to_ty.clone() }
        } else {
            Opcode::Uextend { from_ty: from_ty.clone(), to_ty: to_ty.clone() }
        }
    } else {
        Opcode::Trunc { to_ty: to_ty.clone() }
    };

    let result = ctx.fresh_value();
    instructions.push(Instruction { opcode, args: vec![value], results: vec![result] });
    Ok(result)
}

struct CheckedOverflowFlagInput<'a> {
    op: BinOp,
    rhs: &'a Operand,
    lhs_val: Value,
    rhs_val: Value,
    arith_result: Value,
    value_ty: &'a Ty,
    value_lir_ty: &'a LirType,
}

fn lower_checked_overflow_flag(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    input: CheckedOverflowFlagInput<'_>,
) -> Result<Value, BridgeError> {
    let CheckedOverflowFlagInput {
        op,
        rhs,
        lhs_val,
        rhs_val,
        arith_result,
        value_ty,
        value_lir_ty,
    } = input;
    let signed = value_ty.is_signed();

    match op {
        BinOp::Add if signed => {
            let lhs_xor_result =
                emit_binary_inst(ctx, instructions, Opcode::Bxor, lhs_val, arith_result);
            let rhs_xor_result =
                emit_binary_inst(ctx, instructions, Opcode::Bxor, rhs_val, arith_result);
            let sign_conflict =
                emit_binary_inst(ctx, instructions, Opcode::Band, lhs_xor_result, rhs_xor_result);
            let zero = emit_iconst(ctx, instructions, value_lir_ty.clone(), 0);
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::SignedLessThan },
                sign_conflict,
                zero,
            ))
        }
        BinOp::Add => Ok(emit_binary_inst(
            ctx,
            instructions,
            Opcode::Icmp { cond: IntCC::UnsignedLessThan },
            arith_result,
            lhs_val,
        )),
        BinOp::Sub if signed => {
            let lhs_xor_rhs = emit_binary_inst(ctx, instructions, Opcode::Bxor, lhs_val, rhs_val);
            let lhs_xor_result =
                emit_binary_inst(ctx, instructions, Opcode::Bxor, lhs_val, arith_result);
            let sign_conflict =
                emit_binary_inst(ctx, instructions, Opcode::Band, lhs_xor_rhs, lhs_xor_result);
            let zero = emit_iconst(ctx, instructions, value_lir_ty.clone(), 0);
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::SignedLessThan },
                sign_conflict,
                zero,
            ))
        }
        BinOp::Sub => Ok(emit_binary_inst(
            ctx,
            instructions,
            Opcode::Icmp { cond: IntCC::UnsignedLessThan },
            lhs_val,
            rhs_val,
        )),
        BinOp::Mul => {
            let wide_ty = next_wider_int_type(value_lir_ty).ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "checked multiply overflow flag not yet supported for {value_ty:?}"
                ))
            })?;
            let lhs_wide =
                emit_int_cast(ctx, instructions, lhs_val, value_lir_ty, &wide_ty, signed)?;
            let rhs_wide =
                emit_int_cast(ctx, instructions, rhs_val, value_lir_ty, &wide_ty, signed)?;
            let result_wide =
                emit_int_cast(ctx, instructions, arith_result, value_lir_ty, &wide_ty, signed)?;
            let full_product =
                emit_binary_inst(ctx, instructions, Opcode::Imul, lhs_wide, rhs_wide);
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::NotEqual },
                result_wide,
                full_product,
            ))
        }
        BinOp::Shl | BinOp::Shr => {
            let rhs_ty = operand_ty(ctx, rhs)?;
            let rhs_lir_ty = map_type(&rhs_ty)?;
            let compare_bits = rhs_lir_ty.bits().max(value_lir_ty.bits()).max(8);
            let compare_ty = integer_type_for_bits(compare_bits)?;
            let normalized_rhs = emit_int_cast(
                ctx,
                instructions,
                rhs_val,
                &rhs_lir_ty,
                &compare_ty,
                rhs_ty.is_signed(),
            )?;
            let bitwidth =
                emit_iconst(ctx, instructions, compare_ty.clone(), i64::from(value_lir_ty.bits()));
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::UnsignedGreaterThanOrEqual },
                normalized_rhs,
                bitwidth,
            ))
        }
        BinOp::Div | BinOp::Rem => Err(BridgeError::UnsupportedOp(format!(
            "checked {:?} overflow flag lowering not yet supported",
            op
        ))),
        _ => Err(BridgeError::UnsupportedOp(format!(
            "checked {:?} overflow flag lowering not supported",
            op
        ))),
    }
}

/// The address an in-memory constructor (`Aggregate`, `Repeat`, `CheckedBinaryOp`) writes its
/// lanes at. A direct local's is its ONE memory-backed slot, so every definition of the local —
/// in whichever arm — writes the memory later projections read.
///
/// A projected destination (`(_1.1: E) = E::B(3)`, rustc's `s.e = E::B(3)`; `((_1 as Some).0)
/// = ..`; `(*_2) = (7, 8)`) is written in place at the PLACE's address, the value built typed
/// as the place (`built_dest_ty`), so its sibling lanes are untouched (ticket 216 cg-bridge,
/// review 2: building the whole local's type there overwrote them with a mis-typed image). The
/// callers read every operand before the first lane is written, and an aggregate operand is a
/// snapshot of its bytes (`LoweringCtx::emit_load_value`), so no lane written here can change
/// an operand, even one read from the destination itself or through a pointer that reaches
/// it.
fn constructor_dest_addr(
    ctx: &mut LoweringCtx<'_>,
    dest: &Place,
    constructor: &str,
    instructions: &mut Vec<Instruction>,
) -> Result<Value, BridgeError> {
    if place_is_direct_local(dest) {
        let slot = ctx.memory_backed_slot(dest.local).map_err(|err| match err {
            BridgeError::UnsupportedOp(detail) => {
                BridgeError::UnsupportedOp(format!("{constructor}: {detail}"))
            }
            other => other,
        })?;
        return Ok(ctx.emit_stack_addr(slot, instructions));
    }
    ctx.resolve_place_addr(dest, instructions)
}

/// After a constructor wrote `dest` at `base_ptr` (`constructor_dest_addr`): a direct local's
/// value is the address of its slot (an aggregate is carried by the address of its bytes); a
/// projected destination was written in memory and binds nothing.
fn bind_constructed(ctx: &mut LoweringCtx<'_>, dest: &Place, base_ptr: Value) {
    if place_is_direct_local(dest) {
        ctx.local_values.insert(dest.local, base_ptr);
    }
}

/// The type of the value an rvalue BUILDS for `dest` (`Aggregate`, `Repeat`, `CheckedBinaryOp`).
/// A direct local keeps its declared type, the type of its slot; a projected place takes the
/// PROJECTED type (a `Downcast` + `Field` resolves to the variant's own lane), never the base
/// local's.
fn built_dest_ty(ctx: &LoweringCtx<'_>, dest: &Place) -> Result<Ty, BridgeError> {
    if place_is_direct_local(dest) {
        Ok(ctx.local_ty(dest.local)?.clone())
    } else {
        ctx.place_ty(dest)
    }
}

/// Whether an `AggregateKind::Adt` name names the destination's ADT type. The aggregate carries
/// the generics-erased def path; a type may carry the same path or, for a generic cut-point
/// definition (`trust_mir_extract::ty_convert::rename_definition`), the path followed by its
/// instantiated arguments (`k::Foo<u8>`).
fn aggregate_names_adt(aggregate_name: &str, adt_name: &str) -> bool {
    adt_name == aggregate_name
        || adt_name.strip_prefix(aggregate_name).is_some_and(|args| args.starts_with('<'))
}

/// The value of the aggregate stored at `base_ptr`: a snapshot of its bytes, addressed (see
/// `LoweringCtx::emit_load_value`).
fn materialize_aggregate_value(
    ctx: &mut LoweringCtx<'_>,
    base_ptr: Value,
    lir_ty: &LirType,
    instructions: &mut Vec<Instruction>,
) -> Value {
    ctx.emit_load_value(lir_ty.clone(), base_ptr, instructions)
}

/// Indices into `body.blocks` in reverse postorder of the CFG, entry (`blocks[0]`) first.
///
/// Blocks unreachable from the entry are appended afterwards, each unreachable component in
/// its own reverse postorder. Unreachable roots with no predecessor are taken first (in MIR
/// order), so a dead single-predecessor block still follows its dead predecessor; any block
/// left over (a dead cycle) roots last. The result is a permutation of `0..body.blocks.len()`:
/// every block a lowering pass must see is visited exactly once.
pub(crate) fn reverse_postorder_block_indices(body: &VerifiableBody) -> Vec<usize> {
    let index_of: FxHashMap<usize, usize> =
        body.blocks.iter().enumerate().map(|(index, bb)| (bb.id.0, index)).collect();
    let mut visited = vec![false; body.blocks.len()];
    let mut order = Vec::with_capacity(body.blocks.len());

    let mut has_predecessor = vec![false; body.blocks.len()];
    for bb in &body.blocks {
        for succ in terminator_successors(&bb.terminator) {
            if let Some(&index) = index_of.get(&succ) {
                has_predecessor[index] = true;
            }
        }
    }
    // Entry first, then predecessor-free (dead) roots, then whatever is left (dead cycles).
    let roots = std::iter::once(0)
        .chain((1..body.blocks.len()).filter(|&i| !has_predecessor[i]))
        .chain(1..body.blocks.len());
    for root in roots {
        if visited[root] {
            continue;
        }
        visited[root] = true;
        // Iterative DFS: (block index, its successors as block indices, next successor to try).
        let mut postorder = Vec::new();
        let mut stack: Vec<(usize, Vec<usize>, usize)> = vec![(
            root,
            terminator_successors(&body.blocks[root].terminator)
                .into_iter()
                .filter_map(|id| index_of.get(&id).copied())
                .collect(),
            0,
        )];
        while let Some((block, succs, next)) = stack.last_mut() {
            if let Some(&succ) = succs.get(*next) {
                *next += 1;
                if !visited[succ] {
                    visited[succ] = true;
                    let succ_succs = terminator_successors(&body.blocks[succ].terminator)
                        .into_iter()
                        .filter_map(|id| index_of.get(&id).copied())
                        .collect();
                    stack.push((succ, succ_succs, 0));
                }
            } else {
                postorder.push(*block);
                stack.pop();
            }
        }
        order.extend(postorder.into_iter().rev());
    }
    order
}

/// For each position in `body.blocks`, whether the block is reachable from the entry
/// (`blocks[0]`) along `terminator_successors` edges.
fn reachable_from_entry(body: &VerifiableBody) -> Vec<bool> {
    let index_of: FxHashMap<usize, usize> =
        body.blocks.iter().enumerate().map(|(index, bb)| (bb.id.0, index)).collect();
    let mut reachable = vec![false; body.blocks.len()];
    let mut stack = vec![0_usize];
    reachable[0] = true;
    while let Some(index) = stack.pop() {
        for succ in terminator_successors(&body.blocks[index].terminator) {
            if let Some(&succ_index) = index_of.get(&succ)
                && !reachable[succ_index]
            {
                reachable[succ_index] = true;
                stack.push(succ_index);
            }
        }
    }
    reachable
}

/// The local values block `block_id` starts from, before its own block parameters are
/// bound: its only predecessor's exit values when that predecessor recorded them, else
/// the function-entry values.
///
/// The function-entry values are exact for a join's locals that are not block
/// parameters (never reassigned, or not live into it) and harmless in a block that
/// never runs. They are never right for a REACHABLE block with a single predecessor:
/// that block reads whatever its predecessor left, and reverse postorder lowers the
/// predecessor first. If the values are missing anyway, refuse rather than read stale
/// or never-defined entry values (the silent wrong code this ordering exists to rule out).
pub(crate) fn block_start_values(
    block_id: usize,
    reachable: bool,
    predecessors: &FxHashMap<usize, Vec<usize>>,
    block_entry_values: &FxHashMap<usize, FxHashMap<usize, Value>>,
    initial_local_values: &FxHashMap<usize, Value>,
) -> Result<FxHashMap<usize, Value>, BridgeError> {
    match block_entry_values.get(&block_id) {
        Some(values) => Ok(values.clone()),
        None if reachable && predecessors.get(&block_id).is_some_and(|preds| preds.len() == 1) => {
            Err(BridgeError::InvalidMir(format!(
                "bb{block_id} was lowered before its only predecessor; its entry values are unknown"
            )))
        }
        None => Ok(initial_local_values.clone()),
    }
}

pub(crate) fn terminator_successors(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Goto(target) => vec![target.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs = Vec::with_capacity(targets.len() + 1);
            for (_, target) in targets {
                if !succs.contains(&target.0) {
                    succs.push(target.0);
                }
            }
            if !succs.contains(&otherwise.0) {
                succs.push(otherwise.0);
            }
            succs
        }
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Call { target: Some(target), .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        _ => vec![],
    }
}

pub(crate) fn terminator_supports_block_param_copies(term: &Terminator) -> bool {
    matches!(
        term,
        Terminator::Goto(_)
            | Terminator::Assert { .. }
            | Terminator::SwitchInt { .. }
            | Terminator::Call { target: Some(_), .. }
            | Terminator::Drop { .. }
    )
}

fn conditional_edge_dest(
    target: usize,
    ctx: &mut LoweringCtx<'_>,
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<Block, BridgeError> {
    if !block_params.contains_key(&target) {
        return Ok(Block(target as u32));
    }

    let edge_block = ctx.fresh_block();
    let mut instructions = Vec::new();
    emit_block_param_copies(target, ctx, &mut instructions, block_params)?;
    instructions.push(Instruction {
        opcode: Opcode::Jump { dest: Block(target as u32) },
        args: vec![],
        results: vec![],
    });
    ctx.pending_blocks
        .push((edge_block, LirBlock { params: vec![], instructions, source_locs: vec![] }));
    Ok(edge_block)
}

fn note_live_in(
    local: usize,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    if !written.contains(&local) && seen.insert(local) {
        live_ins.push(local);
    }
}

fn collect_place_live_ins(
    place: &Place,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    note_live_in(place.local, written, seen, live_ins);
    for projection in &place.projections {
        if let Projection::Index(index_local) = projection {
            note_live_in(*index_local, written, seen, live_ins);
        }
    }
}

fn collect_operand_live_ins(
    operand: &Operand,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        collect_place_live_ins(place, written, seen, live_ins);
    }
}

fn collect_rvalue_live_ins(
    rvalue: &Rvalue,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::Repeat(operand, _) => {
            collect_operand_live_ins(operand, written, seen, live_ins);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_operand_live_ins(lhs, written, seen, live_ins);
            collect_operand_live_ins(rhs, written, seen, live_ins);
        }
        Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::AddressOf(_, place) => {
            collect_place_live_ins(place, written, seen, live_ins);
        }
        Rvalue::Ref { place, .. } => {
            collect_place_live_ins(place, written, seen, live_ins);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                collect_operand_live_ins(operand, written, seen, live_ins);
            }
        }
        _ => {}
    }
}

fn collect_block_live_ins(bb: &TrustBlock, return_lowering: ReturnLowering) -> Vec<usize> {
    let mut written = FxHashSet::default();
    let mut seen = FxHashSet::default();
    let mut live_ins = Vec::new();

    for stmt in &bb.stmts {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                collect_rvalue_live_ins(rvalue, &written, &mut seen, &mut live_ins);
                if place_is_direct_local(place) {
                    written.insert(place.local);
                } else {
                    collect_place_live_ins(place, &written, &mut seen, &mut live_ins);
                }
            }
            // `discriminant(*p) = k` stores the tag through `p`'s value
            // (`lower_set_discriminant` -> `resolve_place_addr`), so `p` is read here.
            Statement::SetDiscriminant { place, .. } => {
                collect_place_live_ins(place, &written, &mut seen, &mut live_ins);
            }
            // `copy_nonoverlapping(src, dst, count)` reads all three operands
            // (`lower_copy_nonoverlapping`).
            Statement::CopyNonOverlapping { src, dst, count, .. } => {
                for operand in [src, dst, count] {
                    collect_operand_live_ins(operand, &written, &mut seen, &mut live_ins);
                }
            }
            _ => {}
        }
    }

    match &bb.terminator {
        Terminator::SwitchInt { discr, .. } | Terminator::Assert { cond: discr, .. } => {
            collect_operand_live_ins(discr, &written, &mut seen, &mut live_ins);
        }
        Terminator::Call { args, dest, atomic, .. } => {
            for arg in args {
                collect_operand_live_ins(arg, &written, &mut seen, &mut live_ins);
            }
            if let Some(atomic) = atomic {
                collect_place_live_ins(&atomic.place, &written, &mut seen, &mut live_ins);
                let result_dest = atomic.dest.as_ref().unwrap_or(dest);
                if !place_is_direct_local(result_dest) {
                    collect_place_live_ins(result_dest, &written, &mut seen, &mut live_ins);
                }
            } else if !place_is_direct_local(dest) {
                collect_place_live_ins(dest, &written, &mut seen, &mut live_ins);
            }
        }
        Terminator::Drop { place, .. } => {
            collect_place_live_ins(place, &written, &mut seen, &mut live_ins);
        }
        Terminator::Return if return_lowering == ReturnLowering::Value => {
            note_live_in(0, &written, &mut seen, &mut live_ins);
        }
        _ => {}
    }

    live_ins
}

fn collect_predecessors(body: &VerifiableBody) -> FxHashMap<usize, Vec<usize>> {
    let mut predecessors =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());

    for bb in &body.blocks {
        for successor in terminator_successors(&bb.terminator) {
            let preds: &mut Vec<usize> = predecessors.entry(successor).or_default();
            if !preds.contains(&bb.id.0) {
                preds.push(bb.id.0);
            }
        }
    }

    predecessors
}

fn collect_assigned_locals(body: &VerifiableBody) -> FxHashSet<usize> {
    let mut assigned = FxHashSet::default();

    for bb in &body.blocks {
        for stmt in &bb.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place_is_direct_local(place)
            {
                assigned.insert(place.local);
            }
        }
        if let Some(local) = terminator_written_local(&bb.terminator) {
            assigned.insert(local);
        }
    }

    assigned
}

/// The locals that live in memory: one stack slot each for the whole function, written at
/// every whole-local definition and read at every use (see `LoweringCtx::memory_backed`).
///
/// It is the set of base locals some lowering path asks the ADDRESS of, collected before any
/// block is lowered, as a superset of every place lowering reaches
/// `LoweringCtx::materialize_local_stack_addr` (which refuses a local not in this set):
/// * (a) the base local of a `Ref`/`AddressOf` place (`resolve_place_addr`);
/// * (b) the base local of a projected assignment, call or atomic-result destination and of a
///   `SetDiscriminant` place (stored through `resolve_place_addr`);
///
///   except, in (a) and (b), a place that starts by dereferencing a pointer-valued local
///   (`&*p`, `*p = v`, `(*p).0 = v`): its address is computed from `p`'s value
///   (`place_addr_starts_at_pointer_value`), so `p` needs no slot;
/// * (c) the base local of a projected READ whose type is an addressable aggregate
///   (`resolve_place` walks a tuple/ADT/array field through the slot);
/// * (d) the destination of every `Aggregate`/`Repeat`/`CheckedBinaryOp` (built in memory: a
///   direct destination in its own slot, a projected one through its address as in (b)) and
///   the place of a `Discriminant` (the tag is read from the slot);
/// * (e) every local whose LIR type is an aggregate: LIR carries an aggregate value as the
///   address of its bytes (`LoweringCtx::emit_store_value`), so such a local's value must live
///   in memory the local owns. An address held as its SSA value would alias the memory it was
///   read from and see that memory's later writes (a field store, the next loop iteration's
///   snapshot), and could not be merged across a join as a block parameter.
///
/// An extra member only costs a store per definition and a load per read; a missing one is
/// refused at lowering time. Lowering order cannot affect the result: the set is a property
/// of the whole body.
fn collect_memory_backed_locals(body: &VerifiableBody) -> FxHashSet<usize> {
    struct Planner<'a> {
        local_tys: FxHashMap<usize, &'a Ty>,
        backed: FxHashSet<usize>,
    }

    impl Planner<'_> {
        /// (c), (d): the local's own slot is read or written.
        fn base(&mut self, place: &Place) {
            self.backed.insert(place.local);
        }

        /// (a), (b): `resolve_place_addr` takes the address of `place`, which needs the base
        /// local's slot unless the place starts by dereferencing a pointer-valued local.
        fn address(&mut self, place: &Place) {
            let through_pointer_value = self
                .local_tys
                .get(&place.local)
                .is_some_and(|ty| place_addr_starts_at_pointer_value(place, ty));
            if !through_pointer_value {
                self.base(place);
            }
        }

        /// (b): a destination with projections is stored through its address.
        fn destination(&mut self, place: &Place) {
            if !place.projections.is_empty() {
                self.address(place);
            }
        }

        /// (d): an in-memory constructor writes a direct destination's own slot, and a
        /// projected one through its address (`constructor_dest_addr`).
        fn constructed(&mut self, place: &Place) {
            if place.projections.is_empty() {
                self.base(place);
            } else {
                self.address(place);
            }
        }

        /// (c): a projected read of an addressable aggregate walks its slot.
        fn read(&mut self, place: &Place) {
            if !place.projections.is_empty()
                && self.local_tys.get(&place.local).is_some_and(|ty| is_addressable_local_ty(ty))
            {
                self.base(place);
            }
        }

        fn operand(&mut self, operand: &Operand) {
            if let Operand::Copy(place) | Operand::Move(place) = operand {
                self.read(place);
            }
        }

        fn rvalue(&mut self, dest: &Place, rvalue: &Rvalue) {
            match rvalue {
                Rvalue::Use(operand) | Rvalue::UnaryOp(_, operand) | Rvalue::Cast(operand, _) => {
                    self.operand(operand);
                    self.destination(dest);
                }
                Rvalue::BinaryOp(_, lhs, rhs) => {
                    self.operand(lhs);
                    self.operand(rhs);
                    self.destination(dest);
                }
                Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                    self.operand(lhs);
                    self.operand(rhs);
                    self.constructed(dest);
                }
                Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => {
                    self.address(place);
                    self.destination(dest);
                }
                Rvalue::Discriminant(place) => {
                    self.base(place);
                    self.read(place);
                    self.destination(dest);
                }
                Rvalue::Len(place) | Rvalue::CopyForDeref(place) => {
                    self.read(place);
                    self.destination(dest);
                }
                Rvalue::Aggregate(AggregateKind::RawPtr { .. }, operands) => {
                    for operand in operands {
                        self.operand(operand);
                    }
                    self.destination(dest);
                }
                Rvalue::Aggregate(_, operands) => {
                    for operand in operands {
                        self.operand(operand);
                    }
                    self.constructed(dest);
                }
                Rvalue::Repeat(operand, _) => {
                    self.operand(operand);
                    self.constructed(dest);
                }
                // Every other rvalue is refused by `lower_rvalue`; be generous anyway.
                _ => self.destination(dest),
            }
        }
    }

    let mut planner = Planner {
        local_tys: body.locals.iter().map(|local| (local.index, &local.ty)).collect(),
        backed: FxHashSet::default(),
    };

    for bb in &body.blocks {
        for stmt in &bb.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => planner.rvalue(place, rvalue),
                // The tag is stored through `place` + `Field`, and a whole-local place is also
                // reloaded from its slot (`lower_set_discriminant`).
                Statement::SetDiscriminant { place, .. } => {
                    planner.address(place);
                    if place.projections.is_empty() {
                        planner.base(place);
                    }
                }
                // `copy_nonoverlapping(src, dst, count)` reads its three operands and writes
                // through `dst`'s VALUE (`lower_copy_nonoverlapping`).
                Statement::CopyNonOverlapping { src, dst, count, .. } => {
                    planner.operand(src);
                    planner.operand(dst);
                    planner.operand(count);
                }
                // Every other statement lowers to no instructions or is refused
                // (`lower_statement`).
                _ => {}
            }
        }

        match &bb.terminator {
            Terminator::SwitchInt { discr, .. } | Terminator::Assert { cond: discr, .. } => {
                planner.operand(discr);
            }
            Terminator::Call { args, dest, atomic, .. } => {
                for arg in args {
                    planner.operand(arg);
                }
                if let Some(atomic) = atomic {
                    planner.read(&atomic.place);
                    planner.destination(atomic.dest.as_ref().unwrap_or(dest));
                }
                planner.destination(dest);
            }
            _ => {}
        }
    }

    // (e): aggregate-typed locals.
    for local in &body.locals {
        if map_lowering_type(&local.ty).is_ok_and(|ty| ty.is_aggregate()) {
            planner.backed.insert(local.index);
        }
    }

    planner.backed
}

fn terminator_written_local(term: &Terminator) -> Option<usize> {
    match term {
        Terminator::Call { dest, atomic: None, .. } => {
            place_is_direct_local(dest).then_some(dest.local)
        }
        Terminator::Call { dest, atomic: Some(atomic), .. } => {
            if atomic.op_kind.is_store() || atomic.op_kind.is_fence() {
                return None;
            }

            atomic
                .dest
                .as_ref()
                .or(Some(dest))
                .and_then(|place| place_is_direct_local(place).then_some(place.local))
        }
        _ => None,
    }
}

fn collect_block_written_locals(bb: &TrustBlock) -> FxHashSet<usize> {
    let mut written = FxHashSet::default();

    for stmt in &bb.stmts {
        if let Statement::Assign { place, .. } = stmt
            && place_is_direct_local(place)
        {
            written.insert(place.local);
        }
    }

    if let Some(local) = terminator_written_local(&bb.terminator) {
        written.insert(local);
    }

    written
}

fn compute_required_locals(
    body: &VerifiableBody,
    return_lowering: ReturnLowering,
) -> FxHashMap<usize, Vec<usize>> {
    let mut required_locals =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    let mut required_seen =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    let mut written_locals =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());

    for bb in &body.blocks {
        let live_ins = collect_block_live_ins(bb, return_lowering);
        let seen: FxHashSet<usize> = live_ins.iter().copied().collect();
        required_locals.insert(bb.id.0, live_ins);
        required_seen.insert(bb.id.0, seen);
        written_locals.insert(bb.id.0, collect_block_written_locals(bb));
    }

    let mut propagated = Vec::new();
    loop {
        let mut changed = false;

        for bb in body.blocks.iter().rev() {
            if !terminator_supports_block_param_copies(&bb.terminator) {
                continue;
            }

            let successors = terminator_successors(&bb.terminator);
            let written =
                written_locals.get(&bb.id.0).expect("written locals exist for every block");
            propagated.clear();

            for successor in successors {
                let Some(successor_required) = required_locals.get(&successor) else {
                    continue;
                };

                for &local in successor_required {
                    if written.contains(&local) {
                        continue;
                    }
                    propagated.push(local);
                }
            }

            let block_required =
                required_locals.get_mut(&bb.id.0).expect("required locals exist for every block");
            let block_seen =
                required_seen.get_mut(&bb.id.0).expect("required-local set exists for every block");

            for &local in &propagated {
                if block_seen.insert(local) {
                    block_required.push(local);
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }

    required_locals
}

fn plan_block_params(
    body: &VerifiableBody,
    ctx: &mut LoweringCtx<'_>,
    predecessors: &FxHashMap<usize, Vec<usize>>,
    return_lowering: ReturnLowering,
) -> Result<FxHashMap<usize, Vec<BlockParam>>, BridgeError> {
    let blocks_by_id: FxHashMap<usize, &TrustBlock> =
        body.blocks.iter().map(|bb| (bb.id.0, bb)).collect();
    let assigned_locals = collect_assigned_locals(body);
    let required_locals = compute_required_locals(body, return_lowering);
    let mut block_params =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    let entry_id = body.blocks[0].id.0;

    for bb in &body.blocks {
        let Some(preds) = predecessors.get(&bb.id.0) else {
            continue;
        };
        // Trust: the entry block is also entered from the function entry, an implicit extra
        // predecessor, so once anything jumps back to it (a loop whose header is bb0) it is a
        // join like any other. Without block parameters it would read the function-entry
        // values of its loop-carried locals on every iteration. The function entry cannot
        // pass parameters, so `lower_body_to_lir_with_options_and_consumptions` enters such a
        // bb0 through a synthetic pre-entry block that copies the entry values in.
        let is_entry = bb.id.0 == entry_id;
        if !is_entry && preds.len() <= 1 {
            continue;
        }

        // A memory-backed local needs no block parameter: its slot is the value on every
        // path (each predecessor stored it), and its SSA value is never read. Copying that SSA
        // value would be dead at best and, on a path that wrote the local only through
        // memory, a copy of a value that path never defined.
        let live_ins: Vec<usize> = required_locals
            .get(&bb.id.0)
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .copied()
            .filter(|local| assigned_locals.contains(local) && !ctx.is_memory_backed(*local))
            .collect();
        if live_ins.is_empty() {
            continue;
        }
        // Trust: a join whose reassigned live-ins cannot be passed by every predecessor
        // would read the function-entry values of those locals — silent wrong code — so
        // refuse. Today every terminator with successors supports the copies
        // (`terminator_successors` and `terminator_supports_block_param_copies` name the
        // same variants), so this is unreachable until the two lists drift apart.
        if let Some(pred_id) = preds.iter().find(|pred_id| {
            blocks_by_id
                .get(pred_id)
                .is_none_or(|pred| !terminator_supports_block_param_copies(&pred.terminator))
        }) {
            return Err(BridgeError::UnsupportedOp(format!(
                "bb{} is a join (predecessors {preds:?}{}) that reads reassigned locals \
                 {live_ins:?}, but the terminator of predecessor bb{pred_id} cannot copy into \
                 block parameters",
                bb.id.0,
                if is_entry { ", plus the function entry" } else { "" },
            )));
        }

        let mut params = Vec::with_capacity(live_ins.len());
        for local in live_ins {
            params.push(BlockParam {
                local,
                value: ctx.fresh_value(),
                ty: map_lowering_type(ctx.local_ty(local)?)?,
            });
        }
        block_params.insert(bb.id.0, params);
    }

    Ok(block_params)
}

fn emit_block_param_copies(
    target: usize,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<(), BridgeError> {
    let Some(params) = block_params.get(&target) else {
        return Ok(());
    };

    let mut pending_copies = Vec::with_capacity(params.len());
    for param in params {
        let src = ctx.local_value(param.local)?;
        if src == param.value {
            continue;
        }
        pending_copies.push((src, param.value));
    }

    while !pending_copies.is_empty() {
        if let Some(idx) = pending_copies.iter().enumerate().find_map(|(idx, (_, dest))| {
            (!pending_copies
                .iter()
                .enumerate()
                .any(|(other_idx, (other_src, _))| other_idx != idx && *other_src == *dest))
            .then_some(idx)
        }) {
            let (src, dest) = pending_copies.swap_remove(idx);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dest],
            });
            continue;
        }

        let temp = ctx.fresh_value();
        let (src, _) = pending_copies[0];
        instructions.push(Instruction {
            opcode: Opcode::Copy,
            args: vec![src],
            results: vec![temp],
        });
        pending_copies[0].0 = temp;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Public API: lower_to_lir
// ---------------------------------------------------------------------------

// Trust: #828 — refresh supported MIR constructs in lower_to_lir docs.
/// Convert a trust-types `VerifiableFunction` to an trust_cg LIR `Function`.
///
/// This is the primary entry point for the bridge. It maps the function
/// signature, basic blocks, statements, and terminators to LIR equivalents.
///
/// # Supported MIR constructs
///
/// - Scalar and aggregate types (tuples, ADTs, arrays, slices, references)
/// - Place projections (field, deref, index, downcast, constant-index, subslice)
/// - Memory operations (load, store, stack slots, address-of)
/// - Function calls (direct), tail calls (through the canonical call/return
///   projection), and drop elaboration
/// - Supported terminators (goto, return, switch, assert, call, drop, unreachable)
/// - Casts (int-int, float-int, int-float, float-float, ptr-ptr)
#[must_use = "returns the lowered LIR function"]
pub fn lower_to_lir(func: &VerifiableFunction) -> Result<LirFunction, BridgeError> {
    if func.body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::TailCall { .. })) {
        let expanded = func.with_tail_calls_expanded();
        lower_body_to_lir(&expanded.name, &expanded.body)
    } else {
        lower_body_to_lir(&func.name, &func.body)
    }
}

#[must_use = "returns the lowered LIR function"]
pub fn lower_to_lir_with_options(
    func: &VerifiableFunction,
    options: &LoweringOptions,
) -> Result<LirFunction, BridgeError> {
    if func.body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::TailCall { .. })) {
        let expanded = func.with_tail_calls_expanded();
        lower_body_to_lir_with_options(&expanded.name, &expanded.body, options)
    } else {
        lower_body_to_lir_with_options(&func.name, &func.body, options)
    }
}

/// Convert a trust-types `VerifiableBody` to an trust_cg LIR `Function`.
///
/// Separated from `lower_to_lir` to allow testing with bodies directly.
pub fn lower_body_to_lir(name: &str, body: &VerifiableBody) -> Result<LirFunction, BridgeError> {
    lower_body_to_lir_with_options(name, body, &LoweringOptions::default())
}

pub fn lower_body_to_lir_with_options(
    name: &str,
    body: &VerifiableBody,
    options: &LoweringOptions,
) -> Result<LirFunction, BridgeError> {
    lower_body_to_lir_with_options_and_consumptions(name, body, options).map(|(lir, _)| lir)
}

/// Like [`lower_body_to_lir_with_options`], but also returns the symbolic
/// formulas the lowering consumed with target semantics (entry-register
/// bindings and recognized loads), keyed by source block and statement so the
/// binary-conversion evidence rows can be marked consumed.
pub fn lower_body_to_lir_with_options_and_consumptions(
    name: &str,
    body: &VerifiableBody,
    options: &LoweringOptions,
) -> Result<(LirFunction, Vec<crate::entry_binding::ConsumedSymbolicLowering>), BridgeError> {
    // Check the complete input before unsupported statement no-ops, dead code,
    // or contextual lowering can erase a diagnostic allocation observation.
    if body.contains_memory_image() {
        return Err(BridgeError::UnsupportedOp(
            "ConstValue::MemoryImage has no modeled allocation/provenance value semantics".into(),
        ));
    }
    // Trust: Validate that the function body is not empty.
    if body.blocks.is_empty() {
        return Err(BridgeError::EmptyBody);
    }

    // A bare body does not carry the function-level semantic projection used
    // by `lower_to_lir{,_with_options}`. Refuse TailCall explicitly here so a
    // body-only caller cannot accidentally lower it as an unknown no-successor
    // terminator. The VerifiableFunction entry points preserve it as the
    // equivalent direct Call writing local 0 followed by Return.
    if body.blocks.iter().any(|block| matches!(block.terminator, Terminator::TailCall { .. })) {
        return Err(BridgeError::UnsupportedOp(
            "TailCall requires the VerifiableFunction lowering entry point so its implicit return place can be projected exactly"
                .to_string(),
        ));
    }

    // Trust: Detect duplicate block IDs which indicate malformed MIR.
    {
        let mut seen_ids =
            FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
        for bb in &body.blocks {
            if let Some(()) = seen_ids.insert(bb.id.0, ()) {
                return Err(BridgeError::InvalidMir(format!("duplicate block ID: bb{}", bb.id.0)));
            }
        }
    }

    // Entry-register bindings: cross-check the table against this body and
    // compute the per-block write-freedom certificate. A refused table keeps
    // lowering param-free (symbolic refusals then carry the reason); a
    // justified one makes the params real LIR formals. Mixing with MIR
    // argument locals is refused outright — the two parameter conventions
    // must never coexist in one function.
    let entry_inputs = match &options.entry_bindings {
        Some(bindings) if !bindings.params.is_empty() => {
            if body.arg_count != 0 {
                return Err(BridgeError::UnsupportedOp(format!(
                    "entry-register bindings cannot be combined with MIR argument locals \
                     (arg_count {}); a body has exactly one parameter convention",
                    body.arg_count
                )));
            }
            match crate::entry_binding::compute_entry_preservation(body, bindings) {
                Ok(preservation) => {
                    Some(EntryBindingInputs::Justified { bindings: bindings.clone(), preservation })
                }
                Err(refusal) => Some(EntryBindingInputs::Refused { reason: refusal.reason }),
            }
        }
        _ => None,
    };

    // Compute the maximum block ID so the context can allocate new blocks
    // (e.g., the panic block for Assert) without collisions.
    let max_block_id = body.blocks.iter().map(|bb| bb.id.0 as u32).max().unwrap_or(0);
    let mut ctx =
        LoweringCtx::new(&body.locals, body.arg_count, max_block_id, options, entry_inputs);
    let initial_local_values = ctx.local_values.clone();
    let predecessors = collect_predecessors(body);
    let return_lowering = return_lowering_for(body);
    // Trust: give every memory-backed local its ONE slot before any block is lowered (see
    // `collect_memory_backed_locals`). Must precede `plan_block_params`, which leaves these
    // locals out of the block parameters.
    ctx.plan_memory_backed_locals(&collect_memory_backed_locals(body));
    let block_params = plan_block_params(body, &mut ctx, &predecessors, return_lowering)?;
    // The memory-backed locals that already hold a value at function entry — the MIR
    // arguments — are stored into their slots once, before anything reads them: at the top of
    // the entry block, or, when the entry block is a loop target (re-entered by a back edge,
    // which would re-run the stores and reset the arguments every iteration), in the synthetic
    // pre-entry block below, which runs exactly once. Every other local is undefined until its
    // first definition, which stores.
    let entry_prologue_locals: Vec<usize> =
        (1..=body.arg_count).filter(|&local| ctx.is_memory_backed(local)).collect();
    let entry_is_loop_target = predecessors.contains_key(&body.blocks[0].id.0);
    // The function entry has a value only for a formal. A bb0 block parameter for any other
    // local (read in bb0 before any write) would be read on first entry with no value on the
    // pre-entry edge: valid rustc MIR reads no local before writing it, but the bridge does
    // not prove that, so such a body is REFUSED by name, at lowering (ticket 216 cg, review 6
    // follow-up). With the refusal disabled the pre-entry block copies the local's
    // never-defined placeholder and only trust-cg ISel stops it ("value Value(2) not defined
    // before use"); a lane that stops before ISel would see a well-formed LIR body.
    if let Some(param) = block_params
        .get(&body.blocks[0].id.0)
        .and_then(|params| params.iter().find(|param| !(1..=body.arg_count).contains(&param.local)))
    {
        return Err(BridgeError::UnsupportedOp(format!(
            "local _{} is live into the re-entered entry block bb{} but is not a formal: it \
             has no value on the function's entry edge (a read before any write)",
            param.local, body.blocks[0].id.0
        )));
    }

    // Build signature from locals: args are locals[1..=arg_count], return is locals[0].
    //
    let return_ty = match return_lowering {
        ReturnLowering::Value => Some(map_lowering_type(&body.return_ty)?),
        ReturnLowering::NoValue => None,
    };
    let mut param_types = Vec::with_capacity(body.arg_count);
    // Entry-register binding params come first, mirroring the Value(0..k)
    // allocation in LoweringCtx::new: LIR param i is the function-entry value
    // of the i-th bound ABI argument register, always a 64-bit machine word.
    if let Some(entry) = &ctx.entry_bindings {
        param_types.extend(entry.bindings.params.iter().map(|_| LirType::I64));
    }
    for i in 1..=body.arg_count {
        let local = body
            .locals
            .get(i)
            .filter(|l| l.index == i)
            .or_else(|| body.locals.iter().find(|l| l.index == i))
            .ok_or(BridgeError::MissingLocal(i))?;
        param_types.push(map_lowering_type(&local.ty)?);
    }
    let returns = return_ty.into_iter().collect();
    let signature = Signature { params: param_types, returns };

    // Convert each basic block.
    // Trust: std HashMap required by LirFunction API contract (trust_cg-lower).
    // Keys are Block(u32). Consumers use block_order or sorted keys when order matters.
    #[allow(rustc::default_hash_types)]
    let mut blocks = std::collections::HashMap::with_capacity(body.blocks.len());
    // Trust: lower (and lay out) the blocks in reverse postorder of the CFG, not in MIR block
    // numbering. A block with a single predecessor takes that predecessor's EXIT values, which
    // only exist once the predecessor has been lowered; MIR numbering does not guarantee that
    // (after MIR inlining the return block can be numbered before the block that defines the
    // return place). Lowering in numbering order then handed such a block `initial_local_values`:
    // an undefined placeholder (instruction selection failed: "value Value(N) not defined before
    // use") or, for a reassigned parameter, the STALE parameter value. Reverse postorder lowers
    // every reachable single-predecessor block after its predecessor, so SSA local values flow
    // correctly. Locals that need memory do not depend on the order either: each has one slot
    // allocated above and kept current at every definition (docs/issues/2026-09-29-trust-cg-
    // mir-address-taken-locals-across-sibling-blocks.md, FIXED). trust-cg re-derives its own
    // layout (`layout_order`) from the CFG, starting at `entry_block` (the synthetic pre-entry
    // block below when there is one), so `block_order` here only orders unreachable blocks.
    let lowering_order = reverse_postorder_block_indices(body);
    let reachable = reachable_from_entry(body);
    let mut block_order: Vec<Block> =
        lowering_order.iter().map(|&i| Block(body.blocks[i].id.0 as u32)).collect();
    let mut block_entry_values =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    block_entry_values.insert(body.blocks[0].id.0, initial_local_values.clone());
    for &block_index in &lowering_order {
        let bb = &body.blocks[block_index];
        let block = Block(bb.id.0 as u32);
        let mut entry_values = block_start_values(
            bb.id.0,
            reachable[block_index],
            &predecessors,
            &block_entry_values,
            &initial_local_values,
        )?;
        if let Some(params) = block_params.get(&bb.id.0) {
            for param in params {
                entry_values.insert(param.local, param.value);
            }
        }
        let params = block_params.get(&bb.id.0).map_or(&[][..], Vec::as_slice);
        let prologue_locals = if block_index == 0 && !entry_is_loop_target {
            entry_prologue_locals.as_slice()
        } else {
            &[][..]
        };
        let lir_block = lower_block(
            bb,
            &mut ctx,
            return_lowering,
            &entry_values,
            params,
            &block_params,
            prologue_locals,
        )?;
        for successor in terminator_successors(&bb.terminator) {
            if block_params.contains_key(&successor) {
                continue;
            }
            if predecessors.get(&successor).is_some_and(|preds| preds.len() == 1) {
                block_entry_values.insert(successor, ctx.local_values.clone());
            }
        }
        blocks.insert(block, lir_block);
    }

    for (block, lir_block) in std::mem::take(&mut ctx.pending_blocks) {
        block_order.push(block);
        blocks.insert(block, lir_block);
    }

    // Trust: If any Assert terminator needed a panic block, insert it now.
    // Panic blocks contain either the real rust panic lang-item call supplied
    // by the rustc adapter or a conservative abort for standalone synthetic
    // bridge use.
    for (action, panic_blk) in std::mem::take(&mut ctx.panic_blocks) {
        block_order.push(panic_blk);
        let instructions = panic_block_instructions(&mut ctx, &action);
        blocks.insert(panic_blk, LirBlock { params: vec![], instructions, source_locs: vec![] });
    }

    // SAFETY: body.blocks is non-empty (validated above).
    let source_entry = body.blocks[0].id.0;
    // Trust: an entry block that is a loop target carrying reassigned locals is a join with
    // block parameters (see `plan_block_params`). The function entry cannot pass them, so a
    // synthetic pre-entry block copies the function-entry values in and jumps there; it is
    // the LIR entry, and bb0 is reached only through jumps that fill its parameters. The same
    // block stores the memory-backed arguments of a looping entry into their slots (see
    // `entry_prologue_locals`), so those stores run once, not on every back edge.
    let entry_block = if block_params.contains_key(&source_entry)
        || (entry_is_loop_target && !entry_prologue_locals.is_empty())
    {
        let pre_entry = ctx.fresh_block();
        ctx.local_values = initial_local_values.clone();
        let mut instructions = Vec::new();
        for &local in &entry_prologue_locals {
            let value = ctx.local_value(local)?;
            ctx.store_memory_backed_definition(local, value, &mut instructions)?;
        }
        emit_block_param_copies(source_entry, &mut ctx, &mut instructions, &block_params)?;
        instructions.push(Instruction {
            opcode: Opcode::Jump { dest: Block(source_entry as u32) },
            args: vec![],
            results: vec![],
        });
        blocks.insert(pre_entry, LirBlock { params: vec![], instructions, source_locs: vec![] });
        block_order.insert(0, pre_entry);
        pre_entry
    } else {
        Block(source_entry as u32)
    };

    let consumed_symbolic = std::mem::take(&mut ctx.consumed_symbolic);

    Ok((
        LirFunction {
            name: name.to_string(),
            signature,
            blocks,
            block_order,
            param_pointee_types: Vec::new(),
            #[allow(rustc::default_hash_types)]
            trust_ir_origins: std::collections::HashMap::new(),
            entry_block,
            stack_slots: ctx.stack_slots,
            // Trust: #986 — preserve call-result types for ISel when the
            // producing opcode omits result type metadata.
            value_types: ctx.value_types,
            #[allow(rustc::default_hash_types)]
            pure_callees: std::collections::HashSet::new(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            // Trust: trust-cg 5300b401 pins the AAPCS64 hidden return-buffer (sret)
            // convention on the function (`abi_sret_param`) and on its direct callees
            // (`sret_arg_callees`). The bridge lowers no `ParamAttrs::sret` and never
            // reads it, so it can classify neither side; None/empty is that statement,
            // and it is byte-for-byte the convention trust-cg emitted before the pin.
            //
            // Trust (bridge-abi): that statement is FAITHFUL to the input and is NOT a
            // safety argument on its own — it says "no sret was declared", never "no
            // sret is required". On THIS lane (VerifiableFunction -> LIR) there is no
            // `trust_ir::Module` and therefore no `TargetInfo::struct_passing` to read,
            // so the consumer-side `struct_passing` admission lives where a policy
            // exists to read: `module_to_lir::admit_struct_passing_policy`, reached from
            // every `lower_module_to_lir*` entry point. What keeps THIS lane safe is the
            // rustc driver's MIR-frontend ABI validator
            // (`rustc_codegen_trust_cg::validate_codegen_instance_abi`, `EnumAbi::Refuse`),
            // which cross-checks every admitted parameter and the return against rustc's
            // real `PassMode` and never admits `PassMode::Indirect`. A consumer reaching
            // this entry point WITHOUT such a check has no sret story at all — see
            // `ModuleLirError::UnclassifiedAggregateAbi` for the shape of the guarantee
            // the Module lane now states explicitly.
            abi_sret_param: None,
            sret_arg_callees: Default::default(),
            // Trust: trust-cg de95c72d6 (L01-P5) adds the indirect half of that
            // convention, keyed by the LIR callee value. This lane never emits
            // `Opcode::CallIndirect` (grep: only `module_to_lir` does), so the
            // empty set is exact here, not conservative.
            sret_arg_indirect_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            // trust-cg Function carries per-function exception-handling info; the bridge does
            // not emit EH metadata yet — Default (empty) is the validated no-EH baseline.
            eh_info: Default::default(),
            // The typed-catch table goes with `eh_info`: no landing pad, no catch type index,
            // so the empty table is exact.
            eh_type_table: Default::default(),
            // trust-cg U10: a prologue stack-limit check is requested by the
            // producer's reserved function tags and acknowledged positively,
            // never inferred from a tag (`docs/u10-prologue-stack-limit.md`
            // §1). This lowering decodes no such tag, so it requests none.
            stack_limit: None,
            // trust-cg L03-P9: the target features a function may assume,
            // as an adapter ADMITTED them against its target vocabulary. This
            // lowering admits none, so ISel keeps the profile's baseline
            // instructions for every function, as it did before the field.
            target_features: Vec::new(),
        },
        consumed_symbolic,
    ))
}

// ---------------------------------------------------------------------------
// Block lowering
// ---------------------------------------------------------------------------

fn lower_block(
    bb: &TrustBlock,
    ctx: &mut LoweringCtx<'_>,
    return_lowering: ReturnLowering,
    entry_values: &FxHashMap<usize, Value>,
    params: &[BlockParam],
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
    prologue_locals: &[usize],
) -> Result<LirBlock, BridgeError> {
    ctx.local_values = entry_values.clone();
    ctx.current_block = bb.id.0;
    let mut instructions = Vec::new();

    // Entry block only: memory-backed locals that hold a value at function entry (the
    // arguments) start out in their slots, before anything can take their address.
    for &local in prologue_locals {
        let value = ctx.local_value(local)?;
        ctx.store_memory_backed_definition(local, value, &mut instructions)?;
    }

    // Lower each statement.
    for (stmt_index, stmt) in bb.stmts.iter().enumerate() {
        ctx.current_statement = stmt_index;
        lower_statement(stmt, ctx, &mut instructions)?;
    }

    // Lower the terminator. Entry-binding lowering is off in this position
    // (see `LoweringCtx::in_terminator`).
    ctx.in_terminator = true;
    let terminator_result =
        lower_terminator(&bb.terminator, ctx, &mut instructions, return_lowering, block_params);
    ctx.in_terminator = false;
    terminator_result?;

    Ok(LirBlock {
        params: params.iter().map(|param| (param.value, param.ty.clone())).collect(),
        instructions,
        source_locs: vec![],
    })
}

// ---------------------------------------------------------------------------
// Statement lowering
// ---------------------------------------------------------------------------

fn lower_statement(
    stmt: &Statement,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    match stmt {
        Statement::Assign { place, rvalue, span: _ } => {
            lower_rvalue(place, rvalue, ctx, instructions)?;
        }
        Statement::SetDiscriminant { place, variant_index } => {
            lower_set_discriminant(place, *variant_index, ctx, instructions)?;
        }
        // Trust: #966 — no-op metadata/lifetime statements produce no LIR instructions.
        Statement::Nop
        | Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Retag { .. } => {}
        // `Deinit` makes the place uninitialized: leaving its bytes as they
        // are is one of the values an uninitialized place may hold, and no
        // later read may observe it before a write re-initializes the place.
        Statement::Deinit { .. } => {}
        // `assume(c)` has no effect on any place: a false `c` is UB, so the
        // program that ignores it refines every program that honours it. It
        // is the only intrinsic the extractor spells as `Intrinsic`
        // (`trust-mir-extract` `convert_nondiverging_intrinsic`); any other
        // name may write memory and is refused, never dropped.
        Statement::Intrinsic { name, .. } if name == "assume" => {}
        Statement::Intrinsic { name, .. } => {
            return Err(BridgeError::UnsupportedOp(format!(
                "intrinsic statement `{name}` has no lowering"
            )));
        }
        Statement::CopyNonOverlapping { src, dst, count, elem_ty, .. } => {
            lower_copy_nonoverlapping(src, dst, count, elem_ty, ctx, instructions)?;
        }
        // Trust (ticket 216 cg-bridge, review 5): the sentinel's own contract
        // is "downstream must fail closed", and a new `Statement` variant may
        // write memory (a memory-backed local written that way would keep its
        // old value). Both were a silent no-op here.
        Statement::Unsupported { kind, detail, .. } => {
            return Err(BridgeError::UnsupportedOp(format!(
                "unsupported MIR statement `{kind}`: {detail}"
            )));
        }
        other => {
            return Err(BridgeError::UnsupportedOp(format!(
                "MIR statement has no lowering: {other:?}"
            )));
        }
    }
    Ok(())
}

/// `copy_nonoverlapping::<T>(src, dst, count)`: a write through `dst` of
/// `count * size_of::<T>()` bytes read through `src` — a `Memcpy`, the same
/// byte copy every whole-aggregate write is. A local that `dst` points at had
/// its address taken, so it is memory-backed (`collect_memory_backed_locals`)
/// and every later read loads the copy. The byte count is exact: a constant
/// count is multiplied here
/// (checked), a runtime one by an `Imul` (Rust's precondition makes the
/// product fit `isize`).
fn lower_copy_nonoverlapping(
    src: &Operand,
    dst: &Operand,
    count: &Operand,
    elem_ty: &Ty,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    let elem_bytes = u64::from(map_lowering_type(elem_ty)?.bytes());
    let src = ctx.resolve_operand(src, instructions)?;
    let dst = ctx.resolve_operand(dst, instructions)?;
    let len = match count {
        Operand::Constant(ConstValue::Uint(n, _)) => {
            let bytes = u64::try_from(*n).ok().and_then(|n| n.checked_mul(elem_bytes)).ok_or_else(
                || {
                    BridgeError::UnsupportedOp(format!(
                        "copy_nonoverlapping of {n} x {elem_bytes} bytes overflows u64"
                    ))
                },
            )?;
            emit_iconst(ctx, instructions, LirType::I64, carrier_imm(bytes)?)
        }
        _ => {
            let count = ctx.resolve_operand(count, instructions)?;
            let size = emit_iconst(ctx, instructions, LirType::I64, carrier_imm(elem_bytes)?);
            let len = ctx.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::Imul,
                args: vec![count, size],
                results: vec![len],
            });
            len
        }
    };
    instructions.push(Instruction {
        opcode: Opcode::Memcpy,
        args: vec![dst, src, len],
        results: vec![],
    });
    Ok(())
}

fn lower_set_discriminant(
    place: &Place,
    variant_index: usize,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    let place_ty = ctx.place_ty(place)?;
    // A declared struct or union has no slot (`flat_enum_tag_slot`), and this
    // REFUSES it rather than lowering it as the no-op rustc's
    // `codegen_set_discr` makes of variant 0 on a single-variant layout: there
    // is nothing to write, a variant other than 0 would be invalid MIR, and
    // before the one slot rule this wrote the declared value into the struct's
    // field spelled `tag` — its DATA. Refusing costs only a shape no MIR here
    // needs; a silent no-op would hide a producer that thinks it has a slot.
    let (field_index, field_ty) = explicit_discriminant_field(&place_ty, "SetDiscriminant")?;
    // Trust (ticket 216 cg-bridge): the slot takes the target variant's DECLARED
    // discriminant — the value MIR's `SwitchInt` over `discriminant(place)`
    // compares against — never its index.
    let (tag_lir_ty, tag_imm) =
        declared_tag_lir_const(&place_ty, &field_ty, variant_index, "SetDiscriminant")?;

    let mut tag_place = place.clone();
    tag_place.projections.push(Projection::Field(field_index));
    let tag_addr = ctx.resolve_place_addr(&tag_place, instructions)?;
    let tag_value = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty: tag_lir_ty.clone(), imm: tag_imm },
        args: vec![],
        results: vec![tag_value],
    });
    push_store(instructions, tag_lir_ty, tag_value, tag_addr);
    Ok(())
}

/// Trust (ticket 216 cg-bridge): the field SPELLED as a tag slot — `discriminant`,
/// `__discriminant`, `tag` or `__tag`, at ANY index (the MIR extractor mints
/// `__tag` at index 0; other shapes carry it elsewhere). Only a flat enum's such
/// field IS a slot: every site asks [`flat_enum_tag_slot`], never this.
fn flat_tag_field_index(fields: &[(String, Ty)]) -> Option<usize> {
    fields.iter().position(|(field_name, _)| {
        matches!(field_name.as_str(), "discriminant" | "__discriminant" | "tag" | "__tag")
    })
}

/// A `Ty::Adt` DECLARED a struct or union: it has one variant and no
/// discriminant slot, whatever its fields are spelled.
fn is_declared_struct_or_union(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Adt { adt_kind: Some(trust_types::AdtKind::Struct | trust_types::AdtKind::Union), .. }
    )
}

/// Trust (ticket 216 cg-bridge): THE slot rule — the tag slot of `ty` when `ty`
/// is a FLAT ENUM, an ADT carrying a field spelled as a slot
/// ([`flat_tag_field_index`]) that is not a declared struct or union (a
/// struct's field spelled `tag` is data). All three sites that touch the slot —
/// `Aggregate` construction, `SetDiscriminant` and the `Discriminant` read
/// (through [`explicit_discriminant_field`]) — and the payload-lane resolver
/// ([`flat_variant_lane`]) ask this one predicate, so they can never disagree
/// on whether, or where, a slot exists.
fn flat_enum_tag_slot(ty: &Ty) -> Option<usize> {
    match ty {
        _ if is_declared_struct_or_union(ty) => None,
        Ty::Adt { fields, .. } => flat_tag_field_index(fields),
        _ => None,
    }
}

/// Trust (ticket 216 cg-bridge, review of 95382e6164): THE payload-lane lookup
/// of a flat enum, shared by the aggregate writer and the `Downcast(v) +
/// Field(k)` projection in `place_ty`, `resolve_place` and
/// `resolve_place_addr`, so a payload is read and written through the SAME
/// field. `ty` must be the flat enum itself.
///
/// The MIR extractor (`trust_mir_extract::ty_convert::lower_enum_adt`) lays a
/// flat enum out as `__tag` followed by one `__v{v}_{name}` field per variant
/// field, `name` being the variant descriptor's own field name. Field `k` of
/// variant `v` is the flat field spelled `__v{v}_{variants[v].fields[k].0}`.
///
/// `Ok(None)`: `ty` is not a flat enum ([`flat_enum_tag_slot`]); its fields are
/// positional (a struct, a tuple-like ADT with no slot) and the caller keeps its
/// positional rule. Fails closed — never guesses a field by position — when a
/// flat enum carries no descriptor, the descriptor has no such variant or field,
/// or the lane is missing: before this, the writer took the `k`-th non-slot
/// field (`Err(5)` of `Result<u64, u64>` wrote `Ok`'s lane) and the reader
/// treated `Downcast` as type-only (`(r as Err).0` read flat field 0, the tag).
fn flat_variant_lane(
    ty: &Ty,
    variant_index: usize,
    field_index: usize,
    site: &str,
) -> Result<Option<(usize, Ty)>, BridgeError> {
    if flat_enum_tag_slot(ty).is_none() {
        return Ok(None);
    }
    let Ty::Adt { name, fields, variants, .. } = ty else {
        return Ok(None);
    };
    if variants.is_empty() {
        return Err(BridgeError::UnsupportedOp(format!(
            "{site}: field {field_index} of variant {variant_index} of `{name}`, which carries \
             no variant descriptor: its payload lane is unknown"
        )));
    }
    let variant = variants.get(variant_index).ok_or_else(|| {
        BridgeError::UnsupportedOp(format!(
            "{site} names variant {variant_index}, which the variant descriptor of `{name}` \
             does not have"
        ))
    })?;
    let (variant_field_name, _) = variant.fields.get(field_index).ok_or_else(|| {
        BridgeError::UnsupportedOp(format!(
            "{site}: variant {variant_index} (`{}`) of `{name}` has {} field(s), no field \
             {field_index}",
            variant.name,
            variant.fields.len()
        ))
    })?;
    let mut prefix_buf = [0u8; 32];
    let prefix = {
        use std::io::Write;
        let mut cursor = &mut prefix_buf[..];
        let _ = write!(cursor, "__v{variant_index}_");
        let len = 32 - cursor.len();
        std::str::from_utf8(&prefix_buf[..len]).unwrap_or("")
    };
    let flat_index = fields
        .iter()
        .position(|(field_name, _)| {
            field_name.strip_prefix(prefix) == Some(variant_field_name.as_str())
        })
        .ok_or_else(|| {
            let lane = format!("__v{variant_index}_{variant_field_name}");
            let field_list = fields
                .iter()
                .map(|(field_name, _)| field_name.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            BridgeError::UnsupportedOp(format!(
                "{site}: field {field_index} of variant {variant_index} of `{name}` lives in \
                 lane `{lane}`, which the flat layout does not have; fields=[{field_list}]"
            ))
        })?;
    Ok(Some((flat_index, fields[flat_index].1.clone())))
}

/// The flat field a `Field(field_index)` projection addresses on `current_ty`,
/// and its type. Under a `Downcast(v)` of a flat enum that is variant `v`'s
/// payload lane ([`flat_variant_lane`]); otherwise the positional field.
fn projected_field(
    current_ty: &Ty,
    downcast: Option<usize>,
    field_index: usize,
    site: &str,
) -> Result<(usize, Ty), BridgeError> {
    if let Some(variant_index) = downcast
        && let Some(lane) = flat_variant_lane(current_ty, variant_index, field_index, site)?
    {
        return Ok(lane);
    }
    Ok((field_index, field_type(current_ty, field_index)?))
}

/// A `Downcast` of a flat enum names a variant only for the `Field` that follows
/// it. Any other projection after it would address the flat layout as if it
/// were the variant's, so it is refused rather than guessed.
fn check_downcast_followed_by_field(
    current_ty: &Ty,
    downcast: Option<usize>,
    projection: &Projection,
) -> Result<(), BridgeError> {
    if let Some(variant_index) = downcast
        && !matches!(projection, Projection::Field(_))
        && flat_enum_tag_slot(current_ty).is_some()
    {
        return Err(BridgeError::UnsupportedOp(format!(
            "Downcast({variant_index}) of flat enum {current_ty:?} is followed by \
             {projection:?}, not a Field: the variant's payload lane is unaddressable"
        )));
    }
    Ok(())
}

/// The tag slot of `ty` ([`flat_enum_tag_slot`]) and its type, which must be
/// `bool` or an integer. `site` names the caller in the refusal. A declared
/// struct or union has no slot and is refused by name: before the one slot rule,
/// `SetDiscriminant` and the `Discriminant` read took its field spelled `tag`
/// for one, writing into and reading back DATA.
fn explicit_discriminant_field(ty: &Ty, site: &str) -> Result<(usize, Ty), BridgeError> {
    let Ty::Adt { name, fields, .. } = ty else {
        return Err(BridgeError::UnsupportedOp(format!(
            "{site} is modeled only for tagged ADTs with an explicit discriminant/tag field, got {ty:?}"
        )));
    };
    if is_declared_struct_or_union(ty) {
        return Err(BridgeError::UnsupportedOp(format!(
            "{site} on `{name}`, a declared struct/union: it has no discriminant slot (a field \
             spelled `tag` is data)"
        )));
    }

    let Some(field_index) = flat_enum_tag_slot(ty) else {
        let field_list =
            fields.iter().map(|(field_name, _)| field_name.as_str()).collect::<Vec<_>>().join(", ");
        return Err(BridgeError::UnsupportedOp(format!(
            "ADT `{name}` has no explicit discriminant/tag field for {site}; fields=[{field_list}]"
        )));
    };
    let (field_name, field_ty) = &fields[field_index];

    if !matches!(field_ty, Ty::Bool | Ty::Int { .. }) {
        return Err(BridgeError::UnsupportedOp(format!(
            "ADT `{name}` discriminant/tag field `{field_name}` has type {field_ty:?}; expected bool or integer"
        )));
    }

    Ok((field_index, field_ty.clone()))
}

/// Trust (ticket 216 cg-bridge): the LIR constant the tag slot (of type
/// `field_ty`) of the flat enum `adt_ty` holds for `variant_index` — the DECODED
/// DECLARED discriminant, `Ty::variant_tag`, never the variant index. MIR's
/// `SwitchInt` over `discriminant(e)` compares against declared values, so for
/// `enum E { A = 5, B = 9 }` an index write (`E::B` as 1) takes the wrong arm:
/// in this CODEGEN lane that is a miscompile, not a proof gap.
///
/// Fails closed where the value is not known exactly:
/// * the ADT carries NO variant descriptor. `Ty::variant_tag` answers the index
///   for such an ADT (the verification lane's convention, whose readers agree
///   with it); here the index is only a guess at the declared value, and a wrong
///   guess ships a wrong branch;
/// * the descriptor has no variant `variant_index`;
/// * the declared value does not fit the slot (`Ty::flat_tag_fits`), or has no
///   exact LIR immediate (a negative or above-`i64::MAX` tag in a wider-than-64
///   slot).
fn declared_tag_lir_const(
    adt_ty: &Ty,
    field_ty: &Ty,
    variant_index: usize,
    site: &str,
) -> Result<(LirType, i64), BridgeError> {
    let Ty::Adt { name, variants, .. } = adt_ty else {
        return Err(BridgeError::UnsupportedOp(format!(
            "{site} writes a discriminant into a non-ADT type {adt_ty:?}"
        )));
    };
    if variants.is_empty() {
        return Err(BridgeError::UnsupportedOp(format!(
            "{site} writes the tag of variant {variant_index} of `{name}`, which carries no \
             variant descriptor: its declared discriminant is unknown, and the variant index \
             is only a guess at it"
        )));
    }
    let tag = adt_ty.variant_tag(variant_index).ok_or_else(|| {
        BridgeError::UnsupportedOp(format!(
            "{site} names variant {variant_index}, which the variant descriptor of `{name}` \
             does not have"
        ))
    })?;
    if !field_ty.flat_tag_fits(tag) {
        return Err(BridgeError::UnsupportedOp(format!(
            "{site}: discriminant {tag} of variant {variant_index} of `{name}` does not fit its \
             {field_ty:?} discriminant/tag field"
        )));
    }
    match field_ty {
        // `flat_tag_fits` admitted exactly {0, 1}.
        Ty::Bool => Ok((LirType::B1, i64::from(tag == 1))),
        Ty::Int { width, signed } => {
            let imm = if *width <= 64 {
                // In range for the slot, so exact: a signed tag is its own i64,
                // an unsigned one its u64 pattern.
                if *signed { tag as i64 } else { tag as u64 as i64 }
            } else {
                i64::try_from(tag).ok().filter(|value| *value >= 0).ok_or_else(|| {
                    BridgeError::UnsupportedOp(format!(
                        "{site}: discriminant {tag} of variant {variant_index} of `{name}` has \
                         no exact i64 immediate for its {width}-bit tag field"
                    ))
                })?
            };
            Ok((map_type(field_ty)?, imm))
        }
        other => Err(BridgeError::UnsupportedOp(format!(
            "discriminant/tag field type {other:?} is not modeled as bool or integer"
        ))),
    }
}

/// Helper: assign a computed value to a destination place.
///
/// For simple locals, updates the local_values map (and, for a memory-backed
/// local, stores into its slot). For projected places, computes the address and
/// emits a Store instruction.
fn assign_to_place(
    dest: &Place,
    value: Value,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    // An aggregate is copied FROM its value, so the value must be the address of its bytes
    // (`LoweringCtx::emit_checked_store`); a direct local whose type has no LIR lowering keeps
    // the SSA binding it always had.
    if let Ok(ty) = map_lowering_type(&ctx.place_ty(dest)?)
        && ty.is_aggregate()
        && !ctx.aggregate_carriers.contains(&value)
    {
        return Err(BridgeError::UnsupportedOp(format!(
            "a write of aggregate type {ty:?} to {dest:?} needs the address of the value's \
             bytes; {value:?} does not carry one"
        )));
    }
    if place_is_direct_local(dest) {
        ctx.local_values.insert(dest.local, value);
        ctx.store_memory_backed_definition(dest.local, value, instructions)?;
    } else {
        let addr = ctx.resolve_place_addr(dest, instructions)?;
        let ty = map_lowering_type(&ctx.place_ty(dest)?)?;
        ctx.emit_store_value(ty, value, addr, instructions);
    }
    Ok(())
}

fn lower_rvalue(
    dest: &Place,
    rvalue: &Rvalue,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    let dest_val = ctx.fresh_value();

    match rvalue {
        Rvalue::Use(operand) => {
            let src = ctx.resolve_operand(operand, instructions)?;
            assign_to_place(dest, src, ctx, instructions)?;
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let value_ty = ctx.place_ty(dest)?;
            let (lhs_val, rhs_val) =
                ctx.resolve_binop_operands(*op, lhs, rhs, &value_ty, instructions)?;
            if let Some(fat_ty) = carried_operand_ty(ctx, *op, &[lhs, rhs])? {
                return lower_fat_pointer_compare(
                    dest,
                    *op,
                    &fat_ty,
                    lhs_val,
                    rhs_val,
                    ctx,
                    instructions,
                );
            }

            // Trust: #828 — lower three-way compare as nested selects over lt/gt tests.
            if *op == BinOp::Cmp {
                let (lt_cond, gt_cond) = cmp_int_conditions(ctx, lhs, rhs)?;
                let lt_cmp = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp { cond: lt_cond },
                    args: vec![lhs_val, rhs_val],
                    results: vec![lt_cmp],
                });
                let neg_one = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: -1 },
                    args: vec![],
                    results: vec![neg_one],
                });
                let gt_cmp = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp { cond: gt_cond },
                    args: vec![lhs_val, rhs_val],
                    results: vec![gt_cmp],
                });
                let one = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: 1 },
                    args: vec![],
                    results: vec![one],
                });
                let zero = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: 0 },
                    args: vec![],
                    results: vec![zero],
                });
                let step1 = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Select { cond: IntCC::NotEqual },
                    args: vec![gt_cmp, one, zero],
                    results: vec![step1],
                });
                let result = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Select { cond: IntCC::NotEqual },
                    args: vec![lt_cmp, neg_one, step1],
                    results: vec![result],
                });
                assign_to_place(dest, result, ctx, instructions)?;
                return Ok(());
            }

            // An operand's float-ness is its PLACE's type: `t.0 + t.1` on
            // `t: (f64, f64)` is a float add, whatever the tuple is.
            let lhs_is_float = match lhs {
                Operand::Copy(place) | Operand::Move(place) => ctx.place_ty(place)?.is_float(),
                Operand::Constant(ConstValue::Float(_)) => true,
                _ => false,
            };
            let rhs_is_float = match rhs {
                Operand::Copy(place) | Operand::Move(place) => ctx.place_ty(place)?.is_float(),
                Operand::Constant(ConstValue::Float(_)) => true,
                _ => false,
            };
            if lhs_is_float || rhs_is_float {
                let opcode = map_float_binop(*op)?;
                instructions.push(Instruction {
                    opcode,
                    args: vec![lhs_val, rhs_val],
                    results: vec![dest_val],
                });
                assign_to_place(dest, dest_val, ctx, instructions)?;
                return Ok(());
            }

            // Trust: signedness for relational comparisons (Eq/Ne/Lt/Le/Gt/Ge)
            // must come from the OPERAND types, not the destination. The
            // destination of a comparison is a `bool`, whose `is_signed` is
            // false, which would otherwise select unsigned condition codes
            // (e.g. `x < 0` -> `x <u 0`, vacuously false) and miscompile
            // signed comparisons. Division/shift/etc. still take signedness
            // from the destination value's type: the destination PLACE's
            // (`t.0 = x / 2` on `t: (i64, u64)` divides signed).
            let signed = match op {
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    cmp_operand_ty(ctx, lhs, rhs)?.is_signed()
                }
                _ => ctx.place_ty(dest)?.is_signed(),
            };
            let opcode = map_binop(*op, signed)?;

            instructions.push(Instruction {
                opcode,
                args: vec![lhs_val, rhs_val],
                results: vec![dest_val],
            });
            assign_to_place(dest, dest_val, ctx, instructions)?;
        }
        // Trust: #828 — CheckedBinaryOp produces a (result, overflow_flag) tuple.
        // Compute the narrow wrapping result, then derive the overflow flag
        // with a sound per-op check on the checked value type.
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            if carried_operand_ty(ctx, *op, &[lhs, rhs])?.is_some() {
                return Err(BridgeError::UnsupportedOp(format!(
                    "checked {op:?} of a fat pointer operand has no meaning"
                )));
            }
            let value_ty = checked_binary_value_ty(ctx, dest)?;
            let (lhs_val, rhs_val) =
                ctx.resolve_binop_operands(*op, lhs, rhs, &value_ty, instructions)?;
            if value_ty.is_float() {
                return Err(BridgeError::UnsupportedOp(format!(
                    "checked floating-point binary op not supported: {op:?}"
                )));
            }
            let value_lir_ty = map_type(&value_ty)?;
            let signed = value_ty.is_signed();
            let opcode = map_binop(*op, signed)?;
            let arith_result = ctx.fresh_value();
            instructions.push(Instruction {
                opcode,
                args: vec![lhs_val, rhs_val],
                results: vec![arith_result],
            });
            let overflow_val = lower_checked_overflow_flag(
                ctx,
                instructions,
                CheckedOverflowFlagInput {
                    op: *op,
                    rhs,
                    lhs_val,
                    rhs_val,
                    arith_result,
                    value_ty: &value_ty,
                    value_lir_ty: &value_lir_ty,
                },
            )?;

            // Build the (result, overflow) tuple in the destination (both operands are
            // already read), typed as the DESTINATION place (`built_dest_ty`), not its base
            // local.
            let dest_ty = built_dest_ty(ctx, dest)?;
            let lir_ty = map_type(&dest_ty)?;
            let base_ptr = constructor_dest_addr(ctx, dest, "CheckedBinaryOp", instructions)?;

            // Store field 0: arithmetic result.
            let field0_ptr = ctx.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::StructGep { struct_ty: lir_ty.clone(), field_index: 0 },
                args: vec![base_ptr],
                results: vec![field0_ptr],
            });
            push_store(instructions, value_lir_ty.clone(), arith_result, field0_ptr);

            // Store field 1: overflow flag.
            let field1_ptr = ctx.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::StructGep { struct_ty: lir_ty.clone(), field_index: 1 },
                args: vec![base_ptr],
                results: vec![field1_ptr],
            });
            push_store(instructions, LirType::B1, overflow_val, field1_ptr);

            bind_constructed(ctx, dest, base_ptr);
        }
        Rvalue::UnaryOp(op, operand) => {
            // Trust: #828 — PtrMetadata extracts the metadata lane from fat pointers.
            if *op == UnOp::PtrMetadata {
                let src = ctx.resolve_operand(operand, instructions)?;
                let src_ty = operand_ty(ctx, operand)?;

                if let Some(reason) = ptr_metadata_support_error(&src_ty) {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "PtrMetadata for {src_ty:?} is not supported: {reason}"
                    )));
                }

                if slice_element_type(&src_ty).is_some() {
                    let metadata = ctx.emit_slice_metadata(src, &src_ty, instructions)?;
                    assign_to_place(dest, metadata, ctx, instructions)?;
                } else if src_ty.is_pointer_like() {
                    let zero = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: 0 },
                        args: vec![],
                        results: vec![zero],
                    });
                    assign_to_place(dest, zero, ctx, instructions)?;
                } else {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "PtrMetadata requires a pointer-like operand; got {src_ty:?}"
                    )));
                }

                return Ok(());
            }

            if let Some(ty) = direct_operand_ty(ctx, operand)?
                && is_carried_ty(&ty)
            {
                return Err(BridgeError::UnsupportedOp(format!(
                    "{op:?} of an aggregate or fat pointer operand ({ty:?}): the operand is \
                     carried by the address of its bytes, and {op:?} would act on that address"
                )));
            }
            let src = ctx.resolve_operand(operand, instructions)?;
            // Trust: a MIR `Not` on a `bool` is a one-bit complement. `Bnot` is a full-width
            // bitwise NOT (`mvn` on AArch64), so on a 0/1 value it yields 0xFF..FF / 0xFF..FE
            // (for 0 / 1) instead of 1 / 0 and every consumer of the bool reads garbage. Lower it as
            // `Bxor(x, 1)` on the B1 value; every integer width keeps `Bnot` (measured correct:
            // the width is re-established where the value is consumed).
            if *op == UnOp::Not && matches!(operand_ty(ctx, operand)?, Ty::Bool) {
                let one = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::B1, imm: 1 },
                    args: vec![],
                    results: vec![one],
                });
                instructions.push(Instruction {
                    opcode: Opcode::Bxor,
                    args: vec![src, one],
                    results: vec![dest_val],
                });
            } else {
                let opcode = map_unop(*op)?;
                instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
            }
            assign_to_place(dest, dest_val, ctx, instructions)?;
        }
        // Trust: #828 — Cast handles int-to-int, float-to-int, int-to-float,
        // float-to-float, and pointer-to-pointer conversions.
        Rvalue::Cast(operand, target_ty) => {
            let src = ctx.resolve_operand(operand, instructions)?;

            // The source's type is its PLACE's: `t.0 as u64` on `t: (i8, u8)`
            // widens an i8 by sign, whatever the tuple is.
            let src_place_ty = match operand {
                Operand::Copy(p) | Operand::Move(p) => Some(ctx.place_ty(p)?),
                _ => None,
            };
            let src_ty = src_place_ty.as_ref();
            // Slice fat pointers are carried by the address of their two words
            // (`is_carried_ty`). A cast between two of them copies both words; a cast to a
            // thin pointer keeps the data word; an unsizing cast of `*const [T; N]` builds
            // the pair `(data, N)`. Before ticket 216 cg review 5 all three were a no-op on
            // a one-word value, so the length was whatever the carrier held.
            let src_elem = src_ty.and_then(slice_element_type);
            if let Some(target_elem) = slice_element_type(target_ty) {
                if src_elem.is_some() {
                    assign_to_place(dest, src, ctx, instructions)?;
                    return Ok(());
                }
                let unsized_from = src_ty.and_then(|ty| match ty {
                    Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
                        match inner.as_ref() {
                            Ty::Array { elem, len } if **elem == target_elem => Some(*len),
                            _ => None,
                        }
                    }
                    _ => None,
                });
                let Some(len) = unsized_from else {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "cast of {src_ty:?} to slice fat pointer {target_ty:?} has no length to \
                         carry"
                    )));
                };
                let len = emit_iconst(ctx, instructions, LirType::I64, carrier_imm(len)?);
                let fat_ptr = ctx.emit_slice_fat_pointer(&target_elem, src, len, instructions)?;
                assign_to_place(dest, fat_ptr, ctx, instructions)?;
                return Ok(());
            }
            if let (Some(src_ty), Some(_)) = (src_ty, src_elem.as_ref())
                && target_ty.is_pointer_like()
                && !is_carried_ty(target_ty)
            {
                let data = ctx.emit_slice_data_ptr(src, src_ty, instructions)?;
                assign_to_place(dest, data, ctx, instructions)?;
                return Ok(());
            }
            // An aggregate operand is its carrier (an address): a cast to any
            // other type would reinterpret the ADDRESS, not the bytes.
            if src_ty.is_some_and(is_carried_ty) && src_ty != Some(target_ty) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "cast of aggregate {src_ty:?} to {target_ty:?} is not supported"
                )));
            }

            let src_is_float = src_ty.is_some_and(|t| t.is_float());
            let dst_is_float = target_ty.is_float();
            let src_is_ptr = src_ty.is_some_and(|t| t.is_pointer_like());
            let dst_is_ptr = target_ty.is_pointer_like();

            if src_is_float && !dst_is_float {
                // Trust: Float-to-Int conversion (FcvtToInt / FcvtToUint).
                let dst_ty = map_type(target_ty)?;
                let signed = target_ty.is_signed();
                let opcode = if signed {
                    Opcode::FcvtToInt { dst_ty }
                } else {
                    Opcode::FcvtToUint { dst_ty }
                };
                instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
                assign_to_place(dest, dest_val, ctx, instructions)?;
            } else if !src_is_float && dst_is_float {
                // Trust: Int-to-Float conversion (FcvtFromInt / FcvtFromUint).
                let src_lir_ty = src_ty.map(map_type).transpose()?.unwrap_or(LirType::I32);
                let signed = src_ty.is_some_and(|t| t.is_signed());
                let opcode = if signed {
                    Opcode::FcvtFromInt { src_ty: src_lir_ty }
                } else {
                    Opcode::FcvtFromUint { src_ty: src_lir_ty }
                };
                instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
                assign_to_place(dest, dest_val, ctx, instructions)?;
            } else if src_is_float && dst_is_float {
                // Trust: Float-to-Float conversion (FPExt / FPTrunc).
                let src_width = src_ty.and_then(|t| match t {
                    Ty::Float { width } => Some(*width),
                    _ => None,
                });
                let dst_width = match target_ty {
                    Ty::Float { width } => Some(*width),
                    _ => None,
                };
                match (src_width, dst_width) {
                    (Some(sw), Some(dw)) if sw < dw => {
                        // Widen: f32 -> f64
                        instructions.push(Instruction {
                            opcode: Opcode::FPExt,
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    (Some(sw), Some(dw)) if sw > dw => {
                        // Narrow: f64 -> f32
                        instructions.push(Instruction {
                            opcode: Opcode::FPTrunc,
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    _ => {
                        // Same width or unknown: passthrough.
                        assign_to_place(dest, src, ctx, instructions)?;
                    }
                }
            } else if src_is_ptr && dst_is_ptr {
                // Trust: Ptr-to-Ptr cast. Both are I64 in our representation,
                // so this is a no-op bitcast.
                assign_to_place(dest, src, ctx, instructions)?;
            } else {
                // Int-to-Int cast (original logic).
                let src_width = src_ty.and_then(LoweringCtx::ty_bit_width);
                let dst_width = LoweringCtx::ty_bit_width(target_ty);

                match (src_width, dst_width) {
                    (Some(sw), Some(dw)) if sw == dw => {
                        assign_to_place(dest, src, ctx, instructions)?;
                    }
                    (Some(sw), Some(dw)) if sw > dw => {
                        let to_ty = map_type(target_ty)?;
                        instructions.push(Instruction {
                            opcode: Opcode::Trunc { to_ty },
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    (Some(_), Some(_)) => {
                        let from_ty = src_ty.map(map_type).transpose()?.unwrap_or(LirType::I32);
                        let to_ty = map_type(target_ty)?;
                        let signed = src_ty.is_some_and(|t| t.is_signed());
                        let opcode = if signed {
                            Opcode::Sextend { from_ty, to_ty }
                        } else {
                            Opcode::Uextend { from_ty, to_ty }
                        };
                        instructions.push(Instruction {
                            opcode,
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    _ => {
                        assign_to_place(dest, src, ctx, instructions)?;
                    }
                }
            }
        }
        Rvalue::Discriminant(place) => {
            // Trust (ticket 216 cg-bridge): read the tag slot the writers write
            // (`flat_enum_tag_slot`, any index), at the slot's OWN width, then
            // widen it by the slot's sign (or narrow it) to the destination's
            // discriminant type. The old read was `StructGep(0) + Load(I64)`
            // whatever the slot: an i8/u8/i32 tag read 8 bytes (the slot plus
            // whatever followed it), a negative narrow tag was never
            // sign-extended, and a slot at another index was never read at all.
            // The place is resolved with its projections, so `discriminant(*r)`
            // reads through the reference instead of treating `r` as the enum.
            let place_ty = ctx.place_ty(place)?;
            let dest_ty = ctx.place_ty(dest)?;
            if !matches!(dest_ty, Ty::Int { .. }) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "Discriminant destination must be an integer, got {dest_ty:?}"
                )));
            }
            let dest_lir_ty = map_type(&dest_ty)?;
            // A DECLARED struct or union has no slot (`flat_enum_tag_slot`): its
            // discriminant is 0, rustc's `discriminant_value` for every
            // non-enum type (a single-variant layout reads its variant, 0).
            // MIR spells it when `mem::discriminant::<T>` is instantiated at a
            // struct. Before the one slot rule this read took a struct field
            // spelled `tag` for a slot and returned that field's DATA. An ADT
            // not declared a struct/union and carrying no slot stays refused
            // (`explicit_discriminant_field`): it may be an enum whose slot the
            // lane cannot see, and 0 would then be a guess.
            if is_declared_struct_or_union(&place_ty) {
                let zero = emit_iconst(ctx, instructions, dest_lir_ty, 0);
                assign_to_place(dest, zero, ctx, instructions)?;
                return Ok(());
            }
            if is_fieldless_adt(&place_ty) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "fieldless ADT discriminant has no trustworthy LIR layout: {place_ty:?}"
                )));
            }
            let (tag_index, tag_ty) = explicit_discriminant_field(&place_ty, "Discriminant")?;
            let tag_lir_ty = map_type(&tag_ty)?;
            let mut tag_place = place.clone();
            tag_place.projections.push(Projection::Field(tag_index));
            let tag_addr = ctx.resolve_place_addr(&tag_place, instructions)?;
            let loaded = ctx.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::Load { ty: tag_lir_ty.clone(), align: None },
                args: vec![tag_addr],
                results: vec![loaded],
            });
            let tag_is_signed = matches!(tag_ty, Ty::Int { signed: true, .. });
            let value =
                emit_int_cast(ctx, instructions, loaded, &tag_lir_ty, &dest_lir_ty, tag_is_signed)?;
            assign_to_place(dest, value, ctx, instructions)?;
        }
        Rvalue::Len(place) => {
            // Len: for slices, load the length field (field 1 of the fat pointer).
            // For arrays, emit a constant with the known length.
            let place_ty = ctx.place_ty(place)?;
            match &place_ty {
                Ty::Array { len, .. } => {
                    let len_val = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: *len as i64 },
                        args: vec![],
                        results: vec![len_val],
                    });
                    assign_to_place(dest, len_val, ctx, instructions)?;
                }
                ty if slice_element_type(ty).is_some() => {
                    let src = ctx.resolve_place(place, instructions)?;
                    let len = ctx.emit_slice_metadata(src, ty, instructions)?;
                    assign_to_place(dest, len, ctx, instructions)?;
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "Len on non-array/slice type: {other:?}"
                    )));
                }
            }
        }
        Rvalue::Ref { place, .. } => {
            // Create a reference: compute the address of the place.
            let addr = ctx.resolve_place_addr(place, instructions)?;
            assign_to_place(dest, addr, ctx, instructions)?;
        }
        Rvalue::AddressOf(_mutable, place) => {
            // Raw address-of: compute the address of the place.
            let addr = ctx.resolve_place_addr(place, instructions)?;
            assign_to_place(dest, addr, ctx, instructions)?;
        }
        Rvalue::Aggregate(AggregateKind::RawPtr { pointee_ty, mutable }, operands) => {
            let dest_ty = ctx.place_ty(dest)?;
            match raw_ptr_aggregate_operands(ctx, &dest_ty, pointee_ty, *mutable, operands)? {
                RawPtrAggregateOperands::Thin { data } => {
                    let data = ctx.resolve_operand(data, instructions)?;
                    assign_to_place(dest, data, ctx, instructions)?;
                }
                RawPtrAggregateOperands::Slice { data, metadata, elem_ty } => {
                    let data = ctx.resolve_operand(data, instructions)?;
                    let metadata = ctx.resolve_operand(metadata, instructions)?;
                    let fat_ptr =
                        ctx.emit_slice_fat_pointer(&elem_ty, data, metadata, instructions)?;
                    assign_to_place(dest, fat_ptr, ctx, instructions)?;
                }
            }
        }
        Rvalue::Aggregate(kind, operands) => {
            // Aggregate construction: store each field into the destination. The value built
            // is typed as the DESTINATION place (`built_dest_ty`): `(_1.1: E) = E::B(3)`
            // (rustc's `s.e = E::B(3)`) builds an `E` into `_1.1`, not a whole `_1`.
            let dest_ty = built_dest_ty(ctx, dest)?;
            validate_aggregate_kind_for_lir(kind, &dest_ty)?;
            let lir_ty = map_lowering_type(&dest_ty)?;

            // Read every operand BEFORE the first store: the slot is the destination local's
            // only memory, and MIR lets an operand read the destination itself for a
            // scalar-pair type (`_1 = (copy (_1.1), copy (_1.0))`, rust-lang/rust#68364).
            let mut operand_vals = Vec::with_capacity(operands.len());
            for operand in operands {
                operand_vals.push(ctx.resolve_operand(operand, instructions)?);
            }

            let base_ptr = constructor_dest_addr(ctx, dest, "Aggregate", instructions)?;

            match kind {
                AggregateKind::Tuple | AggregateKind::Array => {
                    for (i, &val) in operand_vals.iter().enumerate() {
                        let store_ty = match &dest_ty {
                            Ty::Tuple(fields) => {
                                let field_ty = fields.get(i).ok_or_else(|| {
                                    BridgeError::InvalidMir(format!(
                                        "tuple aggregate operand {i} exceeds destination arity {}",
                                        fields.len()
                                    ))
                                })?;
                                map_lowering_type(field_ty)?
                            }
                            Ty::Array { elem, .. } => map_lowering_type(elem)?,
                            other => {
                                return Err(BridgeError::InvalidMir(format!(
                                    "aggregate kind {kind:?} does not match destination type {other:?}"
                                )));
                            }
                        };
                        let field_ptr = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::StructGep {
                                struct_ty: lir_ty.clone(),
                                field_index: i as u32,
                            },
                            args: vec![base_ptr],
                            results: vec![field_ptr],
                        });
                        ctx.emit_checked_store(store_ty, val, field_ptr, instructions)?;
                    }
                }
                AggregateKind::Adt { name: aggregate_name, variant, active_field, .. } => {
                    debug_assert!(active_field.is_none());
                    let Ty::Adt { name: adt_name, fields: adt_fields, variants, .. } = &dest_ty
                    else {
                        return Err(BridgeError::InvalidMir(format!(
                            "ADT aggregate `{aggregate_name}` does not match destination type \
                             {dest_ty:?}"
                        )));
                    };
                    // The lanes, the tag slot and the declared discriminants
                    // below are the DESTINATION's: an aggregate that names
                    // another ADT would be laid out in the wrong type's lanes.
                    if !aggregate_names_adt(aggregate_name, adt_name) {
                        return Err(BridgeError::InvalidMir(format!(
                            "ADT aggregate `{aggregate_name}` does not name its destination's \
                             type `{adt_name}`"
                        )));
                    }
                    // Trust (ticket 216 cg-bridge): enum variant construction
                    // writes the variant's DECLARED discriminant into the tag
                    // slot. The slot is found by the one lookup the
                    // `SetDiscriminant` write and the `Discriminant` read use
                    // (`flat_tag_field_index`); the old convention here keyed
                    // on field 0 spelled exactly `tag`, so the extractor's
                    // `__tag` wrote NO tag at all (and took the first payload
                    // operand into the slot), and it wrote the variant INDEX.
                    // A declared struct/union has no tag: a field of it spelled
                    // `tag` is data (`flat_enum_tag_slot`).
                    //
                    // Operand k of a flat enum's variant v goes to that
                    // variant's own lane, `__v{v}_{name_k}` (`flat_variant_lane`,
                    // the lookup the `Downcast(v) + Field(k)` read and write
                    // use). Mapping operands in order onto the non-slot fields
                    // (95382e6164) wrote `Err(5)` of `Result<u64, u64>` into
                    // `Ok`'s lane. A struct, union, or slot-less ADT keeps the
                    // positional rule.
                    let tag_index = flat_enum_tag_slot(&dest_ty);

                    if tag_index.is_some() {
                        let (tag_slot, tag_field_ty) =
                            explicit_discriminant_field(&dest_ty, "enum aggregate")?;
                        let (tag_lir_ty, tag_imm) = declared_tag_lir_const(
                            &dest_ty,
                            &tag_field_ty,
                            *variant,
                            "enum aggregate",
                        )?;
                        let tag_ptr = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::StructGep {
                                struct_ty: lir_ty.clone(),
                                field_index: tag_slot as u32,
                            },
                            args: vec![base_ptr],
                            results: vec![tag_ptr],
                        });
                        let tag_val = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::Iconst { ty: tag_lir_ty.clone(), imm: tag_imm },
                            args: vec![],
                            results: vec![tag_val],
                        });
                        push_store(instructions, tag_lir_ty, tag_val, tag_ptr);
                    }

                    if tag_index.is_some()
                        && let Some(variant_def) = variants.get(*variant)
                        && operands.len() != variant_def.fields.len()
                    {
                        return Err(BridgeError::InvalidMir(format!(
                            "enum aggregate of variant {variant} (`{}`) of `{adt_name}` has {} \
                             operand(s) for {} declared field(s)",
                            variant_def.name,
                            operands.len(),
                            variant_def.fields.len()
                        )));
                    }
                    for (i, &val) in operand_vals.iter().enumerate() {
                        let field_index = if tag_index.is_some() {
                            flat_variant_lane(&dest_ty, *variant, i, "enum aggregate")?
                                .map(|(flat_index, _)| flat_index)
                                .ok_or_else(|| {
                                    BridgeError::InvalidMir(format!(
                                        "enum aggregate operand {i} of `{adt_name}` has no lane"
                                    ))
                                })?
                        } else if i < adt_fields.len() {
                            i
                        } else {
                            return Err(BridgeError::InvalidMir(format!(
                                "ADT aggregate operand {i} maps to no field of `{adt_name}`"
                            )));
                        };
                        let store_ty = map_lowering_type(&adt_fields[field_index].1)?;
                        let field_ptr = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::StructGep {
                                struct_ty: lir_ty.clone(),
                                field_index: field_index as u32,
                            },
                            args: vec![base_ptr],
                            results: vec![field_ptr],
                        });
                        ctx.emit_checked_store(store_ty, val, field_ptr, instructions)?;
                    }
                }
                other => unreachable!("validated aggregate kind before lowering: {other:?}"),
            }

            bind_constructed(ctx, dest, base_ptr);
        }
        Rvalue::Repeat(operand, count) => {
            // Array repeat `[operand; count]` into a stack slot, in a number of instructions set
            // by the program, never proportional to `count`:
            //   * an integer or bool CONSTANT whose byte image is one repeated byte (`[0u8; N]`,
            //     `[0u64; N]`, `[-1i32; N]`, `[true; N]`): ONE `Memset` of the whole extent;
            //   * any other element: lane 0 is stored once, then each `Memcpy` copies the
            //     already-filled prefix onto the lanes after it, doubling the filled length —
            //     ceil(log2 count) copies. That is O(log N), not constant: it is bounded by the
            //     bit width of the u32 extent carrier (at most 32 copies), whatever N is.
            // The per-element store loop this replaces was proportional to `count`, and its
            // `i as u32 * elem_size` offset wrapped past 4 GiB. Every offset and length here is
            // a checked u64 product carried as an I64 immediate, and the fill is checked to be
            // EXACTLY the slot's extent (`repeat_fill_extent`): `map_type` refuses a type whose
            // extent the u32 carrier cannot describe, so the slot is never smaller than what
            // the fill writes. The array is the DESTINATION place's (`built_dest_ty`).
            let dest_ty = built_dest_ty(ctx, dest)?;
            let lir_ty = map_type(&dest_ty)?;
            let elem_src_ty = match &dest_ty {
                Ty::Array { elem, .. } => elem.as_ref().clone(),
                _ => {
                    return Err(BridgeError::UnsupportedOp("Repeat on non-array type".to_string()));
                }
            };
            let elem_ty = map_type(&elem_src_ty)?;
            let elem_size = u64::from(elem_ty.bytes());
            let count = u64::try_from(*count)
                .map_err(|_| BridgeError::UnsupportedOp("Repeat count exceeds u64".to_string()))?;
            let fill_bytes = repeat_fill_extent(&lir_ty, elem_size, count)?;

            let fill_byte =
                if fill_bytes > 0 { repeated_fill_byte(operand, &elem_src_ty) } else { None };
            // The element (unless the fill is one `Memset` byte, which reads nothing) is read
            // before the first store into the destination.
            let val = match fill_byte {
                Some(_) => None,
                None => Some(ctx.resolve_operand(operand, instructions)?),
            };
            let base_ptr = constructor_dest_addr(ctx, dest, "Repeat", instructions)?;
            if let Some(byte) = fill_byte {
                // `Memset` takes the libc `int` fill; libc stores `(unsigned char)c`.
                let fill = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: i64::from(byte) },
                    args: vec![],
                    results: vec![fill],
                });
                let len = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I64, imm: carrier_imm(fill_bytes)? },
                    args: vec![],
                    results: vec![len],
                });
                instructions.push(Instruction {
                    opcode: Opcode::Memset,
                    args: vec![base_ptr, fill, len],
                    results: vec![],
                });
            } else if let Some(val) = val
                && fill_bytes > 0
            {
                ctx.emit_checked_store(elem_ty.clone(), val, base_ptr, instructions)?;
                let mut filled: u64 = 1;
                while filled < count {
                    let chunk = filled.min(count - filled);
                    let dst_offset = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst {
                            ty: LirType::I64,
                            imm: carrier_imm(filled * elem_size)?,
                        },
                        args: vec![],
                        results: vec![dst_offset],
                    });
                    let dst_ptr = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![base_ptr, dst_offset],
                        results: vec![dst_ptr],
                    });
                    let len = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst {
                            ty: LirType::I64,
                            imm: carrier_imm(chunk * elem_size)?,
                        },
                        args: vec![],
                        results: vec![len],
                    });
                    // Source `[0, chunk)` and destination `[filled, filled + chunk)` never
                    // overlap because `chunk <= filled`.
                    instructions.push(Instruction {
                        opcode: Opcode::Memcpy,
                        args: vec![dst_ptr, base_ptr, len],
                        results: vec![],
                    });
                    filled += chunk;
                }
            }

            bind_constructed(ctx, dest, base_ptr);
        }
        Rvalue::CopyForDeref(place) => {
            let src = ctx.resolve_place(place, instructions)?;
            assign_to_place(dest, src, ctx, instructions)?;
        }
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown rvalue variant".to_string()));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Terminator lowering
// ---------------------------------------------------------------------------

fn lower_terminator(
    term: &Terminator,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    return_lowering: ReturnLowering,
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<(), BridgeError> {
    match term {
        Terminator::Goto(target) => {
            emit_block_param_copies(target.0, ctx, instructions, block_params)?;
            instructions.push(Instruction {
                opcode: Opcode::Jump { dest: Block(target.0 as u32) },
                args: vec![],
                results: vec![],
            });
        }
        Terminator::Return => {
            let args = return_args(ctx, return_lowering, instructions)?;
            instructions.push(Instruction { opcode: Opcode::Return, args, results: vec![] });
        }
        Terminator::Unreachable => {
            // Model unreachable as a diverging abort call instead of
            // fabricating a normal return path.
            instructions.push(abort_call_instruction());
        }
        Terminator::SwitchInt { discr, targets, otherwise, span: _, .. } => {
            let discr_val = ctx.resolve_operand(discr, instructions)?;

            if targets.len() == 1 {
                // Binary branch: if discr == value then target else otherwise.
                let (value, target) = &targets[0];
                let then_dest = conditional_edge_dest(target.0, ctx, block_params)?;
                let else_dest = conditional_edge_dest(otherwise.0, ctx, block_params)?;
                // Trust (ticket 216 cg-bridge): the case constant is encoded as
                // the multi-way arm encodes it (`encode_switch_case`) and
                // materialized AT THE SELECTOR'S TYPE. It was an `I64` of
                // `*value as i64` whatever the selector: an `i32`/`u32`
                // selector against a label above 4095 (every negative repr(i32)
                // discriminant, `u32::MAX`) paired a W register with an X
                // register and the AArch64 encoder refused the function
                // ("CMP register widths must agree"; x86-64 ISel refuses any
                // Icmp whose operand types differ), and a 128-bit label was
                // silently truncated to its low 64 bits in the LIR.
                let selector_ty = map_type(&operand_ty(ctx, discr)?)?;
                let encoded = encode_switch_case(*value as i128, &selector_ty)
                    .map_err(|e| BridgeError::UnsupportedOp(format!("SwitchInt: {e}")))?;
                // Emit: cmp = icmp eq(discr, value)
                let const_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: selector_ty, imm: encoded },
                    args: vec![],
                    results: vec![const_val],
                });
                let cmp_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp { cond: IntCC::Equal },
                    args: vec![discr_val, const_val],
                    results: vec![cmp_val],
                });
                instructions.push(Instruction {
                    opcode: Opcode::Brif { cond: cmp_val, then_dest, else_dest },
                    args: vec![cmp_val],
                    results: vec![],
                });
            } else {
                // Multi-way: emit a Switch instruction. MIR spells each case as
                // the ZERO-extended bit pattern at the discriminant's width, but
                // the LIR case encoding depends on the selector's width (see
                // `mapping::encode_switch_case`): a 32-bit selector wants its
                // two's-complement value. `*val as i64` passed `i32 -1` /
                // `u32::MAX` through as 4294967295, which the jump-table lowering
                // (whose index arithmetic sign-extends a 32-bit selector) routed
                // to the default arm.
                let selector_ty = map_type(&operand_ty(ctx, discr)?)?;
                // `as i128` is exact for every selector of at most 64 bits (the
                // only widths the encoder admits); a 128-bit selector is refused.
                let encoded =
                    encode_switch_cases(targets.iter().map(|(val, _)| *val as i128), &selector_ty)
                        .map_err(|e| BridgeError::UnsupportedOp(format!("SwitchInt: {e}")))?;
                let mut cases = Vec::with_capacity(targets.len());
                for ((_, blk), val) in targets.iter().zip(encoded) {
                    cases.push((val, conditional_edge_dest(blk.0, ctx, block_params)?));
                }
                let default = conditional_edge_dest(otherwise.0, ctx, block_params)?;
                instructions.push(Instruction {
                    opcode: Opcode::Switch { cases, default },
                    args: vec![discr_val],
                    results: vec![],
                });
            }
        }
        // `unwind`: the native LIR path models the panic branch via a dedicated
        // panic block; the cleanup successor is lowered as its own reachable block,
        // so this arm ignores the unwind edge (behavior-preserving — this path never
        // modeled unwind tables).
        Terminator::Assert { cond, expected, msg, target, span, unwind: _ } => {
            // Assert: branch to target if cond == expected, else panic block.
            // The panic block is a dedicated diverging block, lazily allocated
            // and inserted by lower_body_to_lir.
            let cond_val = ctx.resolve_operand(cond, instructions)?;
            let panic_action = panic_action_for_assert(ctx, msg, span);
            let panic_blk = ctx.get_or_create_panic_block(panic_action);
            let target_dest = conditional_edge_dest(target.0, ctx, block_params)?;

            if *expected {
                // assert(cond == true) -> brif cond, target, panic
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cond_val,
                        then_dest: target_dest,
                        else_dest: panic_blk,
                    },
                    args: vec![cond_val],
                    results: vec![],
                });
            } else {
                // assert(cond == false) -> brif cond, panic, target
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cond_val,
                        then_dest: panic_blk,
                        else_dest: target_dest,
                    },
                    args: vec![cond_val],
                    results: vec![],
                });
            }
        }
        Terminator::Call { func: callee, args, dest, target, atomic, .. } => {
            if let Some(atomic) = atomic {
                let result_dest = atomic.dest.as_ref().unwrap_or(dest);
                let ordering = map_atomic_ordering(&atomic.ordering)?;

                match atomic.op_kind {
                    AtomicOpKind::Load => {
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        let result = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::AtomicLoad { ty, ordering },
                            args: vec![ptr],
                            results: vec![result],
                        });
                        assign_to_place(result_dest, result, ctx, instructions)?;
                    }
                    AtomicOpKind::Store => {
                        let value_operand = args.get(1).ok_or_else(|| {
                            BridgeError::InvalidMir(
                                "atomic store requires value operand at args[1]".to_string(),
                            )
                        })?;
                        let value = ctx.resolve_operand(value_operand, instructions)?;
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        instructions.push(Instruction {
                            opcode: Opcode::AtomicStore { ty, ordering },
                            args: vec![value, ptr],
                            results: vec![],
                        });
                    }
                    AtomicOpKind::Fence | AtomicOpKind::CompilerFence => {
                        instructions.push(Instruction {
                            opcode: Opcode::Fence { ordering },
                            args: vec![],
                            results: vec![],
                        });
                    }
                    AtomicOpKind::FetchAdd
                    | AtomicOpKind::FetchSub
                    | AtomicOpKind::FetchAnd
                    | AtomicOpKind::FetchOr
                    | AtomicOpKind::FetchXor
                    | AtomicOpKind::Exchange => {
                        let value_operand = args.get(1).ok_or_else(|| {
                            BridgeError::InvalidMir(format!(
                                "atomic {:?} requires value operand at args[1]",
                                atomic.op_kind
                            ))
                        })?;
                        let value = ctx.resolve_operand(value_operand, instructions)?;
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        let op = map_atomic_rmw_op(atomic.op_kind)?;
                        let result = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::AtomicRmw { op, ty, ordering },
                            args: vec![value, ptr],
                            results: vec![result],
                        });
                        assign_to_place(result_dest, result, ctx, instructions)?;
                    }
                    AtomicOpKind::CompareExchange | AtomicOpKind::CompareExchangeWeak => {
                        let expected_operand = args.get(1).ok_or_else(|| {
                            BridgeError::InvalidMir(
                                "atomic compare_exchange requires expected operand at args[1]"
                                    .to_string(),
                            )
                        })?;
                        let desired_operand = args.get(2).ok_or_else(|| {
                            BridgeError::InvalidMir(
                                "atomic compare_exchange requires desired operand at args[2]"
                                    .to_string(),
                            )
                        })?;
                        let expected = ctx.resolve_operand(expected_operand, instructions)?;
                        let desired = ctx.resolve_operand(desired_operand, instructions)?;
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        let result = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::CmpXchg {
                                ty,
                                success: ordering,
                                failure: cmpxchg_failure_ordering(ordering),
                            },
                            args: vec![expected, desired, ptr],
                            results: vec![result],
                        });
                        assign_to_place(result_dest, result, ctx, instructions)?;
                    }
                    AtomicOpKind::FetchNand | AtomicOpKind::FetchMin | AtomicOpKind::FetchMax => {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "atomic op kind has no LIR equivalent: {:?}",
                            atomic.op_kind
                        )));
                    }
                    // Trust: non-exhaustive fallback for future AtomicOpKind variants
                    _ => {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "unknown atomic op kind: {:?}",
                            atomic.op_kind
                        )));
                    }
                }

                if let Some(cont) = target {
                    emit_block_param_copies(cont.0, ctx, instructions, block_params)?;
                    instructions.push(Instruction {
                        opcode: Opcode::Jump { dest: Block(cont.0 as u32) },
                        args: vec![],
                        results: vec![],
                    });
                }

                return Ok(());
            }

            // Resolve call arguments. A by-value aggregate argument's value is the address of
            // its bytes, typed I64 by the `StackAddr` that made it; trust-cg classifies call
            // arguments by their LIR value types, so it is passed through a fresh `Copy` temp
            // typed as the aggregate (trust-cg-lower's call-argument temp contract: an
            // aggregate-typed Copy of an I64 carrier with exactly one use, the call).
            let mut arg_vals = Vec::with_capacity(args.len());
            for arg in args {
                let value = ctx.resolve_operand(arg, instructions)?;
                // Only the aggregate question is asked here: an argument whose type has no LIR
                // lowering (a unit or fn-item constant) is passed as it always was.
                let aggregate_ty = operand_ty(ctx, arg)
                    .ok()
                    .and_then(|ty| map_lowering_type(&ty).ok())
                    .filter(LirType::is_aggregate);
                if let Some(arg_ty) = aggregate_ty {
                    let temp = ctx.fresh_value();
                    ctx.record_value_type(temp, arg_ty);
                    instructions.push(Instruction {
                        opcode: Opcode::Copy,
                        args: vec![value],
                        results: vec![temp],
                    });
                    arg_vals.push(temp);
                } else {
                    arg_vals.push(value);
                }
            }

            // Determine result value for the call destination.
            let dest_ty = ctx.place_ty(dest)?;
            let call_result = if matches!(dest_ty, Ty::Unit | Ty::Never) {
                None
            } else {
                let call_result = ctx.fresh_value();
                let call_result_ty = map_lowering_type(&dest_ty)?;
                ctx.record_value_type(call_result, call_result_ty);
                Some(call_result)
            };

            instructions.push(Instruction {
                opcode: Opcode::Call {
                    name: callee.clone(),
                    binding: DirectCallBinding::Interposable,
                },
                args: arg_vals,
                results: call_result.into_iter().collect(),
            });

            // Assign the call result to the destination place.
            if let Some(call_result) = call_result {
                if place_is_direct_local(dest) {
                    ctx.local_values.insert(dest.local, call_result);
                    ctx.store_memory_backed_definition(dest.local, call_result, instructions)?;
                } else {
                    // For projected destinations, compute the address and store.
                    let addr = ctx.resolve_place_addr(dest, instructions)?;
                    let ty = map_lowering_type(&dest_ty)?;
                    ctx.emit_store_value(ty, call_result, addr, instructions);
                }
            }

            // If there is a continuation block, emit a jump to it.
            if let Some(cont) = target {
                emit_block_param_copies(cont.0, ctx, instructions, block_params)?;
                instructions.push(Instruction {
                    opcode: Opcode::Jump { dest: Block(cont.0 as u32) },
                    args: vec![],
                    results: vec![],
                });
            }
        }
        // TrustIr does not carry rustc's resolved, monomorphized drop-glue
        // instance. Trivially-Copy values need no glue; every other drop must
        // fail until the exact symbol and ABI are provided by the compiler.
        Terminator::Drop { place, target, .. } => {
            // The PLACE's type, never its base local's: `drop((*_1))` on
            // `_1: *mut String` drops a String, and a raw pointer is trivially
            // Copy (ticket 216 cg review 3: that drop lowered as a plain jump).
            let place_ty = ctx.place_ty(place)?;
            if !is_trivially_copy_ty(&place_ty) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "non-trivial Drop for {place_ty:?} requires an exact monomorphized drop-glue symbol and ABI; TrustIr carries neither"
                )));
            }

            emit_block_param_copies(target.0, ctx, instructions, block_params)?;
            instructions.push(Instruction {
                opcode: Opcode::Jump { dest: Block(target.0 as u32) },
                args: vec![],
                results: vec![],
            });
        }
        Terminator::Opaque { kind, targets, .. } => {
            return Err(BridgeError::UnsupportedOp(format!(
                "opaque MIR terminator `{kind}` is unsupported; targets={targets:?}"
            )));
        }
        Terminator::TailCall { .. } => {
            return Err(BridgeError::UnsupportedOp(
                "TailCall reached body lowering without the required call/return projection"
                    .to_string(),
            ));
        }
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown terminator variant".to_string()));
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "memory_image_tests.rs"]
mod memory_image_tests;

#[cfg(test)]
mod function_name_tests {
    use trust_types::{BlockId, SourceSpan};

    use super::*;

    fn unit_return_function(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::nested::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn nested_unit_function_named_main_does_not_become_process_entry() {
        let lir = lower_to_lir(&unit_return_function("main")).expect("unit main should lower");

        assert_eq!(lir.signature.params, Vec::<LirType>::new());
        assert_eq!(lir.signature.returns, Vec::<LirType>::new());

        let entry = &lir.blocks[&Block(0)];
        assert!(matches!(
            entry.instructions.as_slice(),
            [Instruction { opcode: Opcode::Return, args, results }]
                if args.is_empty() && results.is_empty()
        ));
    }

    #[test]
    fn ordinary_unit_function_remains_void() {
        let lir = lower_to_lir(&unit_return_function("helper")).expect("unit helper should lower");

        assert_eq!(lir.signature.returns, Vec::<LirType>::new());

        let entry = &lir.blocks[&Block(0)];
        assert!(matches!(
            entry.instructions.as_slice(),
            [Instruction { opcode: Opcode::Return, args, results }]
                if args.is_empty() && results.is_empty()
        ));
    }
}

#[cfg(test)]
mod return_join_tests {
    use trust_types::{BlockId, SourceSpan};

    use super::*;

    #[test]
    fn return_block_uses_join_param_for_return_slot() {
        let span = SourceSpan::default();
        let func = VerifiableFunction {
            name: "select_i32".to_string(),
            def_path: "test::select_i32".to_string(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: span.clone(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    TrustBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Goto(BlockId(3)),
                    },
                    TrustBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("multi-predecessor return should lower");
        let return_block = &lir.blocks[&Block(3)];
        assert_eq!(
            return_block.params.len(),
            1,
            "return slot must be a block parameter at the join"
        );

        let return_param = return_block.params[0].0;
        assert!(matches!(
            return_block.instructions.as_slice(),
            [Instruction { opcode: Opcode::Return, args, results }]
                if args.as_slice() == [return_param] && results.is_empty()
        ));
    }
}

#[cfg(test)]
mod integer_constant_tests {
    use trust_types::{BlockId, SourceSpan};

    use super::*;

    fn returning_constant(ty: Ty, value: ConstValue) -> VerifiableFunction {
        let span = SourceSpan::default();
        VerifiableFunction {
            name: "constant".to_string(),
            def_path: "test::constant".to_string(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: ty.clone(), name: None }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(value)),
                        span,
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn constants_outside_iconst_domain_fail_closed() {
        let signed = lower_to_lir(&returning_constant(Ty::i128(), ConstValue::Int(i128::MAX)))
            .expect_err("i128 value cannot be truncated into an i64 immediate");
        assert!(signed.to_string().contains("exceeds the exact 64-bit Iconst domain"));

        let unsigned = lower_to_lir(&returning_constant(
            Ty::Int { width: 128, signed: false },
            ConstValue::Uint(1, 128),
        ))
        .expect_err("u128 Iconst is not represented exactly");
        assert!(unsigned.to_string().contains("u128 constants cannot be represented"));

        let malformed = lower_to_lir(&returning_constant(
            Ty::Int { width: 8, signed: false },
            ConstValue::Uint(256, 8),
        ))
        .expect_err("out-of-width constants must not be truncated");
        assert!(malformed.to_string().contains("does not fit declared width 8"));
    }

    #[test]
    fn u64_all_bits_constant_preserves_its_bit_pattern() {
        let lir = lower_to_lir(&returning_constant(
            Ty::Int { width: 64, signed: false },
            ConstValue::Uint(u64::MAX as u128, 64),
        ))
        .expect("u64 bits fit Iconst exactly");
        let entry = &lir.blocks[&Block(0)];
        assert!(entry.instructions.iter().any(|instruction| {
            matches!(instruction.opcode, Opcode::Iconst { ty: LirType::I64, imm: -1 })
        }));
    }
}

#[cfg(test)]
mod terminator_runtime_tests {
    use trust_types::{BlockId, SourceSpan, UnwindEdge};

    use super::*;

    fn unit_function_with_terminator(name: &str, terminator: Terminator) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![TrustBlock { id: BlockId(0), stmts: vec![], terminator }],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn no_successor_inline_asm_fails_closed() {
        let func = unit_function_with_terminator(
            "inline_asm_trap",
            Terminator::Opaque {
                kind: "InlineAsm".to_string(),
                targets: vec![],
                span: SourceSpan::default(),
            },
        );

        let error = lower_to_lir(&func)
            .expect_err("no-successor InlineAsm has no faithful trap equivalence");
        assert!(matches!(
            error,
            BridgeError::UnsupportedOp(message)
                if message.contains("InlineAsm") && message.contains("targets=[]")
        ));
    }

    #[test]
    fn assert_uses_configured_panic_lang_item_with_location() {
        let span = SourceSpan {
            file: "src/main.rs".to_string(),
            line_start: 17,
            col_start: 9,
            line_end: 17,
            col_end: 12,
        };
        let func = VerifiableFunction {
            name: "checked_add".to_string(),
            def_path: "test::checked_add".to_string(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Constant(ConstValue::Bool(false)),
                            expected: true,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: span.clone(),
                        },
                    },
                    TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let options = LoweringOptions {
            panic_symbols: PanicRuntimeSymbols {
                add_overflow: Some("__trust_panic_add_overflow".to_string()),
                ..PanicRuntimeSymbols::default()
            },
            ..LoweringOptions::default()
        };

        let lir = lower_to_lir_with_options(&func, &options)
            .expect("assert should lower with configured panic symbol");
        let panic_block = lir
            .blocks
            .iter()
            .find_map(|(block, bb)| {
                (*block != Block(0)
                    && *block != Block(1)
                    && bb.instructions.iter().any(|inst| {
                        matches!(&inst.opcode, Opcode::Call { name, .. } if name == "__trust_panic_add_overflow")
                    }))
                .then_some(bb)
            })
            .expect("assert lowering should synthesize a runtime panic block");

        assert!(panic_block.instructions.iter().any(|inst| matches!(
            &inst.opcode,
            Opcode::GlobalRef { name }
                if trust_location_file_global_data(name)
                    .is_some_and(|data| data == b"src/main.rs\0".to_vec())
        )));
        let call = panic_block
            .instructions
            .iter()
            .find(|inst| {
                matches!(&inst.opcode, Opcode::Call { name, .. } if name == "__trust_panic_add_overflow")
            })
            .expect("panic block should call configured lang item");
        assert_eq!(call.args.len(), 1, "panic lang-item call must receive caller location");
        assert!(call.results.is_empty());
        assert!(
            !panic_block
                .instructions
                .iter()
                .any(|inst| matches!(&inst.opcode, Opcode::Call { name, .. } if name == "abort")),
            "configured panic lowering must not fall back to abort"
        );
    }
}

/// Test support: the byte length of every `Memcpy` in `block`, in order (each length operand is
/// an `Iconst` defined in the same block).
#[cfg(test)]
pub(crate) fn aggregate_copy_lengths(block: &LirBlock) -> Vec<i64> {
    block
        .instructions
        .iter()
        .filter(|inst| matches!(inst.opcode, Opcode::Memcpy))
        .map(|copy| {
            block
                .instructions
                .iter()
                .find_map(|inst| match inst.opcode {
                    Opcode::Iconst { imm, .. } if inst.results == [copy.args[2]] => Some(imm),
                    _ => None,
                })
                .expect("a Memcpy length is an Iconst in the same block")
        })
        .collect()
}

/// Test support: `block` loads and stores no whole aggregate. LIR carries an aggregate as the
/// address of its bytes, and trust-cg selects a whole-aggregate `Load`/`Store` as ONE
/// register-width access, silently dropping the rest of the value.
#[cfg(test)]
pub(crate) fn assert_no_whole_aggregate_access(block: &LirBlock) {
    for inst in &block.instructions {
        if let Opcode::Load { ty, .. } | Opcode::Store { ty, .. } = &inst.opcode {
            assert!(!ty.is_aggregate(), "whole-aggregate access {inst:?}");
        }
    }
}

#[cfg(test)]
mod aggregate_projection_tests {
    use trust_types::{BlockId, SourceSpan};

    use super::*;

    fn unit_function(
        name: &str,
        locals: Vec<LocalDecl>,
        stmts: Vec<Statement>,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![TrustBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    #[test]
    fn subslice_array_value_lowers_fixed_array() {
        let array_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 5 };
        let subslice_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 2 };
        let func = VerifiableFunction {
            name: "subslice_array_value".to_string(),
            def_path: "test::subslice_array_value".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: subslice_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: array_ty, name: Some("arr".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Subslice {
                                from: 1,
                                to: 3,
                                from_end: false,
                            }],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: subslice_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("array subslice value should lower");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I64, imm: 4 }))
        );
        assert_eq!(
            aggregate_copy_lengths(bb0),
            vec![20, 8, 8],
            "the [i32; 5] argument is copied into its slot (20 bytes); the subslice value is \
             exactly a [i32; 2] (8 bytes) copied out of it, then into the return place"
        );
        assert_no_whole_aggregate_access(bb0);
    }

    #[test]
    fn subslice_array_address_projection_lowers_thin_array_pointer() {
        let array_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 4 };
        let ptr_ty = Ty::RawPtr {
            pointee: Box::new(Ty::Array { elem: Box::new(Ty::i32()), len: 2 }),
            mutable: false,
        };
        let func = VerifiableFunction {
            name: "subslice_addr".to_string(),
            def_path: "test::subslice_addr".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ptr_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: array_ty, name: Some("arr".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::AddressOf(
                            false,
                            Place {
                                local: 1,
                                projections: vec![Projection::Subslice {
                                    from: 1,
                                    to: 3,
                                    from_end: false,
                                }],
                            },
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: ptr_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("array subslice address should lower as thin pointer");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I64, imm: 4 }))
        );
        assert!(
            !bb0.instructions.iter().any(|i| matches!(
                &i.opcode,
                Opcode::Load { ty: LirType::Struct(fields), align: None }
                    if fields.as_slice() == [LirType::I64, LirType::I64]
            )),
            "address-of array subslice must not produce slice metadata"
        );
        assert!(
            !bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 1, .. })),
            "address-of array subslice should remain a thin pointer"
        );
    }

    #[test]
    fn subslice_slice_value_materializes_fat_slice() {
        let slice_ty = Ty::Slice { elem: Box::new(Ty::u8()) };
        let func = VerifiableFunction {
            name: "slice_subslice_value".to_string(),
            def_path: "test::slice_subslice_value".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: slice_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: slice_ty.clone(), name: Some("slice".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Subslice {
                                from: 1,
                                to: 2,
                                from_end: true,
                            }],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: slice_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("slice subslice value should lower as fat pointer");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 1, .. })),
            "slice subslice should read and write the metadata lane"
        );
        assert!(
            bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Isub)),
            "from_end slice subslice should derive the new length from source metadata"
        );
        assert!(
            aggregate_copy_lengths(bb0).contains(&16),
            "slice subslice value should materialize a whole (data, len) fat pointer: a 16-byte copy"
        );
        assert_no_whole_aggregate_access(bb0);
    }

    #[test]
    fn subslice_slice_address_projection_preserves_metadata_lane() {
        let ptr_ty = Ty::RawPtr {
            pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
            mutable: false,
        };
        let func = VerifiableFunction {
            name: "slice_subslice_addr".to_string(),
            def_path: "test::slice_subslice_addr".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ptr_ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ptr_ty.clone(), name: Some("slice".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::AddressOf(
                            false,
                            Place {
                                local: 1,
                                projections: vec![
                                    Projection::Deref,
                                    Projection::Subslice { from: 1, to: 2, from_end: true },
                                ],
                            },
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: ptr_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("slice subslice address should preserve metadata");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 1, .. })),
            "slice address subslice should extract and rewrite the length lane"
        );
        assert!(
            bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::Isub)),
            "from_end slice subslice should derive the new length from source metadata"
        );
    }

    #[test]
    fn adt_active_field_aggregate_fails_closed() {
        let union_like_ty = Ty::Adt {
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "UnionLike".into(),
            fields: vec![("a".into(), Ty::i32()), ("b".into(), Ty::i64())].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        };
        let func = unit_function(
            "adt_active_field",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: union_like_ty, name: None },
            ],
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "UnionLike".into(),
                        variant: 0,
                        active_field: Some(1),
                        args: None,
                    },
                    vec![Operand::Constant(ConstValue::Int(7))],
                ),
                span: SourceSpan::default(),
            }],
        );

        let err = lower_to_lir(&func).expect_err("union active_field must fail closed");
        assert!(matches!(
            err,
            BridgeError::UnsupportedOp(msg) if msg.contains("active_field 1")
        ));
    }

    #[test]
    fn thin_raw_ptr_aggregate_lowers_to_data_pointer() {
        let ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::i32()), mutable: false };
        let func = unit_function(
            "thin_raw_ptr_aggregate",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: ptr_ty.clone(), name: Some("data".into()) },
                LocalDecl { index: 2, ty: ptr_ty, name: Some("out".into()) },
            ],
            vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::RawPtr { pointee_ty: Ty::i32(), mutable: false },
                    vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Unit)],
                ),
                span: SourceSpan::default(),
            }],
        );

        let lir = lower_to_lir(&func).expect("thin raw pointer aggregate should lower");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            !bb0.instructions.iter().any(|i| matches!(i.opcode, Opcode::StructGep { .. })),
            "thin raw pointer aggregate should not be materialized as a struct"
        );
    }

    #[test]
    fn fat_raw_ptr_aggregate_lowers_slice_length_metadata() {
        let data_ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false };
        let slice_ptr_ty = Ty::RawPtr {
            pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
            mutable: false,
        };
        let func = unit_function(
            "fat_raw_ptr_aggregate",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
                LocalDecl { index: 3, ty: slice_ptr_ty, name: Some("out".into()) },
            ],
            vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee_ty: Ty::Slice { elem: Box::new(Ty::u8()) },
                        mutable: false,
                    },
                    vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                ),
                span: SourceSpan::default(),
            }],
        );

        let lir = lower_to_lir(&func).expect("fat raw pointer aggregate should lower");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::StructGep { field_index: 1, .. })),
            "fat raw pointer aggregate should materialize a length metadata lane"
        );
        assert!(matches!(
            lir.stack_slots.last(),
            Some(slot) if slot.size >= 16
        ));
    }

    #[test]
    fn fat_raw_ptr_aggregate_rejects_non_usize_metadata() {
        let data_ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false };
        let slice_ptr_ty = Ty::RawPtr {
            pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
            mutable: false,
        };
        let func = unit_function(
            "fat_raw_ptr_bad_metadata",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("bad_len".into()) },
                LocalDecl { index: 3, ty: slice_ptr_ty, name: Some("out".into()) },
            ],
            vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee_ty: Ty::Slice { elem: Box::new(Ty::u8()) },
                        mutable: false,
                    },
                    vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                ),
                span: SourceSpan::default(),
            }],
        );

        let err = lower_to_lir(&func).expect_err("non-usize metadata must fail closed");
        assert!(matches!(
            err,
            BridgeError::UnsupportedOp(msg) if msg.contains("precise usize length lane")
        ));
    }

    #[test]
    fn raw_ptr_aggregate_rejects_dyn_vtable_metadata() {
        let data_ptr_ty = Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false };
        let dyn_ptr_ty = Ty::RawPtr {
            pointee: Box::new(Ty::Dynamic {
                trait_name: "Debug".into(),
                principal_key: Some("Debug".into()),
            }),
            mutable: false,
        };
        let func = unit_function(
            "raw_ptr_dyn_vtable_metadata",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: data_ptr_ty, name: Some("data".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("vtable".into()) },
                LocalDecl { index: 3, ty: dyn_ptr_ty, name: Some("out".into()) },
            ],
            vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee_ty: Ty::Dynamic {
                            trait_name: "Debug".into(),
                            principal_key: Some("Debug".into()),
                        },
                        mutable: false,
                    },
                    vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                ),
                span: SourceSpan::default(),
            }],
        );

        let err = lower_to_lir(&func).expect_err("dyn metadata must fail closed");
        assert!(matches!(
            err,
            BridgeError::UnsupportedOp(msg) if msg.contains("vtable metadata lane")
        ));
    }

    #[test]
    fn fieldless_adt_aggregate_fails_closed_as_unsupported_op() {
        let fieldless = Ty::Adt {
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "OptionI32".into(),
            fields: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        };
        let func = unit_function(
            "fieldless_adt",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: fieldless, name: None },
            ],
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "OptionI32".into(),
                        variant: 0,
                        active_field: None,
                        args: None,
                    },
                    vec![],
                ),
                span: SourceSpan::default(),
            }],
        );

        let err = lower_to_lir(&func).expect_err("fieldless ADT must fail closed");
        assert!(matches!(
            err,
            BridgeError::UnsupportedOp(msg) if msg.contains("fieldless ADT aggregate")
        ));
    }
}

/// The entry-register binding lowering battery: the fixture shape lowered for
/// real, every mutation refused, and both directions of the certificate gates
/// exercised end to end through `lower_body_to_lir_with_options`.
#[cfg(test)]
mod entry_binding_lowering_tests {
    use trust_types::{BlockId, ConstValue, Operand, Place, Rvalue, Sort, SourceSpan};

    use super::*;
    use crate::entry_binding::{BinaryEntryBindings, BinaryEntryParam, BindingArch};

    fn u64_ty() -> Ty {
        Ty::Int { width: 64, signed: false }
    }

    /// A body shaped like the decompiled `trust_fixture_x86_load` after frame
    /// reconstruction: machine-register locals (the x86_64 LocalLayout names
    /// that matter here), arg_count 0, one surviving statement — the 8-byte
    /// little-endian load of [RDI] into RAX — and a bare return.
    fn x86_load_fixture_body(
        stmts: Vec<Statement>,
        blocks: Option<Vec<TrustBlock>>,
    ) -> VerifiableBody {
        let mut locals =
            vec![LocalDecl { index: 0, ty: u64_ty(), name: Some("_lifted_result".into()) }];
        for (index, name) in [(1, "RAX"), (8, "RDI")] {
            locals.push(LocalDecl { index, ty: u64_ty(), name: Some(name.to_string()) });
        }
        VerifiableBody {
            locals,
            blocks: blocks.unwrap_or_else(|| {
                vec![TrustBlock { id: BlockId(0), stmts, terminator: Terminator::Return }]
            }),
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    fn mem_seed() -> Formula {
        Formula::Var(
            "MEM".to_string(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    }

    fn reg_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(64))
    }

    /// Mirror of the lifters' little-endian byte-assembled load
    /// (`trust-machine-sem::load_le_bytes`).
    fn le_load(root: &Formula) -> Formula {
        let mem = mem_seed();
        let mut result = Formula::BitVec { value: 0, width: 64 };
        for i in 0..8u32 {
            let addr = if i == 0 {
                root.clone()
            } else {
                Formula::BvAdd(
                    Box::new(root.clone()),
                    Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                    64,
                )
            };
            let byte = Formula::Select(Box::new(mem.clone()), Box::new(addr));
            let extended = Formula::BvZeroExt(Box::new(byte), 56);
            result = if i == 0 {
                extended
            } else {
                Formula::BvOr(
                    Box::new(result),
                    Box::new(Formula::BvShl(
                        Box::new(extended),
                        Box::new(Formula::BitVec { value: i128::from(i * 8), width: 64 }),
                        64,
                    )),
                    64,
                )
            };
        }
        result
    }

    fn load_rax_from(root: &Formula) -> Statement {
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Symbolic(le_load(root))),
            span: SourceSpan::default(),
        }
    }

    fn clobber_rdi() -> Statement {
        Statement::Assign {
            place: Place::local(8),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
            span: SourceSpan::default(),
        }
    }

    fn rdi_bindings() -> BinaryEntryBindings {
        BinaryEntryBindings {
            arch: BindingArch::X86_64,
            params: vec![BinaryEntryParam {
                var_name: "X7".to_string(),
                reg_name: "RDI".to_string(),
                local_index: 8,
            }],
        }
    }

    fn options_with(bindings: BinaryEntryBindings) -> LoweringOptions {
        LoweringOptions { entry_bindings: Some(bindings), ..LoweringOptions::default() }
    }

    /// The capability itself, asserted at the instruction level: the fixture
    /// body lowers to exactly [Load{ty: I64} of param Value(0), Return], with
    /// the signature carrying the one bound param — and the consumption
    /// record names the load. The bindings are also asserted NON-EMPTY
    /// explicitly, so an empty-table bug can never hide behind a refusal
    /// that this battery also expects elsewhere.
    #[test]
    fn fixture_load_lowers_to_a_real_load_of_the_entry_param() {
        let body = x86_load_fixture_body(vec![load_rax_from(&reg_var("X7"))], None);
        let bindings = rdi_bindings();
        assert!(!bindings.params.is_empty(), "the binding table must be non-empty");
        let (lir, consumed) = lower_body_to_lir_with_options_and_consumptions(
            "trust_fixture_x86_load",
            &body,
            &options_with(bindings),
        )
        .expect("the justified load must lower");

        assert_eq!(lir.signature.params, vec![LirType::I64], "one entry-register param");
        let entry_block = &lir.blocks[&Block(0)];
        assert_eq!(
            entry_block.instructions.len(),
            2,
            "exactly the load and the return: {:?}",
            entry_block.instructions
        );
        let load = &entry_block.instructions[0];
        assert_eq!(load.opcode, Opcode::Load { ty: LirType::I64, align: None });
        assert_eq!(load.args, vec![Value(0)], "the address is the RDI entry param");
        assert_eq!(entry_block.instructions[1].opcode, Opcode::Return);

        assert_eq!(consumed.len(), 1);
        assert_eq!(consumed[0].block, 0);
        assert_eq!(consumed[0].statement_index, 0);
        assert!(consumed[0].detail.contains("Opcode::Load"), "{}", consumed[0].detail);
        assert!(consumed[0].detail.contains("RDI"), "{}", consumed[0].detail);

        crate::validation::validate_lir(&lir).expect("emitted LIR must validate");
    }

    /// A constant displacement on the base register lowers as
    /// Iconst; Iadd; Load.
    #[test]
    fn displacement_load_lowers_with_iconst_iadd() {
        let root = Formula::BvAdd(
            Box::new(reg_var("X7")),
            Box::new(Formula::BitVec { value: 16, width: 64 }),
            64,
        );
        let body = x86_load_fixture_body(vec![load_rax_from(&root)], None);
        let (lir, _) = lower_body_to_lir_with_options_and_consumptions(
            "disp",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect("the displaced load must lower");
        let instructions = &lir.blocks[&Block(0)].instructions;
        assert_eq!(instructions.len(), 4, "{instructions:?}");
        assert_eq!(instructions[0].opcode, Opcode::Iconst { ty: LirType::I64, imm: 16 });
        assert_eq!(instructions[1].opcode, Opcode::Iadd);
        assert_eq!(instructions[1].args[0], Value(0), "base is the entry param");
        assert_eq!(instructions[2].opcode, Opcode::Load { ty: LirType::I64, align: None });
        assert_eq!(instructions[3].opcode, Opcode::Return);
    }

    /// The anti-"silently wrong otherwise" control: a two-block body whose
    /// first block clobbers RDI must REFUSE the load in the second block, and
    /// the refusal must name the concrete kill.
    #[test]
    fn clobbered_path_refuses_and_names_the_kill() {
        let blocks = vec![
            TrustBlock {
                id: BlockId(0),
                stmts: vec![clobber_rdi()],
                terminator: Terminator::Goto(BlockId(1)),
            },
            TrustBlock {
                id: BlockId(1),
                stmts: vec![load_rax_from(&reg_var("X7"))],
                terminator: Terminator::Return,
            },
        ];
        let body = x86_load_fixture_body(vec![], Some(blocks));
        let err = lower_body_to_lir_with_options_and_consumptions(
            "clobbered",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect_err("a clobbered base register must refuse");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(message.contains("RDI"), "{message}");
        assert!(message.contains("block 0 statement 0"), "{message}");
        assert!(
            message.contains("not what reaches block 1"),
            "the refusal must carry the justification gap: {message}"
        );
    }

    /// Converse of the clobber control: the same two-block CFG with the
    /// clobber removed must LOWER — refusing here would be over-correction.
    #[test]
    fn preserved_multiblock_load_lowers() {
        let blocks = vec![
            TrustBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            TrustBlock {
                id: BlockId(1),
                stmts: vec![load_rax_from(&reg_var("X7"))],
                terminator: Terminator::Return,
            },
        ];
        let body = x86_load_fixture_body(vec![], Some(blocks));
        let (lir, consumed) = lower_body_to_lir_with_options_and_consumptions(
            "preserved",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect("a preserved multi-block load must lower");
        assert_eq!(consumed.len(), 1);
        assert_eq!(consumed[0].block, 1);
        crate::validation::validate_lir(&lir).expect("emitted LIR must validate");
    }

    /// The panel's blocker control: the ENTRY block is its own loop head and
    /// clobbers RDI after the load. `Var("X7")` there denotes the value at
    /// every arrival — iteration 2 sees the clobber — so binding it to the
    /// function-entry param would emit a different program. Must refuse.
    #[test]
    fn entry_as_loop_head_with_clobber_refuses() {
        let blocks = vec![
            TrustBlock {
                id: BlockId(0),
                stmts: vec![load_rax_from(&reg_var("X7")), clobber_rdi()],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Constant(ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(0))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];
        let body = x86_load_fixture_body(vec![], Some(blocks));
        let err = lower_body_to_lir_with_options_and_consumptions(
            "entry_loop_clobber",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect_err("a back edge into the entry block carries the clobber to the load");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(message.contains("RDI"), "{message}");
    }

    /// Converse of the blocker control: the same self-loop that never writes
    /// RDI keeps the binding and lowers.
    #[test]
    fn entry_as_loop_head_without_clobber_lowers() {
        let blocks = vec![
            TrustBlock {
                id: BlockId(0),
                stmts: vec![load_rax_from(&reg_var("X7"))],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Constant(ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(0))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];
        let body = x86_load_fixture_body(vec![], Some(blocks));
        let (lir, _) = lower_body_to_lir_with_options_and_consumptions(
            "entry_loop_clean",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect("a clean self-loop must not strip the binding");
        crate::validation::validate_lir(&lir).expect("emitted LIR must validate");
    }

    /// A base register outside the bound ABI argument prefix refuses with
    /// guidance naming the candidate set.
    #[test]
    fn non_abi_base_refuses_with_guidance() {
        let body = x86_load_fixture_body(vec![load_rax_from(&reg_var("X3"))], None);
        let err = lower_body_to_lir_with_options_and_consumptions(
            "rbx_base",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect_err("an unbound base register must refuse");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(message.contains("X3"), "{message}");
        assert!(message.contains("RDI (X7)"), "the guidance names the candidates: {message}");
    }

    /// Without bindings the behavior is byte-identical to before the field
    /// existed: the same refusal, no params, no consumptions — the MIR-lane
    /// no-op control.
    #[test]
    fn default_options_are_unchanged() {
        let body = x86_load_fixture_body(vec![load_rax_from(&reg_var("X7"))], None);
        let err = lower_body_to_lir_with_options("mir_lane", &body, &LoweringOptions::default())
            .expect_err("the load still refuses without bindings");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(
            message.contains("symbolic operand requires target-semantic lowering"),
            "{message}"
        );
        assert!(
            !message.contains("entry-register"),
            "no binding enrichment without a table: {message}"
        );
    }

    /// Mixing entry bindings with MIR argument locals refuses outright.
    #[test]
    fn mixing_bindings_with_mir_args_refuses() {
        let mut body = x86_load_fixture_body(vec![], None);
        body.arg_count = 1;
        let err = lower_body_to_lir_with_options_and_consumptions(
            "mixed",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect_err("two parameter conventions in one body must refuse");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(message.contains("one parameter convention"), "{message}");
    }

    /// A refused binding table (here: a name mismatch against the body) keeps
    /// lowering param-free and attaches the refusal reason to the symbolic
    /// refusal.
    #[test]
    fn refused_table_attaches_the_reason() {
        let mut bindings = rdi_bindings();
        bindings.params[0].local_index = 1; // RAX's local, named differently
        let body = x86_load_fixture_body(vec![load_rax_from(&reg_var("X7"))], None);
        let err = lower_body_to_lir_with_options_and_consumptions(
            "refused_table",
            &body,
            &options_with(bindings),
        )
        .expect_err("the load refuses when the table was refused");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(
            message.contains("refused for this body"),
            "the refusal carries the table's rejection: {message}"
        );
        assert!(message.contains("does not match"), "{message}");
    }

    /// The bare bound register Var lowers to the param value itself.
    #[test]
    fn bare_bound_var_lowers_to_the_param() {
        let body = x86_load_fixture_body(
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Symbolic(reg_var("X7"))),
                span: SourceSpan::default(),
            }],
            None,
        );
        let (lir, consumed) = lower_body_to_lir_with_options_and_consumptions(
            "mov_rax_rdi",
            &body,
            &options_with(rdi_bindings()),
        )
        .expect("a bare bound Var must lower to the param");
        assert_eq!(lir.signature.params, vec![LirType::I64]);
        assert_eq!(consumed.len(), 1);
        let instructions = &lir.blocks[&Block(0)].instructions;
        assert_eq!(instructions.len(), 1, "just the return: {instructions:?}");
        assert_eq!(instructions[0].opcode, Opcode::Return);
    }
}

/// Terminator-position gate: a symbolic operand in a TERMINATOR never lowers
/// through entry bindings (consumption records are statement-keyed; a
/// terminator has no statement index and no evidence row), so a bare bound
/// Var used as a SwitchInt discriminant refuses exactly as it does today.
#[cfg(test)]
mod entry_binding_terminator_position_tests {
    use trust_types::{BlockId, ConstValue, Operand, Place, Rvalue, Sort, SourceSpan};

    use super::*;
    use crate::entry_binding::{BinaryEntryBindings, BinaryEntryParam, BindingArch};

    #[test]
    fn bare_bound_var_discriminant_refuses_in_terminator_position() {
        let u64_ty = Ty::Int { width: 64, signed: false };
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u64_ty.clone(), name: Some("_lifted_result".into()) },
                LocalDecl { index: 8, ty: u64_ty, name: Some("RDI".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Symbolic(Formula::Var("X7".to_string(), Sort::BitVec(64))),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        };
        let options = LoweringOptions {
            entry_bindings: Some(BinaryEntryBindings {
                arch: BindingArch::X86_64,
                params: vec![BinaryEntryParam {
                    var_name: "X7".to_string(),
                    reg_name: "RDI".to_string(),
                    local_index: 8,
                }],
            }),
            ..LoweringOptions::default()
        };
        let err = lower_body_to_lir_with_options_and_consumptions("discr", &body, &options)
            .expect_err("a terminator-position symbolic operand must refuse");
        let BridgeError::UnsupportedOp(message) = err else { panic!("wrong error kind") };
        assert!(
            message.contains("symbolic operand requires target-semantic lowering"),
            "{message}"
        );
        // A statement-position use of the SAME formula in the SAME body shape
        // still lowers — the gate is positional, not a blanket regression.
        let mut statement_body = body;
        statement_body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Symbolic(Formula::Var(
                "X7".to_string(),
                Sort::BitVec(64),
            ))),
            span: SourceSpan::default(),
        });
        statement_body.blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Constant(ConstValue::Bool(true)),
            targets: vec![(1, BlockId(1))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        let (_, consumed) =
            lower_body_to_lir_with_options_and_consumptions("stmt", &statement_body, &options)
                .expect("statement-position use lowers");
        assert_eq!(consumed.len(), 1, "converse control: the gate is positional");
    }
}
