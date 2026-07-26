//! Lowering from trust-types IR to trust_cg LIR.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cg_lower::function::{
    BasicBlock as LirBlock, Function as LirFunction, Signature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, AssertMessage, AtomicOpKind, BasicBlock as TrustBlock, BinOp, ConstValue,
    Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    UnOp, VerifiableBody, VerifiableFunction,
};

use crate::BridgeError;
use crate::mapping::{
    cmpxchg_failure_ordering, deref_type, downcast_type, element_type, field_type,
    is_trivially_copy_ty, map_atomic_ordering, map_atomic_rmw_op, map_binop, map_float_binop,
    map_type, map_unop,
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
}

impl<'a> LoweringCtx<'a> {
    fn new(
        locals: &'a [LocalDecl],
        arg_count: usize,
        max_block_id: u32,
        options: &'a LoweringOptions,
    ) -> Self {
        let mut ctx = Self {
            locals,
            local_values: FxHashMap::with_capacity_and_hasher(locals.len(), Default::default()),
            value_types: new_lir_value_type_map(),
            next_value: 0,
            stack_slots: Vec::new(),
            local_stack_slots: FxHashMap::default(),
            panic_blocks: Vec::new(),
            options,
            pending_blocks: Vec::new(),
            next_block_id: max_block_id + 1,
        };
        // trust_cg ISel convention: Value(0)..Value(arg_count-1) are formal arguments.
        // Trust-types convention: local 0 is the return slot, locals 1..=arg_count are args.
        // Assign argument locals first to match ISel expectations.
        for i in 1..=arg_count {
            if let Some(local) = locals.iter().find(|l| l.index == i) {
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
            .iter()
            .find(|l| l.index == index)
            .map(|l| &l.ty)
            .ok_or(BridgeError::MissingLocal(index))
    }

    /// Whether a local is a signed integer type.
    fn is_signed(&self, index: usize) -> bool {
        self.local_ty(index).map(|ty| ty.is_signed()).unwrap_or(false)
    }

    /// Get the fully-projected type of a place.
    fn place_ty(&self, place: &Place) -> Result<Ty, BridgeError> {
        let mut current_ty = self.local_ty(place.local)?.clone();

        for proj in &place.projections {
            current_ty = match proj {
                Projection::Field(field_idx) => field_type(&current_ty, *field_idx)?,
                Projection::Deref => deref_type(&current_ty)?,
                Projection::Index(_) | Projection::ConstantIndex { .. } => {
                    element_type(&current_ty)?
                }
                Projection::Downcast(variant_idx) => downcast_type(&current_ty, *variant_idx)?,
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

    /// Materialize a local into a stack slot and return its address.
    fn materialize_local_stack_addr(
        &mut self,
        local_idx: usize,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if let Some(&slot) = self.local_stack_slots.get(&local_idx) {
            return Ok(self.emit_stack_addr(slot, instructions));
        }

        let slot = self.ensure_local_stack_slot(local_idx)?;
        let ptr = self.emit_stack_addr(slot, instructions);
        let value = self.local_value(local_idx)?;
        let ty = map_lowering_type(self.local_ty(local_idx)?)?;
        push_store(instructions, ty, value, ptr);
        Ok(ptr)
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
            Operand::Symbolic(formula) => self.emit_ground_symbolic_constant(formula, instructions),
            _ => Err(BridgeError::UnsupportedOp("unknown operand variant".to_string())),
        }
    }

    /// Resolve a Place to a LIR Value.
    ///
    /// For simple locals (no projections), returns the Value directly.
    /// For projected places (Field, Deref, Index), emits StructGep/Load
    /// instructions to compute the final value.
    fn resolve_place(
        &mut self,
        place: &Place,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if place_is_direct_local(place) {
            return self.local_value(place.local);
        }

        // Start with the base local's address. If it's an aggregate with a
        // stack slot, use StackAddr; otherwise treat the local value as a pointer.
        // Track the current type through projections so we know field types.
        let base_ty = self.local_ty(place.local)?.clone();
        let mut current_val = if is_addressable_local_ty(&base_ty) {
            self.materialize_local_stack_addr(place.local, instructions)?
        } else {
            self.local_value(place.local)?
        };
        let mut current_ty = base_ty;
        let mut current_is_addr = is_addressable_local_ty(&current_ty);

        for proj in &place.projections {
            match proj {
                Projection::Field(field_idx) => {
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Field projection requires addressable aggregate base: {current_ty:?}"
                        )));
                    }
                    let lir_struct_ty = map_type(&current_ty)?;
                    let result = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: lir_struct_ty,
                            field_index: *field_idx as u32,
                        },
                        args: vec![current_val],
                        results: vec![result],
                    });
                    // Load the field value.
                    let field_ty = field_type(&current_ty, *field_idx)?;
                    let lir_field_ty = map_type(&field_ty)?;
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_field_ty, align: None },
                        args: vec![result],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = field_ty;
                    current_is_addr = false;
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

                    let lir_pointee = map_lowering_type(&pointee_ty)?;
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_pointee, align: None },
                        args: vec![current_val],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = pointee_ty;
                    current_is_addr = false;
                }
                Projection::Index(idx_local) => {
                    if slice_element_type(&current_ty).is_some() {
                        let idx_val = self.local_value(*idx_local)?;
                        let elem_ty = slice_element_type(&current_ty).expect("checked above");
                        current_val = self.emit_slice_index_load(
                            current_val,
                            &current_ty,
                            idx_val,
                            instructions,
                        )?;
                        current_ty = elem_ty;
                        current_is_addr = false;
                        continue;
                    }
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Index projection requires addressable array/slice base: {current_ty:?}"
                        )));
                    }
                    // Index into an array/slice: ptr + idx * elem_size.
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();

                    let idx_val = self.local_value(*idx_local)?;
                    // Emit: offset = idx * elem_size
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
                    // Emit: addr = base + offset
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset],
                        results: vec![addr],
                    });
                    // Load the element.
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_elem, align: None },
                        args: vec![addr],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = elem_ty;
                    current_is_addr = false;
                }
                Projection::Downcast(variant_idx) => {
                    // Downcast: select a variant of an enum. At the MIR level this
                    // is just a type-level marker. The actual data pointer is the same.
                    // We update the type tracking but don't emit instructions.
                    current_ty = downcast_type(&current_ty, *variant_idx)?;
                }
                Projection::ConstantIndex { offset, min_length, from_end } => {
                    if slice_element_type(&current_ty).is_some() {
                        let elem_ty = slice_element_type(&current_ty).expect("checked above");
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
                        current_val = self.emit_slice_index_load(
                            current_val,
                            &current_ty,
                            index,
                            instructions,
                        )?;
                        current_ty = elem_ty;
                        current_is_addr = false;
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
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_elem, align: None },
                        args: vec![addr],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = elem_ty;
                    current_is_addr = false;
                }
                Projection::Subslice { from, to, from_end } => {
                    let result_ty = subslice_result_type(&current_ty, *from, *to, *from_end)?;
                    current_val = if current_is_addr && matches!(current_ty, Ty::Array { .. }) {
                        self.emit_array_subslice_value(
                            current_val,
                            &current_ty,
                            *from,
                            *to,
                            *from_end,
                            instructions,
                        )?
                    } else if slice_element_type(&current_ty).is_some() {
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
                            "Subslice projection requires array address or slice fat pointer base: {current_ty:?}"
                        )));
                    };
                    current_ty = result_ty;
                    current_is_addr = false;
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
        Ok(current_val)
    }

    /// Resolve a Place to a pointer Value (address) rather than loading.
    ///
    /// Used by Ref and AddressOf rvalues that need the address of a place.
    fn resolve_place_addr(
        &mut self,
        place: &Place,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let mut current_val = self.materialize_local_stack_addr(place.local, instructions)?;

        if place.projections.is_empty() {
            return Ok(current_val);
        }

        let base_ty = self.local_ty(place.local)?.clone();
        let mut current_ty = base_ty;
        let mut current_is_addr = true;

        for proj in &place.projections {
            match proj {
                Projection::Field(field_idx) => {
                    if !current_is_addr {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "Field address projection requires addressable aggregate base: {current_ty:?}"
                        )));
                    }
                    let lir_struct_ty = map_type(&current_ty)?;
                    let result = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: lir_struct_ty,
                            field_index: *field_idx as u32,
                        },
                        args: vec![current_val],
                        results: vec![result],
                    });
                    current_val = result;
                    current_ty = field_type(&current_ty, *field_idx)?;
                }
                Projection::Deref => {
                    // Load the pointer, then the result is the address. Slice
                    // fat pointers load the full `(data, len)` value instead.
                    let pointee_ty = deref_type(&current_ty)?;
                    if matches!(pointee_ty, Ty::Slice { .. }) {
                        let fat_ty = slice_fat_pointer_lir_ty(&current_ty)?;
                        let loaded = self.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::Load { ty: fat_ty, align: None },
                            args: vec![current_val],
                            results: vec![loaded],
                        });
                        current_val = loaded;
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
                        let idx_val = self.local_value(*idx_local)?;
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

                    let idx_val = self.local_value(*idx_local)?;
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

    fn materialize_value_stack_addr(
        &mut self,
        value: Value,
        ty: &LirType,
        instructions: &mut Vec<Instruction>,
    ) -> Value {
        let slot = self.alloc_stack_slot(ty);
        let addr = self.emit_stack_addr(slot, instructions);
        push_store(instructions, ty.clone(), value, addr);
        addr
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
        let fat_addr = self.materialize_value_stack_addr(fat_ptr, &fat_ty, instructions);
        let field_addr = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::StructGep { struct_ty: fat_ty, field_index },
            args: vec![fat_addr],
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

    fn emit_slice_index_load(
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
        let addr = self.emit_slice_index_addr(fat_ptr, source_ty, index, instructions)?;
        let loaded = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::Load { ty: map_type(&elem_ty)?, align: None },
            args: vec![addr],
            results: vec![loaded],
        });
        Ok(loaded)
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

        Ok(materialize_aggregate_value(self, slice_addr, &fat_ty, instructions))
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

    fn emit_array_subslice_value(
        &mut self,
        base_addr: Value,
        source_ty: &Ty,
        from: usize,
        to: usize,
        from_end: bool,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let result_ty = subslice_result_type(source_ty, from, to, from_end)?;
        let result_lir_ty = match &result_ty {
            Ty::Array { .. } => map_type(&result_ty)?,
            _ => {
                return Err(BridgeError::UnsupportedOp(format!(
                    "array Subslice unexpectedly produced non-array type {result_ty:?}"
                )));
            }
        };
        let start_addr =
            self.emit_array_subslice_addr(base_addr, source_ty, from, to, from_end, instructions)?;
        Ok(materialize_aggregate_value(self, start_addr, &result_lir_ty, instructions))
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
) -> Result<Vec<Value>, BridgeError> {
    match return_lowering {
        ReturnLowering::Value => Ok(vec![ctx.local_value(0)?]),
        ReturnLowering::NoValue => Ok(vec![]),
    }
}

fn abort_call_instruction() -> Instruction {
    Instruction {
        opcode: Opcode::Call { name: ABORT_SYMBOL.to_string() },
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
                opcode: Opcode::Call { name: symbol.clone() },
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

fn materialize_aggregate_value(
    ctx: &mut LoweringCtx<'_>,
    base_ptr: Value,
    lir_ty: &LirType,
    instructions: &mut Vec<Instruction>,
) -> Value {
    let value = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Load { ty: lir_ty.clone(), align: None },
        args: vec![base_ptr],
        results: vec![value],
    });
    value
}

fn terminator_successors(term: &Terminator) -> Vec<usize> {
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

fn terminator_supports_block_param_copies(term: &Terminator) -> bool {
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
        if let Statement::Assign { place, rvalue, .. } = stmt {
            collect_rvalue_live_ins(rvalue, &written, &mut seen, &mut live_ins);
            if place_is_direct_local(place) {
                written.insert(place.local);
            } else {
                collect_place_live_ins(place, &written, &mut seen, &mut live_ins);
            }
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

    loop {
        let mut changed = false;

        for bb in body.blocks.iter().rev() {
            if !terminator_supports_block_param_copies(&bb.terminator) {
                continue;
            }

            let successors = terminator_successors(&bb.terminator);
            let written =
                written_locals.get(&bb.id.0).expect("written locals exist for every block");
            let mut propagated = Vec::new();

            for successor in successors {
                let Some(successor_required) = required_locals.get(&successor).cloned() else {
                    continue;
                };

                for local in successor_required {
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

            for local in propagated {
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

    for bb in &body.blocks {
        let Some(preds) = predecessors.get(&bb.id.0) else {
            continue;
        };
        if preds.len() <= 1 {
            continue;
        }
        if preds.iter().any(|pred_id| {
            blocks_by_id
                .get(pred_id)
                .is_none_or(|pred| !terminator_supports_block_param_copies(&pred.terminator))
        }) {
            continue;
        }

        let live_ins: Vec<usize> = required_locals
            .get(&bb.id.0)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|local| assigned_locals.contains(local))
            .collect();
        if live_ins.is_empty() {
            continue;
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
/// - Function calls (direct) and drop elaboration
/// - Supported terminators (goto, return, switch, assert, call, drop, unreachable)
/// - Casts (int-int, float-int, int-float, float-float, ptr-ptr)
#[must_use = "returns the lowered LIR function"]
pub fn lower_to_lir(func: &VerifiableFunction) -> Result<LirFunction, BridgeError> {
    lower_body_to_lir(&func.name, &func.body)
}

#[must_use = "returns the lowered LIR function"]
pub fn lower_to_lir_with_options(
    func: &VerifiableFunction,
    options: &LoweringOptions,
) -> Result<LirFunction, BridgeError> {
    lower_body_to_lir_with_options(&func.name, &func.body, options)
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
    // Trust: Validate that the function body is not empty.
    if body.blocks.is_empty() {
        return Err(BridgeError::EmptyBody);
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

    // Compute the maximum block ID so the context can allocate new blocks
    // (e.g., the panic block for Assert) without collisions.
    let max_block_id = body.blocks.iter().map(|bb| bb.id.0 as u32).max().unwrap_or(0);
    let mut ctx = LoweringCtx::new(&body.locals, body.arg_count, max_block_id, options);
    let initial_local_values = ctx.local_values.clone();
    let predecessors = collect_predecessors(body);
    let return_lowering = return_lowering_for(body);
    let block_params = plan_block_params(body, &mut ctx, &predecessors, return_lowering)?;

    // Build signature from locals: args are locals[1..=arg_count], return is locals[0].
    //
    let return_ty = match return_lowering {
        ReturnLowering::Value => Some(map_lowering_type(&body.return_ty)?),
        ReturnLowering::NoValue => None,
    };
    let mut param_types = Vec::with_capacity(body.arg_count);
    for i in 1..=body.arg_count {
        let local =
            body.locals.iter().find(|l| l.index == i).ok_or(BridgeError::MissingLocal(i))?;
        param_types.push(map_lowering_type(&local.ty)?);
    }
    let returns = return_ty.into_iter().collect();
    let signature = Signature { params: param_types, returns };

    // Convert each basic block.
    // Trust: std HashMap required by LirFunction API contract (trust_cg-lower).
    // Keys are Block(u32). Consumers use block_order or sorted keys when order matters.
    #[allow(rustc::default_hash_types)]
    let mut blocks = std::collections::HashMap::with_capacity(body.blocks.len());
    let mut block_order: Vec<Block> = body.blocks.iter().map(|bb| Block(bb.id.0 as u32)).collect();
    let mut block_entry_values =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    block_entry_values.insert(body.blocks[0].id.0, initial_local_values.clone());
    for bb in &body.blocks {
        let block = Block(bb.id.0 as u32);
        let mut entry_values = block_entry_values
            .get(&bb.id.0)
            .cloned()
            .unwrap_or_else(|| initial_local_values.clone());
        if let Some(params) = block_params.get(&bb.id.0) {
            for param in params {
                entry_values.insert(param.local, param.value);
            }
        }
        let params = block_params.get(&bb.id.0).map_or(&[][..], Vec::as_slice);
        let lir_block =
            lower_block(bb, &mut ctx, return_lowering, &entry_values, params, &block_params)?;
        let exit_values = ctx.local_values.clone();
        for successor in terminator_successors(&bb.terminator) {
            if block_params.contains_key(&successor) {
                continue;
            }
            if predecessors.get(&successor).is_some_and(|preds| preds.len() == 1) {
                block_entry_values.insert(successor, exit_values.clone());
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
    for (action, panic_blk) in ctx.panic_blocks.clone() {
        block_order.push(panic_blk);
        let instructions = panic_block_instructions(&mut ctx, &action);
        blocks.insert(panic_blk, LirBlock { params: vec![], instructions, source_locs: vec![] });
    }

    // SAFETY: body.blocks is non-empty (validated above).
    let entry_block = Block(body.blocks[0].id.0 as u32);

    Ok(LirFunction {
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
        debug_meta: Default::default(),
        debug_value_bindings: vec![],
        stack_protector: Default::default(),
        // trust-cg Function carries per-function exception-handling info; the bridge does
        // not emit EH metadata yet — Default (empty) is the validated no-EH baseline.
        eh_info: Default::default(),
    })
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
) -> Result<LirBlock, BridgeError> {
    ctx.local_values = entry_values.clone();
    let mut instructions = Vec::new();

    // Lower each statement.
    for stmt in &bb.stmts {
        lower_statement(stmt, ctx, &mut instructions)?;
    }

    // Lower the terminator.
    lower_terminator(&bb.terminator, ctx, &mut instructions, return_lowering, block_params)?;

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
        // Trust: #966 — Deinit/Intrinsic don't yet produce LIR;
        // once the backend matures these may need real lowering.
        Statement::Deinit { .. } | Statement::Intrinsic { .. } => {}
        // Trust: #966 — Statement is #[non_exhaustive]; future variants are no-ops
        // until explicit lowering is added.
        _ => {}
    }
    Ok(())
}

fn lower_set_discriminant(
    place: &Place,
    variant_index: usize,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    let place_ty = ctx.place_ty(place)?;
    let (field_index, field_ty) = explicit_discriminant_field(&place_ty)?;
    let (tag_lir_ty, tag_imm) = explicit_discriminant_lir_const(&field_ty, variant_index)?;

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

    if place.projections.is_empty() && is_addressable_local_ty(&place_ty) {
        let base_addr = ctx.materialize_local_stack_addr(place.local, instructions)?;
        let aggregate_ty = map_lowering_type(&place_ty)?;
        let aggregate_value =
            materialize_aggregate_value(ctx, base_addr, &aggregate_ty, instructions);
        ctx.local_values.insert(place.local, aggregate_value);
    }

    Ok(())
}

fn explicit_discriminant_field(ty: &Ty) -> Result<(usize, Ty), BridgeError> {
    let Ty::Adt { name, fields, .. } = ty else {
        return Err(BridgeError::UnsupportedOp(format!(
            "SetDiscriminant is modeled only for tagged ADTs with an explicit discriminant/tag field, got {ty:?}"
        )));
    };

    let Some((field_index, (field_name, field_ty))) =
        fields.iter().enumerate().find(|(_, (field_name, _))| {
            matches!(field_name.as_str(), "discriminant" | "__discriminant" | "tag" | "__tag")
        })
    else {
        let field_list =
            fields.iter().map(|(field_name, _)| field_name.as_str()).collect::<Vec<_>>().join(", ");
        return Err(BridgeError::UnsupportedOp(format!(
            "ADT `{name}` has no explicit discriminant/tag field for SetDiscriminant; fields=[{field_list}]"
        )));
    };

    if !matches!(field_ty, Ty::Bool | Ty::Int { .. }) {
        return Err(BridgeError::UnsupportedOp(format!(
            "ADT `{name}` discriminant/tag field `{field_name}` has type {field_ty:?}; expected bool or integer"
        )));
    }

    Ok((field_index, field_ty.clone()))
}

fn explicit_discriminant_lir_const(
    ty: &Ty,
    variant_index: usize,
) -> Result<(LirType, i64), BridgeError> {
    match ty {
        Ty::Bool => match variant_index {
            0 => Ok((LirType::B1, 0)),
            1 => Ok((LirType::B1, 1)),
            _ => Err(BridgeError::UnsupportedOp(format!(
                "variant index {variant_index} does not fit bool discriminant/tag field"
            ))),
        },
        Ty::Int { .. } => {
            validate_explicit_discriminant_value(ty, variant_index)?;
            let lir_ty = map_type(ty)?;
            let imm = i64::try_from(variant_index).map_err(|_| {
                BridgeError::UnsupportedOp(format!(
                    "variant index {variant_index} exceeds LIR discriminant immediate range"
                ))
            })?;
            Ok((lir_ty, imm))
        }
        other => Err(BridgeError::UnsupportedOp(format!(
            "discriminant/tag field type {other:?} is not modeled as bool or integer"
        ))),
    }
}

fn validate_explicit_discriminant_value(ty: &Ty, variant_index: usize) -> Result<(), BridgeError> {
    let Ty::Int { width, signed } = ty else {
        return Ok(());
    };
    let width = *width;
    if width == 0 || width > 128 {
        return Err(BridgeError::UnsupportedOp(format!(
            "integer discriminant/tag width {width} is outside the supported 1..=128 range"
        )));
    }

    let value = variant_index as u128;
    let max = if *signed {
        if width == 128 { i128::MAX as u128 } else { (1u128 << (width - 1)) - 1 }
    } else if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };

    if value > max {
        return Err(BridgeError::UnsupportedOp(format!(
            "variant index {variant_index} does not fit {}{} discriminant/tag field",
            if *signed { "i" } else { "u" },
            width
        )));
    }

    Ok(())
}

/// Helper: assign a computed value to a destination place.
///
/// For simple locals, updates the local_values map. For projected places,
/// computes the address and emits a Store instruction.
fn assign_to_place(
    dest: &Place,
    value: Value,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    if place_is_direct_local(dest) {
        ctx.local_values.insert(dest.local, value);
    } else {
        let addr = ctx.resolve_place_addr(dest, instructions)?;
        let ty = map_lowering_type(&ctx.place_ty(dest)?)?;
        push_store(instructions, ty, value, addr);
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
            let lhs_val = ctx.resolve_operand(lhs, instructions)?;
            let rhs_val = ctx.resolve_operand(rhs, instructions)?;

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

            let lhs_is_float = match lhs {
                Operand::Copy(place) | Operand::Move(place) => {
                    ctx.local_ty(place.local)?.is_float()
                }
                Operand::Constant(ConstValue::Float(_)) => true,
                _ => false,
            };
            let rhs_is_float = match rhs {
                Operand::Copy(place) | Operand::Move(place) => {
                    ctx.local_ty(place.local)?.is_float()
                }
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
            // from the destination value's type.
            let signed = match op {
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    cmp_operand_ty(ctx, lhs, rhs)?.is_signed()
                }
                _ => ctx.is_signed(dest.local),
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
            let lhs_val = ctx.resolve_operand(lhs, instructions)?;
            let rhs_val = ctx.resolve_operand(rhs, instructions)?;
            let value_ty = checked_binary_value_ty(ctx, dest)?;
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

            // Build the (result, overflow) tuple in a stack slot.
            let dest_ty = ctx.local_ty(dest.local)?.clone();
            let lir_ty = map_type(&dest_ty)?;
            let slot = ctx.alloc_stack_slot(&lir_ty);
            let base_ptr = ctx.emit_stack_addr(slot, instructions);

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

            ctx.local_stack_slots.insert(dest.local, slot);
            let tuple_value = materialize_aggregate_value(ctx, base_ptr, &lir_ty, instructions);
            ctx.local_values.insert(dest.local, tuple_value);
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

            let src = ctx.resolve_operand(operand, instructions)?;
            let opcode = map_unop(*op)?;
            instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
            assign_to_place(dest, dest_val, ctx, instructions)?;
        }
        // Trust: #828 — Cast handles int-to-int, float-to-int, int-to-float,
        // float-to-float, and pointer-to-pointer conversions.
        Rvalue::Cast(operand, target_ty) => {
            let src = ctx.resolve_operand(operand, instructions)?;

            let src_ty = match operand {
                Operand::Copy(p) | Operand::Move(p) => ctx.local_ty(p.local).ok(),
                _ => None,
            };

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
            let local_ty = ctx.local_ty(place.local)?.clone();
            if is_fieldless_adt(&local_ty) {
                return Err(BridgeError::UnsupportedOp(format!(
                    "fieldless ADT discriminant has no trustworthy LIR layout: {local_ty:?}"
                )));
            } else {
                // Discriminant: extract the tag field from an ADT.
                // By convention the discriminant is field 0 of the struct layout,
                // stored as an integer. We emit StructGep(0) + Load(I64).
                let base_val = if let Some(&slot) = ctx.local_stack_slots.get(&place.local) {
                    ctx.emit_stack_addr(slot, instructions)
                } else {
                    // If the local doesn't have a stack slot, allocate one.
                    let slot = ctx.ensure_local_stack_slot(place.local)?;
                    ctx.emit_stack_addr(slot, instructions)
                };
                let lir_ty = map_type(&local_ty)?;
                let gep_result = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::StructGep { struct_ty: lir_ty, field_index: 0 },
                    args: vec![base_val],
                    results: vec![gep_result],
                });
                let loaded = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Load { ty: LirType::I64, align: None },
                    args: vec![gep_result],
                    results: vec![loaded],
                });
                assign_to_place(dest, loaded, ctx, instructions)?;
            }
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
            // Aggregate construction: allocate a stack slot, store each field.
            let dest_ty = ctx.local_ty(dest.local)?.clone();
            validate_aggregate_kind_for_lir(kind, &dest_ty)?;
            let lir_ty = map_lowering_type(&dest_ty)?;

            let slot = ctx.alloc_stack_slot(&lir_ty);
            let base_ptr = ctx.emit_stack_addr(slot, instructions);

            match kind {
                AggregateKind::Tuple | AggregateKind::Array => {
                    for (i, operand) in operands.iter().enumerate() {
                        let val = ctx.resolve_operand(operand, instructions)?;
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
                        push_store(instructions, store_ty, val, field_ptr);
                    }
                }
                AggregateKind::Adt { variant, active_field, .. } => {
                    debug_assert!(active_field.is_none());
                    {
                        // Trust: #828 — enum variant construction must write the
                        // discriminant tag. Convention: if field 0 of the ADT is
                        // named "tag", it is the discriminant and operands map to
                        // fields starting at index 1. For plain structs (no "tag"
                        // field) operands map 1:1 to fields.
                        let has_discriminant = matches!(
                            &dest_ty,
                            Ty::Adt { fields, .. }
                                if fields.first().map(|(n, _)| n.as_str()) == Some("tag")
                        );

                        let field_offset: u32 = if has_discriminant {
                            // Store the variant index as the discriminant at field 0.
                            let tag_ptr = ctx.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::StructGep {
                                    struct_ty: lir_ty.clone(),
                                    field_index: 0,
                                },
                                args: vec![base_ptr],
                                results: vec![tag_ptr],
                            });
                            let tag_field_ty = match &dest_ty {
                                Ty::Adt { fields, .. } => &fields[0].1,
                                other => {
                                    return Err(BridgeError::InvalidMir(format!(
                                        "ADT aggregate kind does not match destination type {other:?}"
                                    )));
                                }
                            };
                            let (tag_lir_ty, tag_imm) =
                                explicit_discriminant_lir_const(tag_field_ty, *variant)?;
                            let tag_val = ctx.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Iconst { ty: tag_lir_ty.clone(), imm: tag_imm },
                                args: vec![],
                                results: vec![tag_val],
                            });
                            push_store(instructions, tag_lir_ty, tag_val, tag_ptr);
                            1 // data fields start after the discriminant
                        } else {
                            0
                        };

                        for (i, operand) in operands.iter().enumerate() {
                            let val = ctx.resolve_operand(operand, instructions)?;
                            let field_index = i + field_offset as usize;
                            let store_ty = match &dest_ty {
                                Ty::Adt { fields, .. } => {
                                    let (_, field_ty) = fields.get(field_index).ok_or_else(|| {
                                        BridgeError::InvalidMir(format!(
                                            "ADT aggregate operand {i} maps to missing field {field_index}"
                                        ))
                                    })?;
                                    map_lowering_type(field_ty)?
                                }
                                other => {
                                    return Err(BridgeError::InvalidMir(format!(
                                        "ADT aggregate kind does not match destination type {other:?}"
                                    )));
                                }
                            };
                            let field_ptr = ctx.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::StructGep {
                                    struct_ty: lir_ty.clone(),
                                    field_index: field_index as u32,
                                },
                                args: vec![base_ptr],
                                results: vec![field_ptr],
                            });
                            push_store(instructions, store_ty, val, field_ptr);
                        }
                    }
                }
                other => unreachable!("validated aggregate kind before lowering: {other:?}"),
            }

            // Track this local's stack slot so future projections can find it.
            ctx.local_stack_slots.insert(dest.local, slot);
            let aggregate_value = materialize_aggregate_value(ctx, base_ptr, &lir_ty, instructions);
            ctx.local_values.insert(dest.local, aggregate_value);
        }
        Rvalue::Repeat(operand, count) => {
            // Array repeat: [operand; count]. Allocate stack slot and store
            // the same value `count` times.
            let dest_ty = ctx.local_ty(dest.local)?.clone();
            let lir_ty = map_type(&dest_ty)?;
            let elem_ty = match &dest_ty {
                Ty::Array { elem, .. } => map_type(elem)?,
                _ => {
                    return Err(BridgeError::UnsupportedOp("Repeat on non-array type".to_string()));
                }
            };

            let slot = ctx.alloc_stack_slot(&lir_ty);
            let base_ptr = ctx.emit_stack_addr(slot, instructions);
            let val = ctx.resolve_operand(operand, instructions)?;

            let elem_size = elem_ty.bytes();
            for i in 0..*count {
                let offset_const = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I64, imm: (i as u32 * elem_size) as i64 },
                    args: vec![],
                    results: vec![offset_const],
                });
                let elem_ptr = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![base_ptr, offset_const],
                    results: vec![elem_ptr],
                });
                push_store(instructions, elem_ty.clone(), val, elem_ptr);
            }

            ctx.local_stack_slots.insert(dest.local, slot);
            let array_value = materialize_aggregate_value(ctx, base_ptr, &lir_ty, instructions);
            ctx.local_values.insert(dest.local, array_value);
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
            let args = return_args(ctx, return_lowering)?;
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
                // Emit: cmp = icmp eq(discr, value)
                let const_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I64, imm: *value as i64 },
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
                // Multi-way: emit a Switch instruction.
                let mut cases = Vec::with_capacity(targets.len());
                for (val, blk) in targets {
                    cases.push((*val as i64, conditional_edge_dest(blk.0, ctx, block_params)?));
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

            // Resolve call arguments.
            let mut arg_vals = Vec::with_capacity(args.len());
            for arg in args {
                arg_vals.push(ctx.resolve_operand(arg, instructions)?);
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
                opcode: Opcode::Call { name: callee.clone() },
                args: arg_vals,
                results: call_result.into_iter().collect(),
            });

            // Assign the call result to the destination place.
            if let Some(call_result) = call_result {
                if place_is_direct_local(dest) {
                    ctx.local_values.insert(dest.local, call_result);
                } else {
                    // For projected destinations, compute the address and store.
                    let addr = ctx.resolve_place_addr(dest, instructions)?;
                    let ty = map_lowering_type(&dest_ty)?;
                    push_store(instructions, ty, call_result, addr);
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
            let place_ty = ctx.local_ty(place.local)?.clone();
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
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown terminator variant".to_string()));
        }
    }
    Ok(())
}

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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
    use trust_types::UnwindEdge;
    use trust_types::{BlockId, SourceSpan};

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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let options = LoweringOptions {
            panic_symbols: PanicRuntimeSymbols {
                add_overflow: Some("__trust_panic_add_overflow".to_string()),
                ..PanicRuntimeSymbols::default()
            },
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
                        matches!(&inst.opcode, Opcode::Call { name } if name == "__trust_panic_add_overflow")
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
                matches!(&inst.opcode, Opcode::Call { name } if name == "__trust_panic_add_overflow")
            })
            .expect("panic block should call configured lang item");
        assert_eq!(call.args.len(), 1, "panic lang-item call must receive caller location");
        assert!(call.results.is_empty());
        assert!(
            !panic_block
                .instructions
                .iter()
                .any(|inst| matches!(&inst.opcode, Opcode::Call { name } if name == "abort")),
            "configured panic lowering must not fall back to abort"
        );
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("array subslice value should lower");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I64, imm: 4 }))
        );
        assert!(
            bb0.instructions.iter().any(|i| matches!(
                &i.opcode,
                Opcode::Load { ty: LirType::Array(elem, 2), align: None } if **elem == LirType::I32
            )),
            "array subslice value should load a fixed-size [i32; 2]"
        );
        assert!(
            !bb0.instructions.iter().any(|i| matches!(
                &i.opcode,
                Opcode::Load { ty: LirType::Struct(fields), align: None }
                    if fields.as_slice() == [LirType::I64, LirType::I64]
            )),
            "array subslice value must not materialize a slice fat pointer"
        );
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
            bb0.instructions.iter().any(|i| matches!(
                &i.opcode,
                Opcode::Load { ty: LirType::Struct(fields), align: None }
                    if fields.as_slice() == [LirType::I64, LirType::I64]
            )),
            "slice subslice value should materialize a fat pointer"
        );
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
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
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
        let union_like_ty = Ty::Adt { adt_kind: None, layout: None,
            variants: Vec::new(),
            name: "UnionLike".into(),
            fields: vec![("a".into(), Ty::i32()), ("b".into(), Ty::i64())],
            disc_index_safe: false,
         faithful_enum_repr: None, enum_layout: None, };
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
            pointee: Box::new(Ty::Dynamic { trait_name: "Debug".into() }),
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
                        pointee_ty: Ty::Dynamic { trait_name: "Debug".into() },
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
        let fieldless = Ty::Adt { adt_kind: None, layout: None,
            variants: Vec::new(),
            name: "OptionI32".into(),
            fields: vec![],
            disc_index_safe: false,
         faithful_enum_repr: None, enum_layout: None, };
        let func = unit_function(
            "fieldless_adt",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: fieldless, name: None },
            ],
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Adt { name: "OptionI32".into(), variant: 0, active_field: None },
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
