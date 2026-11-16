//! Claim-free lowering of an exact, bounded generated-MIR snapshot.
//!
//! This is not THIR and does not mint a differential or refinement verdict. All
//! operations, including unreachable blocks, are inspected before a function is
//! returned. The only value operations are scalar copies/moves and constants;
//! the coroutine input is an actual tuple of scalar capture values, not havoc.

use std::collections::BTreeSet;

use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Pred, PredId,
    Producer, StructDef, StructId, StructRepr, Ty, TyId, ValueId,
};

pub(super) const PRODUCER: &str = "rust-generated-coroutine-mir.scalar-copy.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Refusal {
    pub site: String,
    pub reason: &'static str,
    pub detail: String,
}

impl Refusal {
    pub fn new(site: impl Into<String>, reason: &'static str, detail: impl Into<String>) -> Self {
        Self { site: site.into(), reason, detail: detail.into() }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct ScalarBody {
    pub name: String,
    /// Entry 0 is the by-move capture frame. Any later entries are the actual
    /// field structure/layout of the otherwise unused resume-context argument.
    pub structs: Vec<StructDef>,
    /// Empty, or the exact one-entry tables for the unused non-null resume
    /// pointer. These are type restrictions, not proof certificates.
    pub types: Vec<Ty>,
    pub predicates: Vec<Pred>,
    pub locals: Vec<Ty>,
    pub blocks: Vec<ScalarBlock>,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) struct ScalarBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Statement {
    Assign {
        destination: usize,
        operand: Operand,
    },
    StorageLive(usize),
    StorageDead(usize),
    /// Only compiler bookkeeping with no runtime operation reaches this arm.
    Nop,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Operand {
    Local { local: usize, moved: bool },
    Capture { field: usize, ty: Ty, moved: bool },
    Constant { ty: Ty, value: Constant },
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Terminator {
    Goto(usize),
    Return,
}

pub(super) fn scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Unit
            | Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::Isize
            | Ty::Usize
    )
}

/// The initial target-independent IR has a 64-bit thin pointer carrier. Do
/// not quietly interpret a fat, differently aligned or differently sized
/// pointer with that default. rustc supplies both actual layouts and ranges.
pub(super) fn exact_resume_pointer_layout(
    target_bytes: u64,
    base_layout: (u64, u64),
    actual_layout: (u64, u64),
    base_range: (u128, u128),
    actual_range: (u128, u128),
    nonnull: bool,
) -> bool {
    target_bytes == 8
        && base_layout == (8, 8)
        && actual_layout == base_layout
        && base_range == (0, u64::MAX as u128)
        && actual_range == (u128::from(nonnull), u64::MAX as u128)
}

fn valid_constant(ty: &Ty, value: &Constant) -> bool {
    match (ty, value) {
        (Ty::Unit, Constant::PhantomData) | (Ty::Bool, Constant::Bool(_)) => true,
        (Ty::I8, Constant::Int(v)) => i8::try_from(*v).is_ok(),
        (Ty::I16, Constant::Int(v)) => i16::try_from(*v).is_ok(),
        (Ty::I32, Constant::Int(v)) => i32::try_from(*v).is_ok(),
        (Ty::I64, Constant::Int(v)) => i64::try_from(*v).is_ok(),
        (Ty::U8, Constant::Int(v)) => u8::try_from(*v).is_ok(),
        (Ty::U16, Constant::Int(v)) => u16::try_from(*v).is_ok(),
        (Ty::U32, Constant::Int(v)) => u32::try_from(*v).is_ok(),
        (Ty::U64, Constant::Int(v)) => u64::try_from(*v).is_ok(),
        // Pointer-sized constants require the actual compiler target width;
        // the initial snapshot adapter deliberately refuses them.
        _ => false,
    }
}

/// Deterministic scalar SSA translation. A refusal returns no partial module.
pub(super) fn lower(body: &ScalarBody) -> Result<Module, Refusal> {
    let refuse = |reason, detail| Refusal::new("body", reason, detail);
    if body.locals.len() < 3
        || body.locals.len() > 4096
        || body.structs.len() > 65
        || body.types.len() > 1
        || body.predicates.len() > 1
        || body.blocks.is_empty()
        || body.blocks.len() > 128
        || body
            .blocks
            .iter()
            .try_fold(0usize, |sum, block| sum.checked_add(block.statements.len()))
            .is_none_or(|count| count > 4096)
    {
        return Err(refuse(
            "GeneratedCoroutine(header)",
            "requires two arguments and a bounded body",
        ));
    }
    if body.locals[1] != Ty::Struct(StructId::new(0)) || !scalar(&body.locals[0]) {
        return Err(refuse(
            "GeneratedCoroutine(signature)",
            "requires an exact capture frame and scalar return",
        ));
    }
    let Some(frame) = body.structs.first() else {
        return Err(refuse("GeneratedCoroutine(frame)", "missing capture frame"));
    };
    if frame.id != StructId::new(0)
        || frame.fields.len() > 64
        || frame.fields.iter().any(|field| !scalar(&field.ty))
    {
        return Err(refuse(
            "GeneratedCoroutine(frame)",
            "capture fields must all be actual scalar values",
        ));
    }
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let has_nonnull = body.types == [Ty::Ptr] && body.predicates == [Pred::NonNull];
    if !has_nonnull && (!body.types.is_empty() || !body.predicates.is_empty()) {
        return Err(refuse(
            "GeneratedCoroutine(resume refinement)",
            "requires the exact canonical Ptr/NonNull tables, or no refinement tables",
        ));
    }
    let mut refined_fields = 0;
    for (index, definition) in body.structs.iter().enumerate() {
        if definition.id.index() as usize != index {
            return Err(refuse("GeneratedCoroutine(type table)", "non-dense struct identity"));
        }
        if index > 0 {
            let [field] = definition.fields.as_slice() else {
                return Err(refuse(
                    "GeneratedCoroutine(resume type)",
                    "resume wrapper must have exactly one field",
                ));
            };
            // The sole leaf is the actual thin pointer, followed by the
            // exact wrapper chain. No unused table rows or sibling carriers.
            let expected = if index == 1 {
                if has_nonnull { refined.clone() } else { Ty::Ptr }
            } else {
                Ty::Struct(StructId::new(u32::try_from(index - 1).map_err(|_| {
                    refuse("GeneratedCoroutine(type table)", "wrapper index overflows u32")
                })?))
            };
            if field.ty != expected
                || field.offset != Some(0)
                || definition.size != Some(8)
                || definition.align != Some(8)
                || !matches!(definition.repr, StructRepr::Rust | StructRepr::Transparent)
            {
                return Err(refuse(
                    "GeneratedCoroutine(resume type)",
                    "resume wrapper type or exact 64-bit thin-pointer layout differs",
                ));
            }
            refined_fields += usize::from(field.ty == refined);
        }
    }
    if (body.structs.len() == 1 && body.locals[2] != Ty::Unit)
        || (body.structs.len() > 1
            && !matches!(body.locals[2], Ty::Struct(id) if id.index() as usize == body.structs.len() - 1))
        || refined_fields != usize::from(has_nonnull)
    {
        return Err(refuse(
            "GeneratedCoroutine(resume type)",
            "resume context must retain its actual field structure",
        ));
    }
    if body.locals.iter().skip(3).any(|ty| !scalar(ty)) {
        return Err(refuse(
            "GeneratedCoroutine(local type)",
            "only scalar temporaries are supported",
        ));
    }

    // No block is dropped as dead code. The bounded slice is one acyclic chain
    // ending in Return, and the chain must account for every supplied block.
    let mut order = Vec::new();
    let mut visited = BTreeSet::new();
    let mut current = 0;
    loop {
        if current >= body.blocks.len() || !visited.insert(current) {
            return Err(refuse(
                "GeneratedCoroutine(control flow)",
                "invalid target or cyclic control flow",
            ));
        }
        order.push(current);
        match body.blocks[current].terminator {
            Terminator::Goto(next) => current = next,
            Terminator::Return => break,
        }
    }
    if visited.len() != body.blocks.len() {
        return Err(refuse(
            "GeneratedCoroutine(control flow)",
            "unaccounted block; unreachable effects are not dropped",
        ));
    }

    let mut module = Module::new(body.name.clone());
    module.structs = body.structs.clone();
    module.types = body.types.clone();
    if has_nonnull && module.intern_pred(Pred::NonNull) != Ok(Some(PredId::new(0))) {
        return Err(refuse(
            "GeneratedCoroutine(resume refinement)",
            "non-canonical predicate identity",
        ));
    }
    // Trust (trust-ir D1b): a refused table door refuses the body, never panics.
    let signature = module
        .add_func_type(FuncTy {
            params: vec![body.locals[1].clone(), body.locals[2].clone()],
            returns: vec![body.locals[0].clone()],
            is_vararg: false,
            abi: None,
        })
        .map_err(|exhausted| {
            Refusal::new("body", "GeneratedCoroutine(module table)", exhausted.to_string())
        })?;
    let mut block = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), body.locals[1].clone())
        .with_param(ValueId::new(1), body.locals[2].clone());
    let mut locals: Vec<Option<ValueId>> = vec![None; body.locals.len()];
    // Locals carrying explicit storage markers start dead. Unmarked locals
    // have whole-body storage, matching built MIR's implicit-live convention.
    let mut storage_live = vec![true; body.locals.len()];
    for statement in body.blocks.iter().flat_map(|block| &block.statements) {
        if let Statement::StorageLive(local) | Statement::StorageDead(local) = statement {
            if *local < 3 || *local >= locals.len() {
                return Err(refuse(
                    "GeneratedCoroutine(storage)",
                    "storage marker names an argument/return slot or unknown local",
                ));
            }
            storage_live[*local] = false;
        }
    }
    let mut captures_live = vec![true; frame.fields.len()];
    let mut next_value = 2u32;
    for block_index in order {
        for (statement_index, statement) in body.blocks[block_index].statements.iter().enumerate() {
            let site = format!("bb{block_index}[{statement_index}]");
            let error = |reason, detail| Refusal::new(site.clone(), reason, detail);
            match statement {
                Statement::Nop => {}
                Statement::StorageLive(local) | Statement::StorageDead(local) => {
                    if *local < 3 || *local >= locals.len() {
                        return Err(error(
                            "GeneratedCoroutine(storage)",
                            "storage marker changes an argument/return slot or unknown local",
                        ));
                    }
                    let becoming_live = matches!(statement, Statement::StorageLive(_));
                    if storage_live[*local] == becoming_live {
                        return Err(error(
                            "GeneratedCoroutine(storage)",
                            "invalid storage lifetime transition",
                        ));
                    }
                    storage_live[*local] = becoming_live;
                    locals[*local] = None;
                }
                Statement::Assign { destination, operand } => {
                    if *destination >= locals.len() || matches!(destination, 1 | 2) {
                        return Err(error(
                            "GeneratedCoroutine(assignment)",
                            "assignment changes an argument or unknown local",
                        ));
                    }
                    if !storage_live[*destination] {
                        return Err(error(
                            "GeneratedCoroutine(storage)",
                            "assignment to dead storage",
                        ));
                    }
                    let (value, ty) = match operand {
                        Operand::Local { local, moved } => {
                            if *local >= locals.len() || matches!(local, 1 | 2) {
                                return Err(error(
                                    "GeneratedCoroutine(operand)",
                                    "whole-frame/resume reads and unknown locals are unsupported",
                                ));
                            }
                            if !storage_live[*local] {
                                return Err(error(
                                    "GeneratedCoroutine(storage)",
                                    "read from dead storage",
                                ));
                            }
                            let value = locals[*local].ok_or_else(|| {
                                error(
                                    "GeneratedCoroutine(uninitialized read)",
                                    "local has no live initialized value",
                                )
                            })?;
                            if *moved {
                                locals[*local] = None;
                            }
                            (value, body.locals[*local].clone())
                        }
                        Operand::Capture { field, ty, moved } => {
                            let Some(declaration) = frame.fields.get(*field) else {
                                return Err(error(
                                    "GeneratedCoroutine(capture)",
                                    "capture index out of bounds",
                                ));
                            };
                            if declaration.ty != *ty || !captures_live[*field] {
                                return Err(error(
                                    "GeneratedCoroutine(capture)",
                                    "wrong capture type or use after move",
                                ));
                            }
                            if *moved {
                                captures_live[*field] = false;
                            }
                            let value = ValueId::new(next_value);
                            next_value += 1;
                            block.body.push(
                                InstrNode::new(Inst::ExtractField {
                                    ty: ty.clone(),
                                    aggregate: ValueId::new(0),
                                    field: u32::try_from(*field).map_err(|_| {
                                        error(
                                            "GeneratedCoroutine(capture)",
                                            "capture index overflows u32",
                                        )
                                    })?,
                                })
                                .with_result(value),
                            );
                            (value, ty.clone())
                        }
                        Operand::Constant { ty, value } => {
                            if !valid_constant(ty, value) {
                                return Err(error(
                                    "GeneratedCoroutine(constant)",
                                    "constant is not exact in its declared scalar type",
                                ));
                            }
                            let id = ValueId::new(next_value);
                            next_value += 1;
                            block.body.push(
                                InstrNode::new(Inst::Const {
                                    ty: ty.clone(),
                                    value: value.clone(),
                                })
                                .with_result(id),
                            );
                            (id, ty.clone())
                        }
                    };
                    if body.locals[*destination] != ty {
                        return Err(error(
                            "GeneratedCoroutine(assignment type)",
                            "source and destination types differ",
                        ));
                    }
                    locals[*destination] = Some(value);
                }
            }
        }
    }
    let returned = locals[0]
        .ok_or_else(|| refuse("GeneratedCoroutine(return)", "return place was not initialized"))?;
    block.body.push(InstrNode::new(Inst::Return { values: vec![returned] }));
    let mut function = Function::new(FuncId::new(0), body.name.clone(), signature, BlockId::new(0))
        .with_producer(Producer::Other(PRODUCER.into()));
    function.calling_conv = trust_ir::CallingConv::Rust;
    function.blocks.push(block);
    module.try_add_function(function).map_err(|refusal| {
        Refusal::new("body", "GeneratedCoroutine(module table)", refusal.to_string())
    })?;
    let errors = trust_ir_build::validate_module(&module);
    if !errors.is_empty() {
        return Err(refuse("GeneratedCoroutine(module validation)", &format!("{errors:?}")));
    }
    Ok(module)
}

#[cfg(test)]
#[path = "model_tests.rs"]
mod tests;
