//! Bounded observation of the original typed MIR Bool-constant assignment.
//! This borrows its original carrier; it is not a proof, quotation theorem,
//! source-grade token, callee model or permission to erase other statements.
use trust_types::fx::FxHashSet;
use trust_types::{ConstValue, Operand, Rvalue, Statement, Ty, VerifiableFunction};

/// Exact original assignment selected by physical block/statement ordinals.
pub struct MirBoolAssignment<'a> {
    function: &'a VerifiableFunction,
    block_ordinal: usize,
    block_id: trust_types::BlockId,
    statement_ordinal: usize,
    destination: usize,
    value: bool,
}
impl<'a> MirBoolAssignment<'a> {
    pub fn function(&self) -> &'a VerifiableFunction {
        self.function
    }
    pub fn block_ordinal(&self) -> usize {
        self.block_ordinal
    }
    pub fn block_id(&self) -> trust_types::BlockId {
        self.block_id
    }
    pub fn statement_ordinal(&self) -> usize {
        self.statement_ordinal
    }
    pub fn destination(&self) -> usize {
        self.destination
    }
    pub fn value(&self) -> bool {
        self.value
    }
}

pub(crate) fn bounded_unique_original(function: &VerifiableFunction) -> Option<()> {
    let body = &function.body;
    if body.locals.len() > 4096 || body.blocks.len() > 1024 {
        return None;
    }
    let mut count = 0usize;
    for block in &body.blocks {
        count = count.checked_add(block.stmts.len())?;
        if count > 8192 {
            return None;
        }
    }
    let mut locals = FxHashSet::with_capacity_and_hasher(body.locals.len(), Default::default());
    if body.locals.iter().any(|local| !locals.insert(local.index)) {
        return None;
    }
    let mut blocks = FxHashSet::with_capacity_and_hasher(body.blocks.len(), Default::default());
    if body.blocks.iter().any(|block| !blocks.insert(block.id.0)) {
        return None;
    }
    Some(())
}

/// Check exact original identities and typing before observing this fragment.
/// Bounds precede identity-set allocation. Unhandled operations are refused;
/// success does not claim that any other part of the function was checked.
pub fn observe_mir_bool_assignment(
    function: &VerifiableFunction,
    block_ordinal: usize,
    statement_ordinal: usize,
) -> Option<MirBoolAssignment<'_>> {
    bounded_unique_original(function)?;
    let body = &function.body;
    let block = body.blocks.get(block_ordinal)?;
    let Statement::Assign {
        place,
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(value))),
        ..
    } = block.stmts.get(statement_ordinal)?
    else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let local = body.locals.iter().find(|local| local.index == place.local)?;
    if local.ty != Ty::Bool {
        return None;
    }
    Some(MirBoolAssignment {
        function,
        block_ordinal,
        block_id: block.id,
        statement_ordinal,
        destination: place.local,
        value: *value,
    })
}
