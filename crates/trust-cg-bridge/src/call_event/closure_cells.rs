//! Typed, nonescaping nominal closure cells in the producer-side evaluator.
//!
//! Keep the actual Alloca/Store/Load and the complete ClosureValue. The source
//! IR's storage binding authenticates the unique target, capture types and
//! observed layout; no code-identity word or scalar width is invented. Each
//! admitted address is used only by this block's plain accesses of exactly its
//! type and natural alignment, so no other operation can observe or alias it.
//!
//! This is source evaluation only. In particular, passing even an empty cell's
//! pointer to a callee is refused. Source-allocation/actual-slot/SP transport,
//! borrowed-callee memory and frame proofs remain separate obligations.

use super::*;

struct Cell {
    nominal: trust_ir::ClosureTyId,
    target: FuncId,
    captures: Vec<IrTy>,
    alignment: u64,
    value: Option<(ValueId, ClosureValue)>,
}

/// Fresh per block evaluation, just like LocalSlots. No accepted source value
/// here is a certificate, allocation-placement witness or function grade.
#[derive(Default)]
pub(super) struct ClosureCells {
    cells: HashMap<ValueId, Cell>,
    declared: Option<HashMap<ValueId, IrTy>>,
}

fn alignment_matches(alignment: Option<u64>, natural: u64) -> bool {
    natural.is_power_of_two() && alignment.is_none_or(|alignment| alignment == natural)
}

fn admit(
    module: &Module,
    function: &trust_ir::Function,
    home: u32,
    slot: ValueId,
    nominal: trust_ir::ClosureTyId,
    count: Option<ValueId>,
    alignment: Option<u64>,
) -> Result<Cell, String> {
    let refuse = |reason: &str| {
        format!("`Alloca` %{} is not a nominal local cell: {reason} (fail-closed)", slot.index())
    };
    if count.is_some() {
        return Err(refuse("it has an element count"));
    }
    let binding = module.closure_storage_binding(nominal).map_err(refuse)?;
    let natural = binding.layout.align;
    if !alignment_matches(alignment, natural) {
        return Err(refuse("allocation alignment differs from its declared natural alignment"));
    }
    let ty = IrTy::Closure(nominal);
    let mut block_ids = BTreeSet::new();
    let mut values = BTreeSet::new();
    // Inspect the actual complete function, including unreachable blocks. A
    // block-map overwrite or repeated SSA ID must not hide an address use.
    for block in &function.blocks {
        if !block_ids.insert(block.id) {
            return Err(refuse("the source has duplicate block identities"));
        }
        for value in block
            .params
            .iter()
            .map(|(id, _)| id)
            .chain(block.body.iter().flat_map(|node| &node.results))
        {
            if !values.insert(*value) {
                return Err(refuse("the source has duplicate SSA identities"));
            }
        }
        for node in &block.body {
            if !node.inst.uses_value(slot) {
                continue;
            }
            if block.id.index() != home {
                return Err(refuse("its address is used in another block"));
            }
            let plain_access = match &node.inst {
                Inst::Load { ty: actual, ptr, volatile: false, align } => {
                    *ptr == slot && *actual == ty && alignment_matches(*align, natural)
                }
                Inst::Store { ty: actual, ptr, value, volatile: false, align } => {
                    *ptr == slot
                        && *value != slot
                        && *actual == ty
                        && alignment_matches(*align, natural)
                }
                _ => false,
            };
            if !plain_access {
                return Err(refuse(
                    "its address escapes or has a non-plain/mistyped/misaligned access",
                ));
            }
        }
    }
    Ok(Cell {
        nominal,
        target: binding.target,
        captures: binding.captures.to_vec(),
        alignment: natural,
        value: None,
    })
}

impl ClosureCells {
    pub(super) fn step(
        &mut self,
        module: &Module,
        function: FuncId,
        home: u32,
        env: &mut SpecEnv,
        node: &trust_ir::node::InstrNode,
    ) -> Option<Result<(), String>> {
        match &node.inst {
            Inst::Alloca { ty: IrTy::Closure(nominal), count, align } => {
                Some(self.alloca(module, function, home, node, *nominal, *count, *align))
            }
            Inst::Store { ty, ptr, value, volatile, align } if self.cells.contains_key(ptr) => {
                Some(self.store(module, function, env, node, ty, *ptr, *value, *volatile, *align))
            }
            Inst::Load { ty, ptr, volatile, align } if self.cells.contains_key(ptr) => {
                Some(self.load(env, node, ty, *ptr, *volatile, *align))
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn alloca(
        &mut self,
        module: &Module,
        function: FuncId,
        home: u32,
        node: &trust_ir::node::InstrNode,
        nominal: trust_ir::ClosureTyId,
        count: Option<ValueId>,
        alignment: Option<u64>,
    ) -> Result<(), String> {
        let [slot] = node.results.as_slice() else {
            return Err("nominal local Alloca must bind one pointer".into());
        };
        let mut functions = module.functions.iter().filter(|row| row.id == function);
        let function = functions.next().ok_or("nominal cell source function is missing")?;
        if functions.next().is_some() {
            return Err("nominal cell source function is ambiguous".into());
        }
        let cell = admit(module, function, home, *slot, nominal, count, alignment)?;
        self.cells.insert(*slot, cell);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn store(
        &mut self,
        module: &Module,
        function: FuncId,
        env: &SpecEnv,
        node: &trust_ir::node::InstrNode,
        ty: &IrTy,
        ptr: ValueId,
        value: ValueId,
        volatile: bool,
        alignment: Option<u64>,
    ) -> Result<(), String> {
        if !node.results.is_empty() {
            return Err("nominal local Store cannot bind a result".into());
        }
        if self.declared.is_none() {
            let function =
                module.function_by_id(function).ok_or("nominal cell source is missing")?;
            self.declared =
                Some(function.typed_values(module).into_iter().map(|v| (v.value, v.ty)).collect());
        }
        if self.declared.as_ref().and_then(|types| types.get(&value)) != Some(ty) {
            return Err("nominal local Store value has another declared SSA type".into());
        }
        let cell = self.cells.get_mut(&ptr).ok_or("nominal local Store cell is missing")?;
        if *ty != IrTy::Closure(cell.nominal)
            || volatile
            || !alignment_matches(alignment, cell.alignment)
        {
            return Err("nominal local Store changes type, volatility or alignment".into());
        }
        let stored =
            env.closures.get(&value).ok_or("nominal local Store has no logical closure value")?;
        stored.check_local_storage(cell.nominal, cell.target, &cell.captures)?;
        cell.value = Some((value, stored.clone()));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn load(
        &self,
        env: &mut SpecEnv,
        node: &trust_ir::node::InstrNode,
        ty: &IrTy,
        ptr: ValueId,
        volatile: bool,
        alignment: Option<u64>,
    ) -> Result<(), String> {
        let [result] = node.results.as_slice() else {
            return Err("nominal local Load must bind one closure".into());
        };
        let cell = self.cells.get(&ptr).ok_or("nominal local Load cell is missing")?;
        if *ty != IrTy::Closure(cell.nominal)
            || volatile
            || !alignment_matches(alignment, cell.alignment)
        {
            return Err("nominal local Load changes type, volatility or alignment".into());
        }
        let (source, value) = cell.value.as_ref().ok_or("nominal local Load precedes any Store")?;
        env.closures.insert(*result, value.clone());
        // Retain only existing pointer-projection origins. A label creates no
        // new source allocation, validity, noalias or machine-memory premise.
        env.memory.copy_closure(*source, *result);
        Ok(())
    }
}

#[cfg(test)]
mod tests;
