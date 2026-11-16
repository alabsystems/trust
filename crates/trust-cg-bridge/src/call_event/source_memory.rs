//! Source-side byte memory for PTR.3b. This is evaluated in production, but
//! cannot authorize a memory-bearing certificate until the remaining M1–M8
//! obligations are connected. In particular, an Arg root grants no validity,
//! alignment, separation or noalias premise.

use trust_ir::analysis::{PointerRoot, PointerRoots};

use super::*;
use crate::cer_memory::{self, AccessKind, PathAccess};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Projection {
    Closure { nominal: trust_ir::ClosureTyId, field: u32 },
    Tuple { field: u32 },
}

/// Preserve capture identity separately from pointer_roots' aggregate Arg(i).
/// Addresses, rather than this label, decide aliasing; distinct labels never
/// become a disjointness assumption.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Origin {
    pub argument: u32,
    pub projection: Option<Projection>,
    pub byte_offset: u64,
}

#[derive(Clone)]
pub(super) struct State {
    pub bytes: Formula,
    pointers: HashMap<ValueId, Origin>,
    projections: HashMap<(ValueId, u32), Origin>,
}

impl State {
    pub fn entry(module: &Module, entry: &trust_ir::Block, bytes: Formula) -> Result<Self, String> {
        let mut state = Self { bytes, pointers: HashMap::new(), projections: HashMap::new() };
        for (index, (id, ty)) in entry.params.iter().enumerate() {
            let argument = u32::try_from(index).map_err(|_| "entry argument index overflows")?;
            if *ty == IrTy::Ptr {
                state.pointers.insert(*id, Origin { argument, projection: None, byte_offset: 0 });
            }
            let fields = match ty {
                IrTy::Closure(nominal) => {
                    &module
                        .closure_type(*nominal)
                        .ok_or("memory source nominal environment is missing")?
                        .captures
                }
                IrTy::Tuple(fields) => fields,
                _ => continue,
            };
            for (field, ty) in fields.iter().enumerate() {
                if *ty != IrTy::Ptr {
                    continue;
                }
                let field = u32::try_from(field).map_err(|_| "capture index overflows")?;
                let projection = match ty_of_parameter(entry, *id)? {
                    IrTy::Closure(nominal) => Projection::Closure { nominal: *nominal, field },
                    _ => Projection::Tuple { field },
                };
                state.projections.insert(
                    (*id, field),
                    Origin { argument, projection: Some(projection), byte_offset: 0 },
                );
            }
        }
        Ok(state)
    }

    pub fn copy_pointer(&mut self, from: ValueId, to: ValueId) {
        if let Some(origin) = self.pointers.get(&from).cloned() {
            self.pointers.insert(to, origin);
        } else {
            self.pointers.remove(&to);
        }
    }

    pub fn copy_closure(&mut self, from: ValueId, to: ValueId) {
        let fields: Vec<_> = self
            .projections
            .iter()
            .filter(|((value, _), _)| *value == from)
            .map(|((_, field), origin)| (*field, origin.clone()))
            .collect();
        self.projections.retain(|(value, _), _| *value != to);
        for (field, origin) in fields {
            self.projections.insert((to, field), origin);
        }
    }

    pub fn project(&mut self, aggregate: ValueId, field: u32, result: ValueId) {
        if let Some(origin) = self.projections.get(&(aggregate, field)).cloned() {
            self.pointers.insert(result, origin);
        } else {
            self.pointers.remove(&result);
        }
    }

    pub fn edge(&self, params: &[(ValueId, IrTy)], args: &[ValueId]) -> Self {
        let mut next = self.clone();
        for ((parameter, ty), argument) in params.iter().zip(args) {
            // Read the original state, so simultaneous SSA binding never
            // overwrites a later argument's provenance.
            if let Some(origin) = self.pointers.get(argument).filter(|_| *ty == IrTy::Ptr) {
                next.pointers.insert(*parameter, origin.clone());
            } else {
                next.pointers.remove(parameter);
            }
        }
        next
    }

    pub fn origin(&self, roots: &PointerRoots, pointer: ValueId) -> Result<Origin, String> {
        let origin = self.pointers.get(&pointer).ok_or(
            "memory pointer is not an entry argument/capture through approved copies/GEPs",
        )?;
        if roots.root(pointer) != &PointerRoot::Arg(origin.argument) {
            return Err("memory pointer does not have its independently computed Arg root".into());
        }
        Ok(origin.clone())
    }

    pub fn gep(&mut self, base: ValueId, result: ValueId, offset: u64) -> Result<(), String> {
        let mut origin =
            self.pointers.get(&base).cloned().ok_or("GEP base has no admitted origin")?;
        origin.byte_offset =
            origin.byte_offset.checked_add(offset).ok_or("constant byte GEP offset overflows")?;
        self.pointers.insert(result, origin);
        Ok(())
    }
}

fn ty_of_parameter(entry: &trust_ir::Block, value: ValueId) -> Result<&IrTy, String> {
    entry
        .params
        .iter()
        .find(|(id, _)| *id == value)
        .map(|(_, ty)| ty)
        .ok_or_else(|| "memory entry parameter disappeared".into())
}

impl SpecCx<'_> {
    pub(super) fn declared_type(&self, value: ValueId, expected: &IrTy) -> Result<(), String> {
        let function = self.module.function_by_id(self.func).ok_or("source function is missing")?;
        let actual = function
            .typed_value(self.module, value)
            .ok_or("memory operand has no declared SSA type")?;
        if &actual.ty != expected {
            return Err(format!("memory operand has type {:?}, expected {expected:?}", actual.ty));
        }
        Ok(())
    }

    pub(super) fn memory_pointer(
        &self,
        env: &SpecEnv,
        pointer: ValueId,
        volatile: bool,
        alignment: Option<u64>,
    ) -> Result<(), String> {
        if volatile {
            return Err("volatile memory remains outside PTR.3b".into());
        }
        if alignment.is_some_and(|a| !a.is_power_of_two()) {
            return Err("memory alignment is not a positive power of two".into());
        }
        let target = self.module.target_info.as_ref().ok_or("source memory target is missing")?;
        if target.pointer_size != 8 || target.endianness != trust_ir::Endianness::Little {
            return Err("source memory requires a 64-bit little-endian target".into());
        }
        self.declared_type(pointer, &IrTy::Ptr)?;
        if lookup(&env.scalars, pointer)?.width != 64 {
            return Err("memory address is not a 64-bit pointer".into());
        }
        env.memory.origin(&self.roots, pointer)?;
        Ok(())
    }
}

/// Byte-valued integers and thin pointers only. Bool/Char validity and float,
/// wide, aggregate and volatile carriers are not silently flattened.
pub(super) fn width(ty: &IrTy) -> Result<u32, String> {
    match ty {
        IrTy::I8 | IrTy::U8 => Ok(1),
        IrTy::I16 | IrTy::U16 => Ok(2),
        IrTy::I32 | IrTy::U32 => Ok(4),
        IrTy::I64 | IrTy::U64 | IrTy::Isize | IrTy::Usize | IrTy::Ptr => Ok(8),
        _ => Err(format!("memory scalar {ty:?} is outside PTR.3b's byte fragment")),
    }
}

#[derive(Clone)]
pub(super) struct Access {
    pub site: SiteKey,
    pub origin: Origin,
    pub term: PathAccess,
}

#[derive(Clone)]
pub(super) struct Exit {
    pub path: Formula,
    pub bytes: Formula,
}

#[derive(Clone)]
pub(super) struct Call {
    pub path: Formula,
    pub before: Formula,
    pub after_variable: String,
}

pub(super) struct ResultMemory {
    pub entry: Formula,
    pub accesses: Vec<Access>,
    pub exits: Vec<Exit>,
    pub calls: BTreeMap<SiteKey, Vec<Call>>,
    pub address_computation: bool,
}

impl ResultMemory {
    pub fn new(scope: &str) -> Self {
        Self {
            entry: cer_memory::shared_entry_memory(scope),
            accesses: Vec::new(),
            exits: Vec::new(),
            calls: BTreeMap::new(),
            address_computation: false,
        }
    }

    pub fn record(
        &mut self,
        site: SiteKey,
        origin: Origin,
        kind: AccessKind,
        path: &Formula,
        address: &Formula,
        bytes: u32,
    ) -> Result<(), String> {
        self.accesses.push(Access {
            site,
            origin,
            term: PathAccess::new(kind, path.clone(), address.clone(), bytes)?,
        });
        Ok(())
    }

    pub fn call(&mut self, site: SiteKey, path: &Formula, state: &mut State) {
        let name = format!("CER_SMEM#{}", site_name(site));
        self.calls.entry(site).or_default().push(Call {
            path: path.clone(),
            before: state.bytes.clone(),
            after_variable: name.clone(),
        });
        // A pending abstract transition, not a proved call premise. The gate
        // below refuses memory use until pre-call equality and the callee's
        // memory obligations are checked. No stale pre-call byte survives.
        state.bytes =
            Formula::Var(name, Sort::Array(b_sort(Sort::BitVec(64)), b_sort(Sort::BitVec(8))));
    }

    /// The actual O2 bijection selects the shared event identity. This binds
    /// source symbols to the *same constructor* the machine rely uses. It does
    /// not discharge any pre-call equality or authorize applying that rely.
    pub fn paired_variables(
        &self,
        pairing: &BTreeMap<SiteKey, u64>,
    ) -> Result<HashMap<String, Formula>, String> {
        let mut map = HashMap::new();
        for (site, calls) in &self.calls {
            let pc = pairing
                .get(site)
                .ok_or_else(|| format!("memory call {} is unpaired", site_name(*site)))?;
            for call in calls {
                map.insert(call.after_variable.clone(), paired_post_memory(*pc));
            }
        }
        Ok(map)
    }

    pub fn missing_integration(&self) -> Option<String> {
        if self.accesses.is_empty() && !self.address_computation {
            return None;
        }
        Some(format!(
            "PTR.3b source memory modeled ({} access path(s), {} exit path(s), {} call site(s)); \
            missing justified frame separation (M1'), complete machine-byte coverage (M3), \
            exit-memory/call-premise discharge (M4/M5), legal disjoint refutations (M6) \
            and independent memory kernel support (M8); Unknown",
            self.accesses.len(),
            self.exits.len(),
            self.calls.len()
        ))
    }
}

fn b_sort(sort: Sort) -> Box<Sort> {
    Box::new(sort)
}

/// Exact legacy machine event memory. Shared by the source pairing and the
/// unchanged rely; moving its constructor changes no formula or assumption.
pub(super) fn paired_post_memory(pc: u64) -> Formula {
    Formula::Var(
        format!("CER_MEM@{pc:x}"),
        Sort::Array(b_sort(Sort::BitVec(64)), b_sort(Sort::BitVec(8))),
    )
}

#[cfg(test)]
#[path = "source_memory/tests.rs"]
mod tests;
